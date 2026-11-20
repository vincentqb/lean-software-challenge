module

public section

namespace SoftwareChallenge

inductive Doc.Value where
  | string (value : String)
  | array (values : List String)

structure Doc where
  fields : List (String × Doc.Value)

private inductive Doc.Token where
  | openObject | closeObject | openArray | closeArray | colon | comma
  | string (value : String)

private inductive Doc.Space where
  | tight | blank | newline | fieldIndent | itemIndent

private def Doc.Space.chars : Doc.Space → List Char
  | .tight => []
  | .blank => [' ']
  | .newline => ['\n']
  | .fieldIndent => ['\n', ' ', ' ']
  | .itemIndent => ['\n', ' ', ' ', ' ', ' ']

private def Doc.hexDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

private def Doc.escape (char : Char) : List Char :=
  if char = '"' then ['\\', '"']
  else if char = '\\' then ['\\', '\\']
  else if char = '\n' then ['\\', 'n']
  else if char = '\r' then ['\\', 'r']
  else if char.toNat < 0x20 then
    ['\\', 'u', '0', '0', Doc.hexDigit (char.toNat / 16), Doc.hexDigit (char.toNat % 16)]
  else [char]

private def Doc.Token.chars : Doc.Token → List Char
  | .openObject => ['{']
  | .closeObject => ['}']
  | .openArray => ['[']
  | .closeArray => [']']
  | .colon => [':']
  | .comma => [',']
  | .string value => '"' :: value.toList.flatMap Doc.escape ++ ['"']

private def Doc.Value.pieces : Doc.Value → List (Doc.Space × Doc.Token)
  | .string value => [(.blank, .string value)]
  | .array [] => [(.blank, .openArray), (.tight, .closeArray)]
  | .array (first :: rest) =>
    (.blank, .openArray) :: (.itemIndent, .string first) ::
      rest.flatMap (fun value => [(.tight, .comma), (.itemIndent, .string value)]) ++
      [(.fieldIndent, .closeArray)]

private def Doc.fieldPieces (field : String × Doc.Value) : List (Doc.Space × Doc.Token) :=
  (.fieldIndent, .string field.1) :: (.tight, .colon) :: field.2.pieces

private def Doc.pieces (doc : Doc) : List (Doc.Space × Doc.Token) :=
  match doc.fields with
  | [] => [(.tight, .openObject), (.tight, .closeObject)]
  | first :: rest =>
    (.tight, .openObject) :: Doc.fieldPieces first ++
      rest.flatMap (fun field => (.tight, .comma) :: Doc.fieldPieces field) ++ [(.newline, .closeObject)]

private def Doc.layout (pieces : List (Doc.Space × Doc.Token)) : List Char :=
  pieces.flatMap fun (gap, token) => gap.chars ++ token.chars

def Doc.render (doc : Doc) : String :=
  String.ofList (Doc.layout doc.pieces ++ ['\n'])

private def Doc.punctuation : Char → Option Doc.Token
  | '{' => some .openObject
  | '}' => some .closeObject
  | '[' => some .openArray
  | ']' => some .closeArray
  | ':' => some .colon
  | ',' => some .comma
  | _ => none

private def Doc.unescape : Char → Option Char
  | '"' => some '"'
  | '\\' => some '\\'
  | '/' => some '/'
  | 'b' => some '\x08'
  | 'f' => some '\x0c'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | _ => none

private def Doc.hexValue (char : Char) : Option Nat :=
  if '0' ≤ char ∧ char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char ∧ char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char ∧ char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private inductive Doc.Lexer where
  | between
  | inString (read : List Char)
  | afterBackslash (read : List Char)
  | inUnicode (read : List Char) (value remaining : Nat)

private def Doc.Lexer.run : Doc.Lexer → List Doc.Token → List Char → Option (List Doc.Token)
  | .between, tokens, [] => some tokens.reverse
  | .between, tokens, char :: rest =>
    match Doc.punctuation char with
    | some token => Doc.Lexer.run .between (token :: tokens) rest
    | none =>
      if char = '"' then Doc.Lexer.run (.inString []) tokens rest
      else if char = ' ' ∨ char = '\n' ∨ char = '\r' ∨ char = '\t' then Doc.Lexer.run .between tokens rest
      else none
  | .inString read, tokens, char :: rest =>
    if char = '"' then Doc.Lexer.run .between (.string (String.ofList read.reverse) :: tokens) rest
    else if char = '\\' then Doc.Lexer.run (.afterBackslash read) tokens rest
    else if char.toNat < 0x20 then none
    else Doc.Lexer.run (.inString (char :: read)) tokens rest
  | .afterBackslash read, tokens, char :: rest =>
    match Doc.unescape char with
    | some decoded => Doc.Lexer.run (.inString (decoded :: read)) tokens rest
    | none => if char = 'u' then Doc.Lexer.run (.inUnicode read 0 4) tokens rest else none
  | .inUnicode read value remaining, tokens, char :: rest =>
    match Doc.hexValue char with
    | none => none
    | some digit =>
      if remaining ≤ 1 then
        if 16 * value + digit < 0xD800 ∨ 0xDFFF < 16 * value + digit then
          Doc.Lexer.run (.inString (Char.ofNat (16 * value + digit) :: read)) tokens rest
        else none
      else Doc.Lexer.run (.inUnicode read (16 * value + digit) (remaining - 1)) tokens rest
  | _, _, [] => none

private inductive Doc.Parser where
  | start
  | firstKey
  | nextKey
  | afterKey (key : String)
  | afterColon (key : String)
  | firstItem (key : String)
  | nextItem (key : String) (items : List String)
  | afterItem (key : String) (items : List String)
  | afterField
  | finished

private def Doc.Parser.run : Doc.Parser → List (String × Doc.Value) → List Doc.Token → Option Doc
  | .start, fields, .openObject :: rest => Doc.Parser.run .firstKey fields rest
  | .firstKey, fields, .closeObject :: rest => Doc.Parser.run .finished fields rest
  | .firstKey, fields, .string key :: rest => Doc.Parser.run (.afterKey key) fields rest
  | .nextKey, fields, .string key :: rest => Doc.Parser.run (.afterKey key) fields rest
  | .afterKey key, fields, .colon :: rest => Doc.Parser.run (.afterColon key) fields rest
  | .afterColon key, fields, .string value :: rest =>
    Doc.Parser.run .afterField ((key, .string value) :: fields) rest
  | .afterColon key, fields, .openArray :: rest => Doc.Parser.run (.firstItem key) fields rest
  | .firstItem key, fields, .closeArray :: rest => Doc.Parser.run .afterField ((key, .array []) :: fields) rest
  | .firstItem key, fields, .string value :: rest => Doc.Parser.run (.afterItem key [value]) fields rest
  | .nextItem key items, fields, .string value :: rest =>
    Doc.Parser.run (.afterItem key (value :: items)) fields rest
  | .afterItem key items, fields, .comma :: rest => Doc.Parser.run (.nextItem key items) fields rest
  | .afterItem key items, fields, .closeArray :: rest =>
    Doc.Parser.run .afterField ((key, .array items.reverse) :: fields) rest
  | .afterField, fields, .comma :: rest => Doc.Parser.run .nextKey fields rest
  | .afterField, fields, .closeObject :: rest => Doc.Parser.run .finished fields rest
  | .finished, fields, [] => some ⟨fields.reverse⟩
  | _, _, _ => none

def Doc.parse (text : String) : Option Doc :=
  (Doc.Lexer.run .between [] text.toList).bind (Doc.Parser.run .start [])

private theorem Doc.Lexer.run_gap (gap : Doc.Space) (tokens : List Doc.Token) (rest : List Char) :
    Doc.Lexer.run .between tokens (gap.chars ++ rest) = Doc.Lexer.run .between tokens rest := by
  cases gap <;> rfl

private theorem Doc.hexValue_hexDigit : ∀ digit, digit < 16 → Doc.hexValue (Doc.hexDigit digit) = some digit := by
  decide

private theorem Doc.Lexer.run_plain {read : List Char} {tokens : List Doc.Token} {char : Char} {rest : List Char}
    (notQuote : char ≠ '"') (notBackslash : char ≠ '\\') (printable : ¬ char.toNat < 0x20) :
    Doc.Lexer.run (.inString read) tokens (char :: rest) = Doc.Lexer.run (.inString (char :: read)) tokens rest := by
  conv => lhs; unfold Doc.Lexer.run
  simp only [notQuote, notBackslash, printable, ↓reduceIte]

private theorem Doc.Lexer.run_hex {read : List Char} {tokens : List Doc.Token} {value remaining digit : Nat}
    {char : Char} {rest : List Char} (hex : Doc.hexValue char = some digit) :
    Doc.Lexer.run (.inUnicode read value remaining) tokens (char :: rest) =
      if remaining ≤ 1 then
        if 16 * value + digit < 0xD800 ∨ 0xDFFF < 16 * value + digit then
          Doc.Lexer.run (.inString (Char.ofNat (16 * value + digit) :: read)) tokens rest
        else none
      else Doc.Lexer.run (.inUnicode read (16 * value + digit) (remaining - 1)) tokens rest := by
  conv => lhs; unfold Doc.Lexer.run
  rw [hex]

private theorem Doc.Lexer.run_escape (char : Char) (read : List Char) (tokens : List Doc.Token) (rest : List Char) :
    Doc.Lexer.run (.inString read) tokens (Doc.escape char ++ rest) =
      Doc.Lexer.run (.inString (char :: read)) tokens rest := by
  unfold Doc.escape
  split
  · subst_vars; rfl
  split
  · subst_vars; rfl
  split
  · subst_vars; rfl
  split
  · subst_vars; rfl
  split
  · rename_i small
    have high : Doc.hexValue (Doc.hexDigit (char.toNat / 16)) = some (char.toNat / 16) :=
      Doc.hexValue_hexDigit _ (by omega)
    have low : Doc.hexValue (Doc.hexDigit (char.toNat % 16)) = some (char.toNat % 16) :=
      Doc.hexValue_hexDigit _ (Nat.mod_lt _ (by decide))
    show Doc.Lexer.run (.inUnicode read 0 2) tokens
      (Doc.hexDigit (char.toNat / 16) :: Doc.hexDigit (char.toNat % 16) :: rest) = _
    rw [Doc.Lexer.run_hex high, Doc.Lexer.run_hex low]
    have scalar : char.toNat < 0xD800 := by omega
    simp [Nat.div_add_mod, scalar]
  · rename_i quote backslash _ _ large
    exact Doc.Lexer.run_plain quote backslash large

private theorem Doc.Lexer.run_escapes (chars read : List Char) (tokens : List Doc.Token) (rest : List Char) :
    Doc.Lexer.run (.inString read) tokens (chars.flatMap Doc.escape ++ rest) =
      Doc.Lexer.run (.inString (chars.reverse ++ read)) tokens rest := by
  induction chars generalizing read with
  | nil => rfl
  | cons char chars ih => simp [List.flatMap_cons, List.append_assoc, Doc.Lexer.run_escape, ih]

private theorem Doc.Lexer.run_token (token : Doc.Token) (tokens : List Doc.Token) (rest : List Char) :
    Doc.Lexer.run .between tokens (token.chars ++ rest) = Doc.Lexer.run .between (token :: tokens) rest := by
  cases token with
  | string value =>
    show Doc.Lexer.run (.inString []) tokens (value.toList.flatMap Doc.escape ++ ['"'] ++ rest) = _
    rw [List.append_assoc, Doc.Lexer.run_escapes]
    simp [Doc.Lexer.run, String.ofList_toList]
  | _ => rfl

private theorem Doc.layout_cons (gap : Doc.Space) (token : Doc.Token) (pieces : List (Doc.Space × Doc.Token)) :
    Doc.layout ((gap, token) :: pieces) = gap.chars ++ token.chars ++ Doc.layout pieces := rfl

private theorem Doc.Lexer.run_layout (pieces : List (Doc.Space × Doc.Token)) (tokens : List Doc.Token)
    (rest : List Char) :
    Doc.Lexer.run .between tokens (Doc.layout pieces ++ rest) =
      Doc.Lexer.run .between ((pieces.map Prod.snd).reverse ++ tokens) rest := by
  induction pieces generalizing tokens with
  | nil => rfl
  | cons piece pieces ih =>
    obtain ⟨gap, token⟩ := piece
    rw [Doc.layout_cons, List.append_assoc, List.append_assoc, Doc.Lexer.run_gap, Doc.Lexer.run_token, ih]
    simp

private theorem Doc.Parser.run_items (key : String) (items values : List String) (fields : List (String × Doc.Value))
    (rest : List Doc.Token) :
    Doc.Parser.run (.afterItem key items) fields
      ((values.flatMap fun value => [(Doc.Space.tight, Doc.Token.comma), (.itemIndent, .string value)]).map
        Prod.snd ++ .closeArray :: rest) =
      Doc.Parser.run .afterField ((key, .array (items.reverse ++ values)) :: fields) rest := by
  induction values generalizing items with
  | nil => simp [Doc.Parser.run]
  | cons value values ih => simp [Doc.Parser.run, ih]

private theorem Doc.Parser.run_value (key : String) (value : Doc.Value) (fields : List (String × Doc.Value))
    (rest : List Doc.Token) :
    Doc.Parser.run (.afterColon key) fields (value.pieces.map Prod.snd ++ rest) =
      Doc.Parser.run .afterField ((key, value) :: fields) rest := by
  cases value with
  | string value => rfl
  | array values =>
    cases values with
    | nil => rfl
    | cons first others =>
      simp only [Doc.Value.pieces, List.map_cons, List.map_append, List.cons_append, List.append_assoc]
      simp [Doc.Parser.run, Doc.Parser.run_items]

private theorem Doc.Parser.run_fields (others fields : List (String × Doc.Value)) (rest : List Doc.Token) :
    Doc.Parser.run .afterField fields
      ((others.flatMap fun field => (Doc.Space.tight, Doc.Token.comma) :: Doc.fieldPieces field).map Prod.snd ++
        .closeObject :: rest) =
      Doc.Parser.run .finished (others.reverse ++ fields) rest := by
  induction others generalizing fields with
  | nil => rfl
  | cons field others ih =>
    rw [List.flatMap_cons, List.map_append, List.append_assoc]
    show Doc.Parser.run (.afterColon field.1) fields (field.2.pieces.map Prod.snd ++ _) = _
    rw [Doc.Parser.run_value, ih]
    simp

theorem Doc.parse_render (doc : Doc) : Doc.parse (Doc.render doc) = some doc := by
  unfold Doc.parse Doc.render
  rw [String.toList_ofList, Doc.Lexer.run_layout, show ['\n'] = Doc.Space.newline.chars ++ [] from rfl,
    Doc.Lexer.run_gap]
  simp only [Doc.Lexer.run, List.append_nil, List.reverse_reverse, Option.bind_some]
  obtain ⟨fields⟩ := doc
  cases fields with
  | nil => rfl
  | cons first others =>
    simp only [Doc.pieces, List.map_cons, List.map_append, List.append_assoc]
    show Doc.Parser.run (.afterColon first.1) [] (first.2.pieces.map Prod.snd ++ _) = _
    rw [Doc.Parser.run_value, List.map_nil, Doc.Parser.run_fields]
    simp [Doc.Parser.run]

end SoftwareChallenge
