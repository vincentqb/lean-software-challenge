module

public import Lean.Data.Name

public section

open Lean

namespace SoftwareChallenge

inductive Role where
  | coreSpec | worldSpec | coreCode | worldCode | tooling
  deriving DecidableEq, Repr

instance : ToString Role where
  toString
    | .coreSpec => "CoreSpec"
    | .worldSpec => "WorldSpec"
    | .coreCode => "CoreCode"
    | .worldCode => "WorldCode"
    | .tooling => "tooling"

def Role.Inner (role : Role) : Prop :=
  role = .coreSpec ∨ role = .worldSpec ∨ role = .coreCode

def Role.ofName (name : Name) : Role :=
  (name.components.findSome? fun component =>
    [Role.coreSpec, .worldSpec, .coreCode, .worldCode].find? (toString · == component.toString)).getD .tooling

structure Project where
  modules : Array (Name × Role)
  executable : Bool := false

def Project.ofPackage (modules : Array Name) (executable : Bool) : Project :=
  { modules := modules.map fun name => (name, Role.ofName name), executable }

def Project.role? (project : Project) (name : Name) : Option Role :=
  (project.modules.find? (·.1 == name)).map (·.2)

structure ImportFact where
  name : Name
  comptime : Bool

structure ModuleFact where
  name : Name
  usesModuleSystem : Bool
  imports : Array ImportFact

structure DeclarationFact where
  name : Name
  moduleName : Name
  computational : Bool
  isUnsafe : Bool
  isPartial : Bool
  external : Bool
  unfoldable : Bool
  replaced : Bool
  initializes : Bool
  effects : Bool
  debug : Bool
  axioms : Array Name

structure Inventory where
  modules : Array ModuleFact
  declarations : Array DeclarationFact

def Inventory.RuntimeImport (inventory : Inventory) (source target : Name) : Prop :=
  ∃ fact ∈ inventory.modules, fact.name = source ∧
    ∃ dependency ∈ fact.imports, dependency.name = target ∧ dependency.comptime = false

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def Role.permits : Role → Role → Bool
  | .tooling, _ => true
  | .worldCode, target => target != .tooling
  | .worldSpec, target => target == .coreSpec || target == .worldSpec
  | .coreCode, target => target == .coreSpec || target == .coreCode
  | .coreSpec, target => target == .coreSpec

def Project.admits (project : Project) (source : Role) (dependency : ImportFact) : Bool :=
  dependency.comptime || match project.role? dependency.name with
    | some target => source.permits target
    | none => true

def Project.moduleAdmitted (project : Project) (fact : ModuleFact) : Bool :=
  match project.role? fact.name with
  | some role => fact.usesModuleSystem && fact.imports.all (project.admits role)
  | none => false

def DeclarationFact.reasons (role : Role) (fact : DeclarationFact) : List String :=
  let flags := [(fact.isUnsafe, "unsafe"), (fact.isPartial, "partial"),
    (fact.external, "@[extern]"), (fact.replaced, "@[implemented_by]"),
    (fact.initializes, "initializer"), (fact.effects, "IO"), (fact.debug, "dbg builtin")]
  let raised := fun (allowed : List String) =>
    flags.filterMap fun (set, reason) => if set && !allowed.contains reason then some reason else none
  if !fact.computational then [] else match role with
    | .coreSpec | .coreCode => raised []
    | .worldSpec =>
      if !fact.external then raised []
      else if fact.unfoldable then ["@[extern] with a body the kernel unfolds"]
      else raised ["@[extern]", "IO"]
    | .worldCode => raised ["partial", "initializer", "IO", "dbg builtin"]
    | .tooling => []

def Project.check (project : Project) (inventory : Inventory) : Bool :=
  inventory.modules.all project.moduleAdmitted &&
    inventory.declarations.all fun fact => match project.role? fact.moduleName with
      | some role => fact.axioms.isEmpty && (fact.reasons role).isEmpty
      | none => false

private theorem permits_inner {source target : Role} (permitted : source.permits target = true)
    (inner : source.Inner) : target.Inner := by
  cases source <;> cases target <;> simp_all [Role.Inner, Role.permits]

private theorem import_step {project : Project} {inventory : Inventory}
    (accepted : project.check inventory = true) {source target : Name}
    (inner : ∀ role, project.role? source = some role → role.Inner)
    (edge : inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  obtain ⟨fact, member, rfl, dependency, imported, rfl, runtime⟩ := edge
  simp only [Project.check, Bool.and_eq_true, Array.all_eq_true'] at accepted
  have admitted := accepted.1 fact member
  unfold Project.moduleAdmitted at admitted
  intro reached found
  cases owner : project.role? fact.name with
  | none => simp [owner] at admitted
  | some role =>
    simp only [owner, Bool.and_eq_true, Array.all_eq_true'] at admitted
    have permitted := admitted.2 dependency imported
    simp only [Project.admits, runtime, Bool.false_or, found] at permitted
    exact permits_inner permitted (inner role owner)

theorem layering_sound (project : Project) (inventory : Inventory)
    (accepted : project.check inventory = true) (source target : Name) (role : Role)
    (classified : project.role? source = some role) (inner : role.Inner)
    (reaches : Relation.TransGen inventory.RuntimeImport source target) :
    ∀ reached, project.role? target = some reached → reached.Inner := by
  induction reaches with
  | single edge => exact import_step accepted (fun _ owner => by simp_all) edge
  | tail _ edge previous => exact import_step accepted previous edge

inductive Universe where
  | zero
  | succ (level : Universe)
  | max (left right : Universe)
  | imax (left right : Universe)
  | param (name : Name)
  | mvar (name : Name)
  deriving DecidableEq

inductive Shape where
  | bvar (index : Nat)
  | fvar (name : Name)
  | mvar (name : Name)
  | sort (level : Universe)
  | const (name : Name) (levels : List Universe)
  | app (function argument : Shape)
  | lam (type body : Shape)
  | forallE (type body : Shape)
  | letE (type value body : Shape)
  | natLit (value : Nat)
  | strLit (value : String)
  | proj (structureName : Name) (index : Nat) (value : Shape)
  deriving DecidableEq

abbrev Witnesses := List (Name × Shape)

def Witnesses.find? : Witnesses → Name → Option Shape
  | [], _ => none
  | (key, witness) :: rest, name => if key = name then some witness else find? rest name

namespace Shape

def closedUnder (depth : Nat) : Shape → Bool
  | .bvar index => index < depth
  | .app function argument => function.closedUnder depth && argument.closedUnder depth
  | .lam type body | .forallE type body => type.closedUnder depth && body.closedUnder (depth + 1)
  | .letE type value body =>
    type.closedUnder depth && value.closedUnder depth && body.closedUnder (depth + 1)
  | .proj _ _ value => value.closedUnder depth
  | _ => true

def subst (replaceable : Name → Bool) (σ : Witnesses) : Shape → Shape
  | .const name levels => if replaceable name then (σ.find? name).getD (.const name levels) else .const name levels
  | .app function argument => .app (function.subst replaceable σ) (argument.subst replaceable σ)
  | .lam type body => .lam (type.subst replaceable σ) (body.subst replaceable σ)
  | .forallE type body => .forallE (type.subst replaceable σ) (body.subst replaceable σ)
  | .letE type value body =>
    .letE (type.subst replaceable σ) (value.subst replaceable σ) (body.subst replaceable σ)
  | .proj structureName index value => .proj structureName index (value.subst replaceable σ)
  | term => term

def collect (replaceable : Name → Bool) : Shape → Shape → Witnesses → Witnesses
  | .const name levels, target, σ =>
    if replaceable name ∧ σ.find? name = none ∧ target ≠ .const name levels then (name, target) :: σ else σ
  | .app f a, .app g b, σ => collect replaceable a b (collect replaceable f g σ)
  | .lam t b, .lam u c, σ | .forallE t b, .forallE u c, σ =>
    collect replaceable b c (collect replaceable t u σ)
  | .letE t v b, .letE u w c, σ =>
    collect replaceable b c (collect replaceable v w (collect replaceable t u σ))
  | .proj _ _ v, .proj _ _ w, σ => collect replaceable v w σ
  | _, _, σ => σ

def witnesses? (replaceable : Name → Bool) (pattern target : Shape) : Option Witnesses :=
  let σ := collect replaceable pattern target []
  if σ.all (·.2.closedUnder 0) ∧ pattern.subst replaceable σ = target then some σ else none

private theorem find?_mem {σ : Witnesses} {name : Name} {witness : Shape}
    (found : σ.find? name = some witness) : (name, witness) ∈ σ := by
  induction σ with
  | nil => simp [Witnesses.find?] at found
  | cons entry rest ih =>
    obtain ⟨key, w⟩ := entry
    by_cases same : key = name
    · subst same; simp_all [Witnesses.find?]
    · simp only [Witnesses.find?, same, ite_false] at found
      exact List.mem_cons_of_mem _ (ih found)

private theorem collect_extends {replaceable : Name → Bool} {σ' : Witnesses} {pattern : Shape}
    {σ : Witnesses} {name : Name} {witness : Shape} (found : σ.find? name = some witness) :
    (collect replaceable pattern (pattern.subst replaceable σ') σ).find? name = some witness := by
  induction pattern generalizing σ with
  | const key levels =>
    simp only [collect]
    split
    · rename_i h
      have : key ≠ name := fun same => by simp_all
      simp [Witnesses.find?, this, found]
    · exact found
  | app f a ihf iha => exact iha (ihf found)
  | lam t b iht ihb => exact ihb (iht found)
  | forallE t b iht ihb => exact ihb (iht found)
  | letE t v b iht ihv ihb => exact ihb (ihv (iht found))
  | proj _ _ v ih => exact ih found
  | _ => simpa [collect, subst] using found

private theorem collect_from {replaceable : Name → Bool} {σ' : Witnesses} {pattern : Shape}
    {σ : Witnesses} {entry : Name × Shape}
    (member : entry ∈ collect replaceable pattern (pattern.subst replaceable σ') σ) :
    entry ∈ σ ∨ replaceable entry.1 = true ∧ σ'.find? entry.1 = some entry.2 := by
  induction pattern generalizing σ with
  | const key levels =>
    simp only [collect] at member
    split at member
    · rename_i h
      rcases List.mem_cons.mp member with rfl | rest
      · obtain ⟨replaced, _, changed⟩ := h
        refine .inr ⟨replaced, ?_⟩
        simp only [subst, replaced, ite_true] at changed ⊢
        cases found : σ'.find? key <;> simp_all
      · exact .inl rest
    · exact .inl member
  | app f a ihf iha =>
    rcases iha member with inner | outer
    · exact ihf inner
    · exact .inr outer
  | lam t b iht ihb | forallE t b iht ihb =>
    rcases ihb member with inner | outer
    · exact iht inner
    · exact .inr outer
  | letE t v b iht ihv ihb =>
    rcases ihb member with inner | outer
    · rcases ihv inner with inner | outer
      · exact iht inner
      · exact .inr outer
    · exact .inr outer
  | proj _ _ v ih => exact ih member
  | _ => exact .inl (by simpa [collect, subst] using member)

private theorem collect_keeps {replaceable : Name → Bool} {σ' σ : Witnesses} {pattern : Shape}
    {name : Name} (found : (σ.find? name).isSome) :
    ((collect replaceable pattern (pattern.subst replaceable σ') σ).find? name).isSome := by
  obtain ⟨witness, found⟩ := Option.isSome_iff_exists.mp found
  simp [collect_extends found]

private theorem subst_collect {replaceable : Name → Bool} {σ' σ₀ σ : Witnesses} {pattern : Shape}
    (agrees : ∀ name witness, σ.find? name = some witness → σ'.find? name = some witness)
    (covers : ∀ name, ((collect replaceable pattern (pattern.subst replaceable σ') σ₀).find? name).isSome →
      (σ.find? name).isSome) :
    pattern.subst replaceable σ = pattern.subst replaceable σ' := by
  induction pattern generalizing σ₀ with
  | const key levels =>
    by_cases replaced : replaceable key = true
    · simp only [subst, replaced, ite_true]
      cases found : σ.find? key with
      | some witness => simp [agrees key witness found]
      | none =>
        have missing := covers key
        rw [found] at missing
        simp only [collect, subst, replaced, ite_true, Option.isSome_none] at missing
        split at missing
        · simp [Witnesses.find?] at missing
        · rename_i kept
          cases known : σ₀.find? key with
          | some _ => simp [known] at missing
          | none =>
            cases found' : σ'.find? key with
            | none => rfl
            | some w => simp_all
    · simp [subst, replaced]
  | app f a ihf iha =>
    simp only [subst]
    rw [ihf (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := a) found), iha covers]
  | lam t b iht ihb =>
    simp only [subst]
    rw [iht (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := b) found), ihb covers]
  | forallE t b iht ihb =>
    simp only [subst]
    rw [iht (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := b) found), ihb covers]
  | letE t v b iht ihv ihb =>
    simp only [subst]
    rw [iht (σ₀ := σ₀) fun name found => covers name (collect_keeps (pattern := b) (collect_keeps (pattern := v) found)),
      ihv (σ₀ := collect replaceable t (t.subst replaceable σ') σ₀) fun name found =>
        covers name (collect_keeps (pattern := b) found), ihb covers]
  | proj _ _ v ih => simp only [subst]; rw [ih covers]
  | _ => rfl

theorem witnesses?_sound {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (found : pattern.witnesses? replaceable target = some σ) :
    (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  simp only [witnesses?] at found
  split at found
  · rename_i accepted
    cases found
    exact ⟨List.all_eq_true.mp accepted.1, accepted.2⟩
  · cases found

theorem witnesses?_complete {replaceable : Name → Bool} {pattern target : Shape} {σ : Witnesses}
    (closed : ∀ entry ∈ σ, replaceable entry.1 = true → entry.2.closedUnder 0 = true)
    (instantiates : pattern.subst replaceable σ = target) :
    (pattern.witnesses? replaceable target).isSome := by
  subst instantiates
  have from_σ := fun (entry : Name × Shape)
      (member : entry ∈ collect replaceable pattern (pattern.subst replaceable σ) []) =>
    (collect_from member).resolve_left (by simp)
  have agrees : ∀ name witness,
      (collect replaceable pattern (pattern.subst replaceable σ) []).find? name = some witness →
      σ.find? name = some witness := fun name witness found => (from_σ _ (find?_mem found)).2
  have allClosed : (collect replaceable pattern (pattern.subst replaceable σ) []).all
      (·.2.closedUnder 0) = true := List.all_eq_true.mpr fun entry member => by
    obtain ⟨replaced, found⟩ := from_σ entry member
    simpa using closed _ (find?_mem found) replaced
  simp [witnesses?, allClosed, subst_collect agrees fun _ found => found]

theorem witnesses?_isSome_iff {replaceable : Name → Bool} {pattern target : Shape} :
    (pattern.witnesses? replaceable target).isSome ↔
      ∃ σ : Witnesses, (∀ entry ∈ σ, entry.2.closedUnder 0 = true) ∧ pattern.subst replaceable σ = target := by
  constructor
  · intro found
    obtain ⟨σ, found⟩ := Option.isSome_iff_exists.mp found
    exact ⟨σ, witnesses?_sound found⟩
  · rintro ⟨σ, closed, instantiates⟩
    exact witnesses?_complete (fun entry member _ => closed entry member) instantiates

end Shape

end SoftwareChallenge
