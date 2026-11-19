module

meta import SoftwareChallenge

set_option warn.sorry false

public section

namespace SoftwareChallengeTests.Fixtures.StrayChallenge

def double : Nat → Nat := sorry

theorem double_even (n : Nat) : double n % 2 = 0 := sorry

@[kills double_even] theorem double_even_rejects_identity : ¬ ∀ n : Nat, (fun n => n) n % 2 = 0 := sorry

private theorem double_two : double 2 = 4 := sorry

axiom double_axiom : double 1 = 2

inductive Color where
  | red
  | green

def triple (n : Nat) : Nat := 3 * n

end SoftwareChallengeTests.Fixtures.StrayChallenge
