module

public import SoftwareChallengeTests.Fixtures.CoreCode
meta import SoftwareChallenge

set_option warn.sorry false

public section

namespace SoftwareChallengeTests.Fixtures.Challenge

def double : Nat → Nat := sorry

def triple (n : Nat) : Nat := 3 * n

theorem double_even (n : Nat) : double n % 2 = 0 := sorry

@[kills double_even] theorem double_even_rejects_identity : ¬ ∀ n : Nat, (fun n => n) n % 2 = 0 := sorry

@[kills double_even] theorem double_even_rejects_nothing : ¬ ∀ n : Nat, n = n := sorry

@[kills triple] theorem triple_rejects_nothing : ¬ ∀ n : Nat, 3 * n = 3 * n := sorry

@[terminates triple] theorem double_zero : double 0 = 0 := sorry

theorem double_one (n : Nat) : double n ≠ 1 := sorry

theorem double_one_rejects_one : ¬ ∀ n : Nat, (fun _ => 1) n ≠ 1 := sorry

end SoftwareChallengeTests.Fixtures.Challenge
