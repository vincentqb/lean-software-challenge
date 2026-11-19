module

public import SoftwareChallengeTests.Fixtures.CoreCode
public import SoftwareChallengeTests.Fixtures.WorldSpec
meta import SoftwareChallenge

public section

namespace SoftwareChallengeTests.Fixtures

initialize counter : IO.Ref Nat ← IO.mkRef 0

partial def drain (stream : IO.FS.Stream) : IO Unit := do
  let line ← stream.getLine
  unless line.isEmpty do drain stream

partial def loopIdentity (n : Nat) : IO Unit := do
  unless identity n == n do loopIdentity (n + 1)

def successor (n : Nat) : Nat := nativeSucc n

theorem successor_grows (agrees : SuccAgrees nativeSucc) (n : Nat) : n < successor n := by
  simp only [successor, agrees n]
  omega

theorem successor_positive (_agrees : SuccAgrees nativeSucc) (n : Nat) : 0 < n + 1 := Nat.succ_pos n

theorem successor_correct (agrees : SuccAgrees nativeSucc) (n : Nat) : successor n = n + 1 := agrees n

theorem successor_correct_rejects_identity :
    ¬ (SuccAgrees Nat.succ → ∀ n : Nat, (fun n : Nat => n) n = n + 1) := by
  intro h
  exact absurd (h (fun _ => rfl) 0) (by decide)

theorem uses_unchecked (h : Unchecked) : wrongSucc 0 = 0 := h 0

theorem uses_live (now : Nat → Nat) (h : ClockAdvances now) (t : Nat) : t ≤ now t := h t

Check SuccAgrees nativeSucc : nativeSucc 41 = 41 + 1

Check ClockAdvances id := do
  let first ← IO.monoMsNow
  let second ← IO.monoMsNow
  unless first ≤ second do throw (IO.userError "the monotonic clock ran backwards")

Check WrongSuccAgrees : wrongSucc 1 = 1 + 1

Check WrongSuccAgrees := throw (IO.userError "ran during the build")

theorem succ_at_leaves (h : SuccAt (leafSum 30 1)) : nativeSucc (leafSum 30 1) = leafSum 30 1 + 1 := h

Check SuccAt 0 : nativeSucc 0 = 0 + 1

theorem succ_everywhere (h : ∀ n, SuccAt n) : nativeSucc 1 = 1 + 1 := h 1

theorem succ_on_positives (h : ∀ n, n > 0 → SuccAt n) : nativeSucc 1 = 1 + 1 := h 1 (by decide)

theorem succ_everywhere_ignored (_h : ∀ n, SuccAt n) : 1 = 1 := rfl

theorem unchecked_everywhere (h : ∀ n, UncheckedAt n) : wrongSucc 0 = 0 := h 0

theorem unchecked_on_positives (h : ∀ n, n > 0 → UncheckedAt n) : wrongSucc 1 = 1 := h 1 (by decide)

theorem hidden_succ (agrees : SuccHidden) : nativeSucc 0 = 0 + 1 := by
  unfold SuccHidden at agrees
  exact agrees 0

theorem bounded_under_claim (n : Nat) (_h : ∀ m, m > 0 → SuccAt m) (small : n < 5) : n < 6 := by omega

end SoftwareChallengeTests.Fixtures
