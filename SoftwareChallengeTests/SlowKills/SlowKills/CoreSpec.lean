module

@[expose] public section

namespace SlowKills

def spin : Nat → Nat → Nat
  | 0, total => total
  | n + 1, total => spin n (total + n % 7)

end SlowKills
