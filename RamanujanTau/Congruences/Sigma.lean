import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Int.ModEq

/-! # Divisor power sums `σ_k`

For each fixed odd weight `k`, `σ_k(n) = Σ_{d ∣ n} d^k`. These show up on the
right-hand side of every classical Ramanujan congruence:

* `σ_3` — appears in the mod-7 congruence (Ramanujan 1916).
* `σ_7` — appears in the mod-27 (= 3³) congruence (Wilton 1929).
* `σ_9` — appears in the mod-25 (= 5²) congruence (Ramanujan 1916).
* `σ_11` — appears in the mod-691 and mod-2¹¹ congruences (Ramanujan 1916,
  Wilton 1929, Kolberg 1962). Defined separately in `Congruences.lean`.

Each `σ_k` is computable for small `n` via `decide`, since it is a `Finset.sum`
over `Nat.divisors n`. The small-value lemmas below are used only for numerical
sanity checks; the deep modular-form content is exposed elsewhere as
hypothesis classes.
-/

namespace RamanujanTau

open Finset

/-- `σ_3(n) = Σ_{d ∣ n} d³`. -/
def sigma3 (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ)^3

/-- `σ_7(n) = Σ_{d ∣ n} d⁷`. -/
def sigma7 (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ)^7

/-- `σ_9(n) = Σ_{d ∣ n} d⁹`. -/
def sigma9 (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ)^9

/-! ## Small values of `σ_3`

Listed for `n = 1..7` to support the mod-7 numerical checks. -/

theorem sigma3_one : sigma3 1 = 1 := by unfold sigma3; decide
theorem sigma3_two : sigma3 2 = 9 := by unfold sigma3; decide
theorem sigma3_three : sigma3 3 = 28 := by unfold sigma3; decide
theorem sigma3_four : sigma3 4 = 73 := by unfold sigma3; decide
theorem sigma3_five : sigma3 5 = 126 := by unfold sigma3; decide
theorem sigma3_six : sigma3 6 = 252 := by unfold sigma3; decide
theorem sigma3_seven : sigma3 7 = 344 := by unfold sigma3; decide

/-! ## Small values of `σ_7`

Listed for `n = 1..7` to support the mod-27 numerical checks. -/

theorem sigma7_one : sigma7 1 = 1 := by unfold sigma7; decide
theorem sigma7_two : sigma7 2 = 129 := by unfold sigma7; decide
theorem sigma7_three : sigma7 3 = 2188 := by unfold sigma7; decide
theorem sigma7_four : sigma7 4 = 16513 := by unfold sigma7; decide
theorem sigma7_five : sigma7 5 = 78126 := by unfold sigma7; decide
theorem sigma7_six : sigma7 6 = 282252 := by unfold sigma7; decide
theorem sigma7_seven : sigma7 7 = 823544 := by unfold sigma7; decide

/-! ## Small values of `σ_9`

Listed for `n = 1..7` to support the mod-25 numerical checks. -/

theorem sigma9_one : sigma9 1 = 1 := by unfold sigma9; decide
theorem sigma9_two : sigma9 2 = 513 := by unfold sigma9; decide
theorem sigma9_three : sigma9 3 = 19684 := by unfold sigma9; decide
theorem sigma9_four : sigma9 4 = 262657 := by unfold sigma9; decide

end RamanujanTau
