import RamanujanTau.EulerFactor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

/-! # The general closed form `τ(p^r)` via Gegenbauer / Chebyshev-U polynomials

The Hecke recurrence `τ(p^{r+1}) = τ(p)·τ(p^r) − p¹¹·τ(p^{r-1})` makes `r ↦ τ(p^r)` a member of the
**Gegenbauer / Chebyshev-second-kind** polynomial family: the two-variable Dickson polynomials
`G_r(s,q)` defined by `G_0 = 1`, `G_1 = s`, `G_{r+2} = s·G_{r+1} − q·G_r`. With `(s,q) = (τ p, p¹¹)`
they compute every `τ(p^r)` at once.

We prove, all kernel-verified:
* `tau_ppow_eq_gegen` — the **general closed form** `τ(p^r) = G_r(τ p, p¹¹)` for all `r`.
* `gegen_eq_sum` — the **explicit Gegenbauer formula**
  `G_r(s,q) = ∑_{j} (−1)^j · C(r−j, j) · q^j · s^{r−2j}`,
  whose coefficients are the Gegenbauer/Chebyshev-U binomials (proved via Pascal's rule).
* `tau_ppow_eq_sum` — combining the two:
  `τ(p^r) = ∑_{j} (−1)^j · C(r−j, j) · p^{11j} · τ(p)^{r−2j}`.

These subsume the fixed-exponent forms `τ(p²), …, τ(p⁷)` (the proofworld-discovered `HeckePowers`).
-/

namespace RamanujanTau

open Finset

/-- Dickson/Gegenbauer recurrence family: `G_0 = 1`, `G_1 = s`, `G_{r+2} = s·G_{r+1} − q·G_r`.
This is the (homogenized) Chebyshev polynomial of the second kind `U_r`, i.e. the Gegenbauer
polynomial `C_r^{(1)}`. With `(s,q) = (τ p, p¹¹)` it equals `τ(p^r)`. -/
def gegen (s q : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => s
  | (r + 2) => s * gegen s q (r + 1) - q * gegen s q r

@[simp] theorem gegen_zero (s q : ℤ) : gegen s q 0 = 1 := rfl
@[simp] theorem gegen_one (s q : ℤ) : gegen s q 1 = s := rfl

/-- The defining Gegenbauer/Chebyshev three-term recurrence. -/
theorem gegen_succ_succ (s q : ℤ) (r : ℕ) :
    gegen s q (r + 2) = s * gegen s q (r + 1) - q * gegen s q r := rfl

/-! ## Part 1 — the general closed form -/

/-- **General closed form for `τ(p^r)`.** For every prime `p` and every `r`,
`τ(p^r) = G_r(τ p, p¹¹)` — the Gegenbauer/Chebyshev-U value. A single theorem giving all prime-power
values of `τ`, of which `tau_prime_sq`, `tau_prime_cube`, and `HeckePowers.τ(p⁴…p⁷)` are instances. -/
theorem tau_ppow_eq_gegen [TauHeckeRecurrence] {p : ℕ} (hp : p.Prime) (r : ℕ) :
    τ (p ^ r) = gegen (τ p) ((p : ℤ) ^ 11) r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | _ | k
    · simp [tau_one]
    · simp
    · have hrec := euler_factor_coeff hp k
      have e1 := ih (k + 1) (by omega)
      have e0 := ih k (by omega)
      rw [show k + 1 + 1 = k + 2 from rfl, gegen_succ_succ, ← e1, ← e0]
      linarith

/-! ## Part 2 — the explicit Gegenbauer binomial formula

The coefficients of `G_r` are the Gegenbauer/Chebyshev-U binomials `(−1)^j C(r−j, j)`. We prove the
explicit sum satisfies the three-term recurrence via Pascal's rule, hence equals `gegen`. -/

/-- The `j`-th Gegenbauer term `(−1)^j C(n−j, j) q^j s^{n−2j}` (terms with `2j > n` vanish: `C = 0`). -/
private def gterm (s q : ℤ) (n j : ℕ) : ℤ :=
  (-1) ^ j * (Nat.choose (n - j) j : ℤ) * q ^ j * s ^ (n - 2 * j)

private def gsum (s q : ℤ) (r : ℕ) : ℤ := ∑ j ∈ range (r + 1), gterm s q r j

private theorem gsum_eq (s q : ℤ) (m : ℕ) : gsum s q m = ∑ j ∈ range (m + 1), gterm s q m j := rfl
private theorem gsum_zero (s q : ℤ) : gsum s q 0 = 1 := by simp [gsum, gterm]
private theorem gsum_one (s q : ℤ) : gsum s q 1 = s := by simp [gsum, gterm, Finset.sum_range_succ]

/-- The term-level Gegenbauer identity, by Pascal's rule `C((r+1-j)+1, j+1) = C(r+1-j, j) + C(r+1-j, j+1)`,
with the three boundary regimes `r < 2j`, `r = 2j`, `r > 2j`. -/
private theorem gterm_rec (s q : ℤ) (r j : ℕ) :
    gterm s q (r + 2) (j + 1) = s * gterm s q (r + 1) (j + 1) - q * gterm s q r j := by
  rcases lt_trichotomy r (2 * j) with hC | hB | hA
  · -- r < 2j : all three binomials vanish
    unfold gterm
    rw [Nat.choose_eq_zero_of_lt (show (r + 2) - (j + 1) < j + 1 by omega),
        Nat.choose_eq_zero_of_lt (show (r + 1) - (j + 1) < j + 1 by omega),
        Nat.choose_eq_zero_of_lt (show r - j < j by omega)]
    push_cast; ring
  · -- r = 2j : middle term vanishes, the two ends balance
    subst hB
    unfold gterm
    rw [show 2 * j + 2 - (j + 1) = j + 1 by omega, show 2 * j + 1 - (j + 1) = j by omega,
        show 2 * j - j = j by omega, show 2 * j + 2 - 2 * (j + 1) = 0 by omega,
        show 2 * j + 1 - 2 * (j + 1) = 0 by omega, show 2 * j - 2 * j = 0 by omega,
        Nat.choose_self, Nat.choose_self, Nat.choose_eq_zero_of_lt (show j < j + 1 by omega)]
    push_cast; ring
  · -- 2j < r : Pascal's rule
    obtain ⟨t, rfl⟩ : ∃ t, r = 2 * j + 1 + t := ⟨r - (2 * j + 1), by omega⟩
    unfold gterm
    rw [show 2 * j + 1 + t + 2 - (j + 1) = (j + 1 + t) + 1 by omega,
        show 2 * j + 1 + t + 1 - (j + 1) = j + 1 + t by omega,
        show 2 * j + 1 + t - j = j + 1 + t by omega,
        show 2 * j + 1 + t + 2 - 2 * (j + 1) = t + 1 by omega,
        show 2 * j + 1 + t + 1 - 2 * (j + 1) = t by omega,
        show 2 * j + 1 + t - 2 * j = t + 1 by omega,
        Nat.choose_succ_succ (j + 1 + t) j]
    push_cast; ring

/-- The explicit Gegenbauer sum obeys the three-term recurrence (assembled from `gterm_rec`). -/
private theorem gsum_rec (s q : ℤ) (r : ℕ) :
    gsum s q (r + 2) = s * gsum s q (r + 1) - q * gsum s q r := by
  have g0r2 : gterm s q (r + 2) 0 = s ^ (r + 2) := by unfold gterm; simp
  have g0r1 : gterm s q (r + 1) 0 = s ^ (r + 1) := by unfold gterm; simp
  have top1 : gterm s q (r + 1) (r + 2) = 0 := by
    unfold gterm; rw [Nat.choose_eq_zero_of_lt (show (r + 1) - (r + 2) < r + 2 by omega)]; simp
  have top2 : gterm s q r (r + 1) = 0 := by
    unfold gterm; rw [Nat.choose_eq_zero_of_lt (show r - (r + 1) < r + 1 by omega)]; simp
  have hA : (∑ j ∈ range (r + 2), gterm s q (r + 1) (j + 1)) = gsum s q (r + 1) - s ^ (r + 1) := by
    rw [show r + 2 = r + 1 + 1 from rfl,
        Finset.sum_range_succ (fun j => gterm s q (r + 1) (j + 1)) (r + 1), top1, add_zero,
        gsum_eq s q (r + 1), Finset.sum_range_succ' (gterm s q (r + 1)) (r + 1), g0r1]
    ring
  have hB : (∑ j ∈ range (r + 2), gterm s q r j) = gsum s q r := by
    rw [show r + 2 = r + 1 + 1 from rfl, gsum_eq s q r,
        Finset.sum_range_succ (gterm s q r) (r + 1), top2, add_zero]
  rw [gsum_eq s q (r + 2), Finset.sum_range_succ' (gterm s q (r + 2)) (r + 2), g0r2,
      Finset.sum_congr rfl (fun j _ => gterm_rec s q r j), Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hA, hB]
  ring

/-- **Explicit Gegenbauer formula:** `G_r(s,q) = ∑_j (−1)^j C(r−j, j) q^j s^{r−2j}`. -/
theorem gegen_eq_sum (s q : ℤ) (r : ℕ) :
    gegen s q r
      = ∑ j ∈ range (r + 1), (-1) ^ j * (Nat.choose (r - j) j : ℤ) * q ^ j * s ^ (r - 2 * j) := by
  show gegen s q r = gsum s q r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | _ | k
    · rw [gsum_zero]; rfl
    · rw [gsum_one]; rfl
    · show gegen s q (k + 2) = gsum s q (k + 2)
      rw [gegen_succ_succ, gsum_rec, ih (k + 1) (by omega), ih k (by omega)]

/-- **Explicit closed form for `τ(p^r)`** (the Gegenbauer/Chebyshev-U binomial series):
`τ(p^r) = ∑_j (−1)^j C(r−j, j) p^{11j} τ(p)^{r−2j}`. -/
theorem tau_ppow_eq_sum [TauHeckeRecurrence] {p : ℕ} (hp : p.Prime) (r : ℕ) :
    τ (p ^ r) = ∑ j ∈ range (r + 1),
      (-1) ^ j * (Nat.choose (r - j) j : ℤ) * ((p : ℤ) ^ 11) ^ j * τ p ^ (r - 2 * j) := by
  rw [tau_ppow_eq_gegen hp, gegen_eq_sum]

end RamanujanTau
