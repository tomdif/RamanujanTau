/-
# Bailey campaign, rung 1: the Gaussian (q-)binomial coefficient

Goal of the campaign: prove the infinite identity χ₀ = 2F₀ − φ₀(−q) (its coefficient form is the hypothesis
of `MockTheta5.Formal.mtc5_chi0_of_coeff`). The standard route is a Bailey-pair argument. Mathlib has NONE of
the prerequisite q-series machinery (no Gaussian binomial, no q-binomial theorem, no Bailey pairs), so the
campaign builds it from the ground up over `PowerSeries ℤ` (q := X). The ladder:

  Tier 0  [DONE]  qpoch / qpochG + invertibility; summable family; F₀,χ₀,φ₀ as PowerSeries; reduction to coeffs.
  Tier 1  [HERE]  Gaussian binomial `gaussBinom n k` via q-Pascal; vanishing; symmetry; → q-binomial theorem.
  Tier 2          Bailey pair (def) + Bailey's lemma (the iteration generating Bailey pairs).
  Tier 3          the specific 5th-order Bailey pair / unit pair specialization.
  Tier 4          assemble the coefficient identity, discharge `mtc5_chi0_of_coeff`'s hypothesis → identity closed.

This file is rung 1: the Gaussian binomial and its defining q-Pascal recurrence, with the diagonal-vanishing
fact. Fully proven, no `sorry`. (Each higher tier is a substantial formalization — the loop attacks them rung
by rung; this is the bottom.)
-/
import Mathlib.RingTheory.PowerSeries.Basic

namespace MockTheta5.Bailey
open PowerSeries

/-- Gaussian (q-)binomial coefficient `[n,k]_q` over `ℤ⟦X⟧` (q := X), via the q-Pascal recurrence
`[n+1, k+1] = [n,k] + qᵏ⁺¹·[n,k+1]`. -/
noncomputable def gaussBinom : ℕ → ℕ → PowerSeries ℤ
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => gaussBinom n k + X ^ (k + 1) * gaussBinom n (k + 1)

@[simp] lemma gaussBinom_zero_right (n : ℕ) : gaussBinom n 0 = 1 := by cases n <;> rfl
@[simp] lemma gaussBinom_zero_succ (k : ℕ) : gaussBinom 0 (k + 1) = 0 := rfl

/-- q-Pascal recurrence. -/
lemma gaussBinom_succ_succ (n k : ℕ) :
    gaussBinom (n + 1) (k + 1) = gaussBinom n k + X ^ (k + 1) * gaussBinom n (k + 1) := rfl

/-- diagonal vanishing: `[n,k]_q = 0` whenever `n < k`. -/
lemma gaussBinom_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → gaussBinom n k = 0 := by
  intro n
  induction n with
  | zero => intro k h; cases k with | zero => exact absurd h (by omega) | succ _ => rfl
  | succ m ih =>
      intro k h
      cases k with
      | zero => exact absurd h (by omega)
      | succ k =>
          rw [gaussBinom_succ_succ, ih (show m < k by omega), ih (show m < k + 1 by omega),
              mul_zero, add_zero]

@[simp] lemma gaussBinom_self (n : ℕ) : gaussBinom n n = 1 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [gaussBinom_succ_succ, ih, gaussBinom_eq_zero_of_lt (Nat.lt_succ_self m),
                     mul_zero, add_zero]

end MockTheta5.Bailey
