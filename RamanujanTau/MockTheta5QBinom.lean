/-
# Bailey campaign, Tier-1 capstone: the q-binomial theorem (finite Cauchy / Rothe)

Goal: `∏_{i<n} (1 + qⁱ·t) = ∑_{k≤n} q^{C(k,2)}·[n,k]_q·tᵏ`, the finite q-binomial theorem, the bridge from the
Gaussian binomial `gaussBinom` (rung 1) to the product side that the Bailey machinery needs.

Worked over `Polynomial (PowerSeries ℤ)`: the outer indeterminate `X` is the bookkeeping variable `t`, and the
coefficients live in `PowerSeries ℤ` with `q := PowerSeries.X` (here `qq`). The clean proof route is the
**functional equation** `Pₙ₊₁(t) = (1+t)·Pₙ(q·t)` (substituting `t ↦ q·t` reproduces q-Pascal exactly when the
`tᵏ` coefficients are matched). This file builds that functional equation; the coefficient match (with the
triangular exponent `C(k,2)`) is the next rung on top of it.

No `sorry`.
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import RamanujanTau.MockTheta5Bailey

namespace MockTheta5.Bailey
open Polynomial

/-- `q := PowerSeries.X`, the coefficient-ring indeterminate (the outer `Polynomial.X` is the variable `t`). -/
noncomputable abbrev qq : PowerSeries ℤ := PowerSeries.X

/-- `Pₙ(t) = ∏_{i<n} (1 + qⁱ·t)`, in `Polynomial (PowerSeries ℤ)` (`X` is `t`). -/
noncomputable def qprod (n : ℕ) : Polynomial (PowerSeries ℤ) :=
  ∏ i ∈ Finset.range n, (1 + C (qq ^ i) * X)

/-- A single factor under the substitution `t ↦ q·t`: `(1 + qⁱ·t)|_{t↦q·t} = 1 + qⁱ⁺¹·t`. -/
lemma factor_comp (i : ℕ) :
    (1 + C (qq ^ i) * X).comp (C qq * X) = 1 + C (qq ^ (i + 1)) * X := by
  simp only [add_comp, mul_comp, C_comp, X_comp, one_comp, pow_succ, map_mul]
  ring

/-- `Pₙ(q·t) = ∏_{i<n} (1 + qⁱ⁺¹·t)` — the substitution shifts every exponent up by one. -/
lemma qprod_comp (n : ℕ) :
    (qprod n).comp (C qq * X) = ∏ i ∈ Finset.range n, (1 + C (qq ^ (i + 1)) * X) := by
  rw [qprod, prod_comp]
  exact Finset.prod_congr rfl (fun i _ => factor_comp i)

/-- **The functional equation** `Pₙ₊₁(t) = (1 + t)·Pₙ(q·t)`. -/
lemma qprod_succ (n : ℕ) :
    qprod (n + 1) = (1 + X) * (qprod n).comp (C qq * X) := by
  rw [qprod_comp, qprod, Finset.prod_range_succ']
  simp only [pow_zero, map_one, one_mul]
  ring

/-- The weighted coefficient `q^{C(k,2)}·[n,k]_q` (the coefficient of `tᵏ` in the q-binomial expansion).
We use `Nat.choose k 2` for the triangular exponent `C(k,2)=k(k-1)/2`; this gives the clean Pascal
relation `C(k+1,2)=C(k,2)+k` with no ℕ-division. -/
noncomputable def qcoeff (n k : ℕ) : PowerSeries ℤ := qq ^ (k.choose 2) * gaussBinom n k

/-- The right-hand side of the q-binomial theorem: `∑_{k≤n} q^{C(k,2)}·[n,k]_q·tᵏ`. -/
noncomputable def qbRHS (n : ℕ) : Polynomial (PowerSeries ℤ) :=
  ∑ k ∈ Finset.range (n + 1), C (qcoeff n k) * X ^ k

/-- Coefficient extraction for `∑_{k<m} C(f k)·tᵏ`: the `tʲ` coefficient is `f j` (if `j<m`, else 0). -/
lemma coeff_Csum (f : ℕ → PowerSeries ℤ) (m j : ℕ) :
    (∑ k ∈ Finset.range m, C (f k) * X ^ k).coeff j = if j < m then f j else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range m) j f]; simp [Finset.mem_range]

/-- A single term under `t ↦ q·t`: `(C a · tᵏ)|_{t↦q·t} = C (a·qᵏ)·tᵏ`. -/
lemma term_comp (a : PowerSeries ℤ) (k : ℕ) :
    (C a * X ^ k).comp (C qq * X) = C (a * qq ^ k) * X ^ k := by
  rw [mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow, C_mul]; ring

/-- Triangular Pascal: `C(k+1,2) = C(k,2) + k`. -/
lemma choose_two_succ (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right]; exact Nat.add_comm _ _

/-- `Pₙ(q·t) = ∑_{k≤n} q^{C(k,2)+k}·[n,k]_q·tᵏ` (the substitution multiplies the `tᵏ` weight by `qᵏ`). -/
lemma comp_qbRHS (n : ℕ) :
    (qbRHS n).comp (C qq * X) = ∑ k ∈ Finset.range (n + 1), C (qcoeff n k * qq ^ k) * X ^ k := by
  rw [qbRHS, sum_comp]
  exact Finset.sum_congr rfl (fun k _ => term_comp (qcoeff n k) k)

/-- q-Pascal at the level of the weighted coefficient: `qcoeff` satisfies the same recurrence the
q-binomial theorem needs — `qcoeff (n+1) (k+1) = qᵏ·qcoeff n k + qᵏ⁺¹·qcoeff n (k+1)`. -/
lemma qcoeff_succ_succ (n i : ℕ) :
    qcoeff (n + 1) (i + 1) = qq ^ i * qcoeff n i + qq ^ (i + 1) * qcoeff n (i + 1) := by
  simp only [qcoeff, choose_two_succ, gaussBinom_succ_succ, pow_add, pow_one]
  ring

@[simp] lemma qcoeff_zero_right (n : ℕ) : qcoeff n 0 = 1 := by simp [qcoeff]

lemma qcoeff_eq_zero_of_lt {n k : ℕ} (h : n < k) : qcoeff n k = 0 := by
  simp [qcoeff, gaussBinom_eq_zero_of_lt h]

/-- **The finite q-binomial theorem** (Rothe / finite Cauchy):
`∏_{i<n} (1 + qⁱ·t) = ∑_{k≤n} q^{C(k,2)}·[n,k]_q·tᵏ`, over `Polynomial (PowerSeries ℤ)` (`t = X`, `q = qq`).
Proved by induction via the functional equation `Pₙ₊₁(t) = (1+t)·Pₙ(q·t)` and coefficient matching
against the q-Pascal recurrence — the route that needs no multiplicative `(q;q)`-recurrence. No `sorry`. -/
theorem qbinom (n : ℕ) : qprod n = qbRHS n := by
  induction n with
  | zero => simp [qprod, qbRHS, qcoeff]
  | succ n ih =>
      rw [qprod_succ, ih, comp_qbRHS, add_mul, one_mul]
      refine Polynomial.ext fun j => ?_
      rw [coeff_add, coeff_Csum]
      rcases j with _ | i
      · rw [qbRHS, coeff_Csum]; simp
      · rw [coeff_X_mul, coeff_Csum, qbRHS, coeff_Csum, qcoeff_succ_succ]
        by_cases h1 : i < n
        · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]; ring
        · by_cases h2 : i = n
          · subst h2
            rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
                qcoeff_eq_zero_of_lt (Nat.lt_succ_self i)]
            ring
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring

end MockTheta5.Bailey
