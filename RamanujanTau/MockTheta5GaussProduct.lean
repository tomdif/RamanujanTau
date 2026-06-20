/-
# Gauss theta in classical product form

`map ev1 SZ = (−q;q²)_∞`: the partial-theta sum `Σ_{k≥0} q^{k²}/(q²;q²)_k` equals the product
`∏_{n≥1}(1+q^{2n−1})` — the `z = 1` Cauchy/Euler identity, obtained as the `n → ∞` limit of `finite_jtp`
evaluated at `z = 1` (`negOddFac_eq_sum`) together with the limit `[n,k]_{q²} → 1/(q²;q²)_k`
(`E2_gaussBinom_stable`).

Substituting into `gauss_theta` upgrades it to the **classical product form**
`Σ_{n∈ℤ} q^{n²} = (q²;q²)_∞ · (−q;q²)_∞²`. No `sorry`.
-/
import RamanujanTau.MockTheta5OddPairing
import RamanujanTau.MockTheta5GaussTheta

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- `finite_jtp` at `z = 1`: `∏_{i<n}(1+q^{2i+1}) = Σ_{k≤n} q^{k²}·E2([n,k]_{q²})`. -/
lemma negOddFac_eq_sum (n : ℕ) :
    negOddFac n = ∑ k ∈ Finset.range (n + 1), X ^ (k ^ 2) * E2 (gaussBinom n k) := by
  have h := congrArg (Polynomial.eval (1 : PowerSeries ℤ)) (finite_jtp n)
  simp only [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, mul_one, one_pow] at h
  rw [negOddFac]; exact h

/-- each `q^{k²}·E2([2m+2,k]_{q²})` agrees with the Cauchy coefficient `szc m k` at q-degree `m`. -/
lemma coeff_term_eq_szc (m k : ℕ) :
    coeff m (X ^ (k ^ 2) * E2 (gaussBinom (2 * m + 2) k)) = szc m k := by
  rw [szc, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases hkm : k ^ 2 ≤ m
  · rw [if_pos hkm, if_pos hkm]
    have hkle : k ≤ m := le_trans (Nat.le_self_pow (by norm_num) k) hkm
    exact E2_gaussBinom_stable (2 * m + 2) k (by omega) (by omega)
  · rw [if_neg hkm, if_neg hkm]

/-- **`map ev1 SZ = (−q;q²)_∞`** — `Σ_{k≥0} q^{k²}/(q²;q²)_k = ∏(1+q^{2n−1})` (the `z=1` Cauchy/Euler sum
= product identity). -/
theorem map_ev1_SZ_eq : PowerSeries.map ev1 SZ = negOddPochInf := by
  ext m
  rw [coeff_map_ev1_SZ, coeff_negOddPochInf (show m + 1 ≤ 2 * m + 2 by omega), negOddFac_eq_sum,
      map_sum, Finset.sum_congr rfl (fun k _ => coeff_term_eq_szc m k)]
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega) (fun k _ hk => ?_)
  simp only [Finset.mem_range, not_lt] at hk
  exact szc_zero m k (by have hkk : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k; omega)

/-- **Gauss theta, classical product form: `Σ_{n∈ℤ} q^{n²} = (q²;q²)_∞ · (−q;q²)_∞²`.** -/
theorem gauss_theta_product :
    PowerSeries.map ev1 bilateralTheta = qfac2Inf * negOddPochInf ^ 2 := by
  rw [gauss_theta, map_ev1_SZ_eq]

end MockTheta5.JTP
