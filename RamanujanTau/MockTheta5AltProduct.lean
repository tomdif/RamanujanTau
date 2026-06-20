/-
# Alternating theta in classical product form

`map evm1 SZ = (q;q²)_∞`: the signed partial theta `Σ_{k≥0} (−1)ᵏ q^{k²}/(q²;q²)_k` equals the product
`∏_{n≥1}(1−q^{2n−1})` — the `z = −1` Cauchy/Euler identity, from `finite_jtp` evaluated at `z = −1`.

Substituting into `alternating_theta` gives the **classical product form**
`Σ_{n∈ℤ} (−1)ⁿ q^{n²} = (q²;q²)_∞ · (q;q²)_∞²`. The `z = −1` twin of `gauss_theta_product`. No `sorry`.
-/
import RamanujanTau.MockTheta5GaussProduct
import RamanujanTau.MockTheta5AltTheta

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- pull the constant sign `(−1)^k` out of a coefficient (`coeff` is `ℤ`-linear). -/
lemma coeff_neg_pow_mul {m : ℕ} (k : ℕ) (g : PowerSeries ℤ) :
    coeff m ((-1) ^ k * g) = (-1) ^ k * coeff m g := by
  rw [show ((-1 : PowerSeries ℤ) ^ k) = PowerSeries.C ((-1 : ℤ) ^ k) by rw [map_pow]; simp,
      PowerSeries.coeff_C_mul]

/-- `finite_jtp` at `z = −1`: `∏_{i<n}(1−q^{2i+1}) = Σ_{k≤n} (−1)ᵏ q^{k²}·E2([n,k]_{q²})`. -/
lemma oddFac_eq_sum (n : ℕ) :
    oddFac n = ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (X ^ (k ^ 2) * E2 (gaussBinom n k)) := by
  have h := congrArg (Polynomial.eval (-1 : PowerSeries ℤ)) (finite_jtp n)
  simp only [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  rw [oddFac, show (∏ k ∈ Finset.range n, (1 - X ^ (2 * k + 1) : PowerSeries ℤ))
        = ∏ x ∈ Finset.range n, (1 + X ^ (2 * x + 1) * -1) from
      Finset.prod_congr rfl (fun i _ => by ring), h]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **`map evm1 SZ = (q;q²)_∞`** — `Σ_{k≥0} (−1)ᵏ q^{k²}/(q²;q²)_k = ∏(1−q^{2n−1})` (the `z=−1`
Cauchy/Euler sum = product identity). -/
theorem map_evm1_SZ_eq : PowerSeries.map evm1 SZ = oddPochInf := by
  ext m
  rw [coeff_map_evm1_SZ, coeff_oddPochInf (show m + 1 ≤ 2 * m + 2 by omega), oddFac_eq_sum, map_sum,
      Finset.sum_congr rfl (fun k _ => by rw [coeff_neg_pow_mul, coeff_term_eq_szc m k]
        : ∀ k ∈ Finset.range (2 * m + 2 + 1),
          coeff m ((-1) ^ k * (X ^ (k ^ 2) * E2 (gaussBinom (2 * m + 2) k))) = (-1) ^ k * szc m k)]
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega) (fun k _ hk => ?_)
  simp only [Finset.mem_range, not_lt] at hk
  rw [szc_zero m k (by have hkk : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k; omega), mul_zero]

/-- **Alternating theta, classical product form: `Σ(−1)ⁿq^{n²} = (q²;q²)_∞ · (q;q²)_∞²`.** -/
theorem alternating_theta_product :
    PowerSeries.map evm1 bilateralTheta = qfac2Inf * oddPochInf ^ 2 := by
  rw [alternating_theta, map_evm1_SZ_eq]

end MockTheta5.JTP
