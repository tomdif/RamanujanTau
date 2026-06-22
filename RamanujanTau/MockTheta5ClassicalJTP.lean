/-
# The classical (product-form) Jacobi triple product

The bilateral JTP was proved in `SZ·SZinv` sum form (`bilateral_jacobi_triple_product`). Here we upgrade
it to the **textbook product form**

  `(q²;q²)_∞ · ∏_{n≥1}(1+z q^{2n−1}) · ∏_{n≥1}(1+z⁻¹ q^{2n−1}) = Σ_{n∈ℤ} zⁿ q^{n²}`,

via the **master one-sided Cauchy identity** `SZ = ∏_{i≥0}(1+z q^{2i+1})` (`SZ_eq_jtpProdQInf`) — of which
the earlier `z = ±1, ±q` evaluations are all specializations.

The product `∏(1+z q^{2i+1})` is built in the `q`-outer ring `ℤ[z;z⁻¹]⟦q⟧` (coefficient stabilization).
The bridge is the **variable-swap ring hom** `Psi : (ℤ⟦q⟧)[z] → ℤ[z;z⁻¹]⟦q⟧` (`z ↦ T 1`, coeff `a ↦ map C a`),
which transports `finite_jtp` to the `q`-outer ring (`jtpProdQ_eq_sum`); the `n → ∞` limit (matching
`E2[n,k]_{q²} → 1/(q²;q²)_k`) is read off by the z-degree projection `zProj` and `zProj_ext`. No `sorry`.
-/
import RamanujanTau.MockTheta5GaussProduct

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the **variable-swap ring hom** `(ℤ⟦q⟧)[z] → ℤ[z;z⁻¹]⟦q⟧`: `z ↦ T 1`, coeff `a(q) ↦ map C a`. -/
noncomputable def Psi : Polynomial (PowerSeries ℤ) →+* PowerSeries (LaurentPolynomial ℤ) :=
  Polynomial.eval₂RingHom (PowerSeries.map (LaurentPolynomial.C)) (PowerSeries.C (LaurentPolynomial.T 1))

@[simp] lemma Psi_C (a : PowerSeries ℤ) :
    Psi (Polynomial.C a) = PowerSeries.map (LaurentPolynomial.C) a := by
  rw [Psi, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

@[simp] lemma Psi_X : Psi Polynomial.X = PowerSeries.C (LaurentPolynomial.T 1) := by
  rw [Psi, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

lemma T_one_pow (k : ℕ) :
    (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) ^ k = LaurentPolynomial.T (k : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← LaurentPolynomial.T_add]; norm_num

/-- the finite one-sided product `∏_{i<n}(1 + z q^{2i+1})` in the `q`-outer ring. -/
noncomputable def jtpProdQ (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 + X ^ (2 * i + 1) * PowerSeries.C (LaurentPolynomial.T 1))

/-- transport `finite_jtp` to the `q`-outer ring: `∏(1+z q^{2i+1}) = Σ_{k≤n} q^{k²} E2([n,k]_{q²}) zᵏ`. -/
lemma jtpProdQ_eq_sum (n : ℕ) :
    jtpProdQ n = ∑ k ∈ Finset.range (n + 1),
      X ^ (k ^ 2) * PowerSeries.map (LaurentPolynomial.C) (E2 (gaussBinom n k))
        * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
  have h := congrArg Psi (finite_jtp n)
  rw [map_prod, map_sum] at h
  rw [jtpProdQ,
      show (∏ i ∈ Finset.range n,
              (1 + X ^ (2 * i + 1) * PowerSeries.C (LaurentPolynomial.T 1) :
                PowerSeries (LaurentPolynomial ℤ)))
        = ∏ i ∈ Finset.range n, Psi (1 + Polynomial.C (qq ^ (2 * i + 1)) * Polynomial.X) from
        Finset.prod_congr rfl (fun i _ => by
          rw [map_add, map_one, map_mul, Psi_C, Psi_X, qq, map_pow, PowerSeries.map_X]), h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, Psi_C, map_mul, map_pow, qq, map_pow, PowerSeries.map_X, Psi_X, ← map_pow, T_one_pow,
      mul_assoc]

lemma jtpProdQ_succ (n : ℕ) :
    jtpProdQ (n + 1) = jtpProdQ n * (1 + X ^ (2 * n + 1) * PowerSeries.C (LaurentPolynomial.T 1)) := by
  rw [jtpProdQ, jtpProdQ, Finset.prod_range_succ]

lemma coeff_jtpProdQ_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (jtpProdQ N) = coeff k (jtpProdQ M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [jtpProdQ_succ, mul_add, mul_one, map_add]
        have hz : coeff k (jtpProdQ N * (X ^ (2 * N + 1) * PowerSeries.C (LaurentPolynomial.T 1))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{n≥1}(1 + z q^{2n−1})`** as a formal power series (the one-sided Jacobi product). -/
noncomputable def jtpProdQInf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (jtpProdQ (k + 1))

lemma coeff_jtpProdQInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k jtpProdQInf = coeff k (jtpProdQ N) := by
  rw [jtpProdQInf, coeff_mk, coeff_jtpProdQ_stable (Nat.lt_succ_self k) hN]

/-! ### z-degree projection of the product, and the limit to `SZ` -/

lemma zProj_mapC_CT (a : PowerSeries ℤ) (k : ℕ) (κ : ℤ) :
    zProj κ (PowerSeries.map (LaurentPolynomial.C) a * PowerSeries.C (LaurentPolynomial.T (k : ℤ)))
      = if (k : ℤ) = κ then a else 0 := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul_C, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]
  split_ifs with h <;> simp

lemma zProj_jtpProdQ_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ (k ^ 2) * PowerSeries.map (LaurentPolynomial.C) (E2 (gaussBinom n k))
      * PowerSeries.C (LaurentPolynomial.T (k : ℤ)))
      = if (k : ℤ) = κ then X ^ (k ^ 2) * E2 (gaussBinom n k) else 0 := by
  rw [show X ^ (k ^ 2) * PowerSeries.map (LaurentPolynomial.C) (E2 (gaussBinom n k))
        = PowerSeries.map (LaurentPolynomial.C) (X ^ (k ^ 2) * E2 (gaussBinom n k)) from by
      rw [map_mul, map_pow, PowerSeries.map_X], zProj_mapC_CT]

lemma zProj_jtpProdQ (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (jtpProdQ M) = X ^ (k ^ 2) * E2 (gaussBinom M k) := by
  rw [jtpProdQ_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_jtpProdQ_term, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_jtpProdQ_term, if_pos rfl]

lemma coeff_X_E2gauss_stable (m k : ℕ) :
    coeff m (X ^ (k ^ 2) * E2 (gaussBinom (m + k + 1) k))
      = coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  by_cases hkm : k ^ 2 ≤ m
  · rw [if_pos hkm, if_pos hkm]; exact E2_gaussBinom_stable (m + k + 1) k (by omega) (by omega)
  · rw [if_neg hkm, if_neg hkm]

lemma zProj_jtpProdQInf (k : ℕ) :
    zProj (k : ℤ) jtpProdQInf = X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_jtpProdQInf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_jtpProdQ k (m + k + 1) (by omega), coeff_X_E2gauss_stable]

lemma zProj_jtpProdQ_neg {κ : ℤ} (hκ : κ < 0) : zProj κ jtpProdQInf = 0 := by
  ext m
  rw [coeff_zProj, coeff_jtpProdQInf (le_refl (m + 1)), ← coeff_zProj, jtpProdQ_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_jtpProdQ_term, if_neg (by omega)])]

lemma zProj_SZ_neg {κ : ℤ} (hκ : κ < 0) : zProj κ SZ = 0 := by
  ext m
  rw [coeff_zProj, coeff_SZ (le_refl (m + 1)), ← coeff_zProj, SZfinite, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_SZterm, if_neg (by omega)])]

/-- **the one-sided Jacobi/Cauchy identity**: `Σ_{k≥0} q^{k²}zᵏ/(q²;q²)_k = ∏_{i≥0}(1+z q^{2i+1})`.
The master identity of which the `z = ±1, ±q` evaluations are specializations. -/
theorem SZ_eq_jtpProdQInf : SZ = jtpProdQInf := by
  refine zProj_ext (fun κ => ?_)
  by_cases hκ : 0 ≤ κ
  · lift κ to ℕ using hκ with k; rw [zProj_SZ, zProj_jtpProdQInf]
  · rw [not_le] at hκ; rw [zProj_SZ_neg hκ, zProj_jtpProdQ_neg hκ]

/-- **The classical (product-form) bilateral Jacobi triple product**:
`(q²;q²)_∞ · ∏(1+z q^{2n−1}) · ∏(1+z⁻¹ q^{2n−1}) = Σ_{n∈ℤ} zⁿ q^{n²}`. -/
theorem classical_jacobi_triple_product :
    qfac2InfL * jtpProdQInf * PowerSeries.map invertHom jtpProdQInf = bilateralTheta := by
  rw [← SZ_eq_jtpProdQInf, map_invert_SZ]; exact bilateral_jacobi_triple_product

end MockTheta5.JTP
