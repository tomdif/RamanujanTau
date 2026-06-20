/-
# Jacobi triple product campaign: the one-sided Cauchy sum in the Laurent ring (JTP L7 factor)

`SZ = Σ_{k≥0} (q^{k²}/(q²;q²)_k)·zᵏ` as an element of `PowerSeries (ℤ[z;z⁻¹])` (`z = T 1`), built by coefficient
stabilization (`SZterm k` has q-degree `≥ k²`). This is one of the two one-sided factors of the Jacobi triple
product's bilateralization (the other, `SZ⁻¹`, is the `z ↦ z⁻¹` mirror). Together with the lifted prefactor
`qfac2InfL`, the bilateralization step L7 is `qfac2InfL · SZ · SZ⁻¹ = bilateralTheta`, whose `zⁿ`-coefficient
collapses to `durfee_rect_base_Q`. No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiAssembly

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

noncomputable def cauchyCoef (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)))

noncomputable def SZterm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  cauchyCoef k * PowerSeries.C (LaurentPolynomial.T (k : ℤ))

lemma SZterm_coeff_zero {k m : ℕ} (h : m < k ^ 2) : coeff m (SZterm k) = 0 := by
  rw [SZterm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map,
      show coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (k ^ 2) m h, map_zero, zero_mul]

noncomputable def SZfinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, SZterm k

noncomputable def SZ : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (SZfinite (m + 1))

lemma coeff_SZ_stable {m : ℕ} : ∀ {M N : ℕ}, m < M → M ≤ N → coeff m (SZfinite N) = coeff m (SZfinite M) := by
  intro M N hm hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : SZfinite (N + 1) = SZfinite N + SZterm N := by
          rw [SZfinite, SZfinite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            SZterm_coeff_zero (show m < N ^ 2 by have hN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N; omega),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_SZ {m M : ℕ} (hM : m + 1 ≤ M) : coeff m SZ = coeff m (SZfinite M) := by
  rw [SZ, coeff_mk, coeff_SZ_stable (Nat.lt_succ_self m) hM]

/-! ## The `z⁻¹` mirror sum `SZinv = Σ_{k≥0} (q^{k²}/(q²;q²)_k)·z^{-k}` (the other JTP factor) -/

/-- the `z^{-k}`-term of the mirror Cauchy sum. -/
noncomputable def SZinvTerm (k : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  cauchyCoef k * PowerSeries.C (LaurentPolynomial.T (-(k : ℤ)))

lemma SZinvTerm_coeff_zero {k m : ℕ} (h : m < k ^ 2) : coeff m (SZinvTerm k) = 0 := by
  rw [SZinvTerm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map,
      show coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) = 0 from
        MockTheta5.mt_coeff_Xpow_mul_zero _ (k ^ 2) m h, map_zero, zero_mul]

noncomputable def SZinvFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) := ∑ k ∈ Finset.range M, SZinvTerm k

/-- **The mirror one-sided Cauchy sum** `Σ_{k≥0} (q^{k²}/(q²;q²)_k)·z^{-k}` (the `z ↦ z⁻¹` image of `SZ`).
Together with `SZ` and the prefactor `qfac2InfL`, the JTP bilateralization (L8) is
`qfac2InfL · SZ · SZinv = bilateralTheta`, whose `zⁿ`-coefficient collapses to `durfee_rect_base_Q`. -/
noncomputable def SZinv : PowerSeries (LaurentPolynomial ℤ) := mk fun m => coeff m (SZinvFinite (m + 1))

lemma coeff_SZinv_stable {m : ℕ} : ∀ {M N : ℕ}, m < M → M ≤ N →
    coeff m (SZinvFinite N) = coeff m (SZinvFinite M) := by
  intro M N hm hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : SZinvFinite (N + 1) = SZinvFinite N + SZinvTerm N := by
          rw [SZinvFinite, SZinvFinite, Finset.sum_range_succ]
        rw [hsucc, map_add,
            SZinvTerm_coeff_zero (show m < N ^ 2 by have hN : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N; omega),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_SZinv {m M : ℕ} (hM : m + 1 ≤ M) : coeff m SZinv = coeff m (SZinvFinite M) := by
  rw [SZinv, coeff_mk, coeff_SZinv_stable (Nat.lt_succ_self m) hM]
