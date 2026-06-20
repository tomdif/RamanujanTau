/-
# JTP step L8 (foundation): the z-degree projection

Finishing the bilateral Jacobi triple product needs `qfac2InfL · SZ · SZinv = bilateralTheta`, in
`PowerSeries (ℤ[z;z⁻¹])`. The plan (worked out, reduces cleanly to the PROVED `durfee_rect_base_Q`):

  * `zProj n φ` extracts the `T^n` (z-degree `n`) coefficient of `φ` at every q-degree, giving a `ℤ⟦q⟧`.
  * `qfac2InfL = map C qfac2Inf` is z-degree-0, so `zProj n (qfac2InfL · X) = qfac2Inf · zProj n X`.
  * `zProj k SZ = q^{k²}/(q²;q²)_k` for `k ≥ 0` (else 0); `zProj (-j) SZinv = q^{j²}/(q²;q²)_j` (else 0).
  * the **z-convolution law** `zProj n (A·B) = Σ_{s+t=n} zProj s A · zProj t B` then gives
    `zProj n (qfac2InfL·SZ·SZinv) = qfac2Inf · Σ_{k-j=n} q^{k²+j²}/((q²;q²)_k(q²;q²)_j) = q^{n²}`
    by `durfee_rect_base_Q` (the diagonal collapse), matching `zProj n bilateralTheta = q^{n²}`.
  * a "z-projections determine the element" lemma concludes `qfac2InfL·SZ·SZinv = bilateralTheta`.

This file is the foundation: `zProj` and its additivity. **Honest status:** the z-convolution law is the genuine
remaining crux — it is `AddMonoidAlgebra`/`Finsupp` convolution over the additive group `ℤ` (`LaurentPolynomial ℤ
= ℤ →₀ ℤ`), a real Mathlib-API build with finite-support double-sum reindexing, NOT light plumbing. The
*mathematics* of L8 is finished (it reduces to the proved `durfee_rect_base_Q`); what remains is that convolution
machinery. No `sorry`.
-/
import RamanujanTau.MockTheta5CauchySum

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- **z-degree-`n` projection**: extract the `T^n` (Laurent / z-degree) coefficient at each q-degree,
yielding a formal power series in `q` alone. The tool for matching the JTP bilateralization z-degree by
z-degree against `durfee_rect_base_Q`. -/
noncomputable def zProj (n : ℤ) (φ : PowerSeries (LaurentPolynomial ℤ)) : PowerSeries ℤ :=
  mk fun m => (coeff m φ) n

@[simp] lemma coeff_zProj (n : ℤ) (φ : PowerSeries (LaurentPolynomial ℤ)) (m : ℕ) :
    coeff m (zProj n φ) = (coeff m φ) n := by rw [zProj, coeff_mk]

/-- `zProj n` is additive (it is a coefficient-extraction, a linear map). -/
lemma zProj_add (n : ℤ) (a b : PowerSeries (LaurentPolynomial ℤ)) :
    zProj n (a + b) = zProj n a + zProj n b := by ext m; simp [map_add]

lemma zProj_zero (n : ℤ) : zProj n (0 : PowerSeries (LaurentPolynomial ℤ)) = 0 := by
  ext m; simp only [coeff_zProj, map_zero]; exact Finsupp.zero_apply

/-- `zProj n` commutes with finite sums (it is an additive coefficient-extraction). -/
lemma zProj_sum (n : ℤ) (s : Finset ℕ) (f : ℕ → PowerSeries (LaurentPolynomial ℤ)) :
    zProj n (∑ i ∈ s, f i) = ∑ i ∈ s, zProj n (f i) := by
  induction s using Finset.induction_on with
  | empty => exact zProj_zero n
  | @insert a s h ih => rw [Finset.sum_insert h, Finset.sum_insert h, zProj_add, ih]

/-! ### Projections of the two one-sided Cauchy sums

The `T^n`-coefficient of each Cauchy term is read off by `single_eq_C_mul_T → single_apply`
(sidestepping the `LaurentPolynomial.C` coercion), and `zProj` is then pushed through the defining
finite sum by `zProj_sum`. The upshot: the `z`-degree-`k` slice of `SZ` (and the `z^{-k}` slice of
`SZinv`) is exactly the `k`-th Cauchy coefficient `q^{k²}/(q²;q²)_k`. -/
section Projections
open MockTheta5.Bailey

/-- the `T^n` coefficient of `SZterm k` at q-degree `m`. -/
lemma SZterm_apply (k m : ℕ) (n : ℤ) :
    (coeff m (SZterm k)) n = if (k : ℤ) = n then coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) else 0 := by
  rw [SZterm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]

lemma zProj_SZterm (k : ℕ) (n : ℤ) :
    zProj n (SZterm k) = if (k : ℤ) = n then X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) else 0 := by
  ext m; rw [coeff_zProj, SZterm_apply]; split_ifs with h <;> simp

lemma zProj_SZfinite (k M : ℕ) (h : k < M) :
    zProj (k : ℤ) (SZfinite M) = X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) := by
  rw [SZfinite, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_SZterm, if_neg (by exact_mod_cast hik)])
        (fun hk => absurd (Finset.mem_range.mpr h) hk),
      zProj_SZterm, if_pos rfl]

/-- **z-degree-`k` projection of `SZ`** = the `k`-th Cauchy coefficient `q^{k²}/(q²;q²)_k`. -/
lemma zProj_SZ (k : ℕ) : zProj (k : ℤ) SZ = X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_SZ (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_SZfinite k (m + k + 1) (by omega)]

lemma SZinvTerm_apply (k m : ℕ) (n : ℤ) :
    (coeff m (SZinvTerm k)) n =
      if (-(k : ℤ)) = n then coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) else 0 := by
  rw [SZinvTerm, PowerSeries.coeff_mul_C, cauchyCoef, PowerSeries.coeff_map,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]

lemma zProj_SZinvTerm (k : ℕ) (n : ℤ) :
    zProj n (SZinvTerm k) = if (-(k : ℤ)) = n then X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) else 0 := by
  ext m; rw [coeff_zProj, SZinvTerm_apply]; split_ifs with h <;> simp

lemma zProj_SZinvFinite (k M : ℕ) (h : k < M) :
    zProj (-(k : ℤ)) (SZinvFinite M) = X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) := by
  rw [SZinvFinite, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_SZinvTerm, if_neg (by simpa only [neg_inj, Nat.cast_inj] using hik)])
        (fun hk => absurd (Finset.mem_range.mpr h) hk),
      zProj_SZinvTerm, if_pos rfl]

/-- **z-degree-`(-k)` projection of `SZinv`** = `q^{k²}/(q²;q²)_k` (the mirror of `zProj_SZ`). -/
lemma zProj_SZinv (k : ℕ) : zProj (-(k : ℤ)) SZinv = X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) := by
  ext m
  rw [coeff_zProj, coeff_SZinv (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_SZinvFinite k (m + k + 1) (by omega)]

end Projections

/-! ### The z-degree-0 prefactor law

`qfac2InfL = map C (q²;q²)_∞` lives entirely in z-degree 0, so it commutes out of any z-projection
as the scalar power series `(q²;q²)_∞`. This is the easy half of the Cauchy product (one factor is a
z-scalar); the genuine z-Cauchy product `SZ · SZinv` is handled separately. -/
section Prefactor
open MockTheta5.Bailey

/-- finset-sum of `LaurentPolynomial`s, applied at a z-degree (through the `def`-opacity via `show`). -/
lemma laurentSum_apply {ι : Type*} (s : Finset ι) (f : ι → LaurentPolynomial ℤ) (a : ℤ) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, (f i) a := by
  show (∑ i ∈ s, f i : ℤ →₀ ℤ) a = _
  rw [Finsupp.finsetSum_apply]

/-- `(C a · g)` applied at a z-degree: the constant scales the coefficient. -/
lemma C_mul_apply (a : ℤ) (g : LaurentPolynomial ℤ) (n : ℤ) :
    (LaurentPolynomial.C a * g) n = a * g n := by
  rw [← LaurentPolynomial.single_eq_C]; exact AddMonoidAlgebra.single_zero_mul_apply g a n

/-- **prefactor law**: `qfac2InfL` is z-degree-0, so it factors out of any z-projection. -/
lemma zProj_qfac2InfL_mul (n : ℤ) (Y : PowerSeries (LaurentPolynomial ℤ)) :
    zProj n (qfac2InfL * Y) = qfac2Inf * zProj n Y := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [qfac2InfL, PowerSeries.coeff_map, C_mul_apply, coeff_zProj]

end Prefactor

end MockTheta5.JTP
