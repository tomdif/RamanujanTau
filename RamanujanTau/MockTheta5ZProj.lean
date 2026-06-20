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

end MockTheta5.JTP
