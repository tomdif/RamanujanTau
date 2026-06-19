/-
# Jacobi triple product campaign, R4: the Durfee rectangle identity in base Q = q²

Applies the base change `E2` (`q ↦ q²`) to the base-`q` Durfee rectangle (`durfee_rect_base`) to obtain the
`Q = q²` form that the bilateralization step L7 consumes:

  **`durfee_rect_base_Q`:**  `E2(Σ_{j≥0} q^{j(j+n)}/((q;q)_j(q;q)_{n+j})) = 1/(q²;q²)_∞`.

This completes the genuinely-new mathematical content of the entire Jacobi-triple-product development: the
Durfee rectangle identity, in both base `q` and base `q²`. What remains for the full JTP (`MockTheta5Jacobi*`)
is L5 (transport `oneSidedCauchy` to the `ℤ[z;z⁻¹]` coefficient ring + the `z⁻¹` mirror), the L7 z-coefficient
bookkeeping (Cauchy product → per-diagonal → this identity), and L8 (assemble against `bilateralTheta`) — all
ring-transport / coefficient plumbing, no new mathematics. No `sorry`.
-/
import RamanujanTau.MockTheta5DurfeeBase
import RamanujanTau.MockTheta5JacobiBilateralize

import RamanujanTau.MockTheta5JacobiBilateralize
namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

lemma E2_inverse_qfacInf : E2 (Ring.inverse qfacInf) = Ring.inverse (E2 qfacInf) := by
  have hu := isUnit_qfacInf
  have hu2 : IsUnit (E2 qfacInf) := hu.map E2
  have h1 : E2 qfacInf * E2 (Ring.inverse qfacInf) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hu, map_one]
  calc E2 (Ring.inverse qfacInf)
      = Ring.inverse (E2 qfacInf) * (E2 qfacInf * E2 (Ring.inverse qfacInf)) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu2, one_mul]
    _ = Ring.inverse (E2 qfacInf) := by rw [h1, mul_one]

/-- **The Durfee rectangle identity in base `Q = q²`** (the form consumed by JTP step L7):
`E2(Σ_{j≥0} q^{j(j+n)}/((q;q)_j(q;q)_{n+j})) = 1/(q²;q²)_∞`. -/
theorem durfee_rect_base_Q (n : ℕ) : E2 (rectInf n) = Ring.inverse qfac2Inf := by
  rw [durfee_rect_base n, E2_inverse_qfacInf, qfac2Inf]
