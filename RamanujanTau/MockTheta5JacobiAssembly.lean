/-
# Jacobi triple product campaign: final assembly (L5/L7/L8) — infrastructure

All of the *mathematical* content of the Jacobi triple product is proved (`MockTheta5DurfeeBase`,
`MockTheta5DurfeeQ`): the Durfee rectangle identity in both base `q` and base `q²`, and the one-sided
Cauchy/Euler identity (`MockTheta5JacobiCauchy`). What remains for the literal full JTP

  `∏_{n≥1}(1-q^{2n})(1+z q^{2n-1})(1+z⁻¹ q^{2n-1}) = Σ_{n∈ℤ} zⁿ q^{n²}  (= bilateralTheta)`

is Laurent-ring formalization infrastructure (no new mathematics):

  L5  transport `oneSidedCauchy` into `PowerSeries (ℤ[z;z⁻¹])` (the `z`-variable becomes the Laurent
      generator `T 1`), and the `z⁻¹` mirror — a coefficient transport between ambient rings.
  L7  the bilateralization: with `SZ = Σ_k q^{k²}zᵏ/(q²;q²)_k`, `SZ⁻ = Σ_j q^{j²}z⁻ʲ/(q²;q²)_j` in the Laurent
      ring, prove `qfac2InfL · SZ · SZ⁻ = bilateralTheta` by matching each `zⁿ`-coefficient: the diagonal
      Cauchy sum times `(q²;q²)_∞` is `q^{n²}` by `durfee_rect_base_Q`. (Needs the Laurent Cauchy product and
      `z`-degree coefficient extraction.)
  L8  identify the two one-sided sums with the products `∏(1+z q^{2n-1})`, `∏(1+z⁻¹ q^{2n-1})` (via L5 + a
      Laurent-ring infinite product), giving the full JTP.

This file holds the first assembly building block — the `(q²;q²)_∞` prefactor lifted into the Laurent
coefficient ring. No `sorry`.
-/
import RamanujanTau.MockTheta5DurfeeQ
import Mathlib.Algebra.Polynomial.Laurent

namespace MockTheta5.JTP
open PowerSeries

/-- The `(q²;q²)_∞` prefactor, lifted into `PowerSeries (ℤ[z;z⁻¹])` (the ambient ring of the bilateral JTP),
via the constant embedding `ℤ ↪ ℤ[z;z⁻¹]`. -/
noncomputable def qfac2InfL : PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.map (LaurentPolynomial.C) qfac2Inf

lemma constantCoeff_qfac2InfL : constantCoeff qfac2InfL = 1 := by
  rw [qfac2InfL, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply,
      show constantCoeff qfac2Inf = coeff 0 qfac2Inf from (coeff_zero_eq_constantCoeff_apply _).symm,
      coeff_zero_qfac2Inf]
  exact map_one _

lemma isUnit_qfac2InfL : IsUnit qfac2InfL := by
  rw [isUnit_iff_constantCoeff, constantCoeff_qfac2InfL]; exact isUnit_one

end MockTheta5.JTP
