/-
# Jacobi triple product campaign, toward L7: inverse stabilization (the limit lynchpin)

To pass from the finite Durfee rectangle `inner_inv_gen` to the infinite one (and thence to the Durfee
rectangle identity = JTP step L7), the `m → ∞` limit must move `(q;q)_{m-j}⁻¹`, `(q;q)_m⁻¹`, `(q;q)_{n+m}⁻¹`
to `(q;q)_∞⁻¹`. That is the content of:

  **`inv_qfac_stable`:** `coeff k ((q;q)_N⁻¹) = coeff k ((q;q)_∞⁻¹)` for `N ≥ k+1`.

It is proved with no strong induction: `a⁻¹ - b⁻¹ = a⁻¹(b-a)b⁻¹`, and `(q;q)_∞ - (q;q)_N` is divisible by
`X^{k+1}` (their coefficients agree up to degree `k`, `coeff_qfacInf`), so the difference of inverses vanishes
in degree `≤ k` (`mt_coeff_Xpow_mul_zero`).

**Status of L7.** The two genuinely-hard pieces are now both proved and committed, axiom-clean:
  * `inner_inv_gen` — the finite Durfee rectangle (general `n`), free from `F_eq_one`.
  * `inv_qfac_stable` — inverse stabilization (this file).

What remains is **mechanical coefficient bookkeeping**, no new ideas:
  R1  product-truncation: `coeff k (f·g)` depends only on `coeff ≤ k` of `f, g`; so in `coeff k` of an
      `inner_inv_gen` term (`m` large) one may replace `(q;q)_{m-j}⁻¹ → (q;q)_∞⁻¹` (via `inv_qfac_stable`),
      and likewise the RHS `(q;q)_m⁻¹(q;q)_{n+m}⁻¹ → (q;q)_∞⁻²`.
  R2  the `j`-sum truncates (`X^{j²+nj}` kills `j` with `j²+nj > k`), giving the infinite rectangle sum.
  R3  cancel one unit `(q;q)_∞` (`isUnit_qfacInf`, `mul_left_cancel₀`) to drop `(q;q)_∞⁻²` to `(q;q)_∞⁻¹`,
      yielding the base-`q` Durfee rectangle `Σ_{j≥0} q^{j(j+n)}(q;q)_j⁻¹(q;q)_{n+j}⁻¹ = (q;q)_∞⁻¹`.
  R4  apply `E2` (`q ↦ q²`, `E2_inverse_qfac`, `qfac2Inf`) → the Durfee rectangle identity = L7.
  L8  assemble L5 (Laurent transport) + L6 + L7 with `coeff_bilateralTheta` → the full Jacobi triple product.

No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiTriple
import RamanujanTau.MockTheta5DurfeeRect

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- **Inverse stabilization.** `coeff k` of `(q;q)_N⁻¹` agrees with that of `(q;q)_∞⁻¹` once `N ≥ k+1`.
The limit lynchpin for the Durfee rectangle. No induction: uses `a⁻¹-b⁻¹ = a⁻¹(b-a)b⁻¹` plus divisibility. -/
lemma inv_qfac_stable {k N : ℕ} (hN : k + 1 ≤ N) :
    coeff k (Ring.inverse (qfac N)) = coeff k (Ring.inverse qfacInf) := by
  have hu1 := isUnit_qfac N
  have hu2 := isUnit_qfacInf
  have hid : Ring.inverse (qfac N) - Ring.inverse qfacInf
      = Ring.inverse (qfac N) * (qfacInf - qfac N) * Ring.inverse qfacInf := by
    rw [mul_sub, sub_mul, mul_assoc (Ring.inverse (qfac N)) qfacInf,
        Ring.mul_inverse_cancel qfacInf hu2, mul_one,
        Ring.inverse_mul_cancel (qfac N) hu1, one_mul]
  have hdvd : (X : PowerSeries ℤ) ^ (k + 1) ∣ (qfacInf - qfac N) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro i hi
    rw [map_sub, coeff_qfacInf (show i + 1 ≤ N by omega), sub_self]
  obtain ⟨h, hh⟩ := hdvd
  have hz : coeff k (Ring.inverse (qfac N) - Ring.inverse qfacInf) = 0 := by
    rw [hid, hh,
        show Ring.inverse (qfac N) * (X ^ (k + 1) * h) * Ring.inverse qfacInf
          = X ^ (k + 1) * (Ring.inverse (qfac N) * h * Ring.inverse qfacInf) from by ring]
    exact MockTheta5.mt_coeff_Xpow_mul_zero _ (k + 1) k (by omega)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end MockTheta5.JTP
