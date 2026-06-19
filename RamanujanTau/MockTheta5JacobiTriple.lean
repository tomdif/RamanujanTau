/-
# Jacobi triple product campaign, Rung 1: infinite products via coefficient stabilization

The Jacobi triple product `∏_{n≥1}(1-q^{2n})(1+zq^{2n-1})(1+z⁻¹q^{2n-1}) = Σ_{n∈ℤ} zⁿ q^{n²}` is the bridge
from the q-Pochhammer / Bailey world (base-`q` formal power series) to the theta-function world, and the first
honest step on Hickerson's route toward the mock theta conjecture (the harmonic-Maass layer beyond it is a
separate, much larger undertaking — see `MockTheta5BaileyTier3`). It is itself a multi-rung campaign:

  Rung 1  [HERE]  infinite products via coefficient stabilization — the `(q;q)_∞` object.
  Rung 2          bilateral sums `Σ_{n∈ℤ}` + a Laurent setup for the `z` variable.
  Rung 3          the finite (one-sided) JTP — essentially `qbinom` (the q-binomial theorem) in base `q²`.
  Rung 4          the limit: finite → the full infinite bilateral JTP.

This file is Rung 1. An infinite product `∏_{n≥1}(1-qⁿ)` is a genuine formal power series even though it has
infinitely many factors, because the factor `(1-qⁿ)` only affects coefficients of degree `≥ n`: so the `q^k`
coefficient is the SAME for every finite truncation `(q;q)_N` with `N > k`. This is the product analogue of
the summable-family idiom (`MockTheta5Lemmas`) used for the mock theta functions. No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyChain
import RamanujanTau.MockTheta5Lemmas

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- The `q^k` coefficient of the finite product `(q;q)_N = ∏_{n=1}^N (1-qⁿ)` stabilizes once `N > k`:
the extra factors `(1-q^{N+1})…` only touch coefficients of degree `> k`. -/
lemma coeff_qfac_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N → coeff k (qfac N) = coeff k (qfac M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [qfac_succ, mul_sub, mul_one, map_sub]
        have hz : coeff k (qfac N * X ^ (N + 1)) = 0 := by
          rw [mul_comm]; exact MockTheta5.mt_coeff_Xpow_mul_zero (qfac N) (N + 1) k (by omega)
        rw [hz, sub_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`(q;q)_∞ = ∏_{n≥1}(1 - qⁿ)`** as a formal power series, defined by coefficient stabilization. -/
noncomputable def qfacInf : PowerSeries ℤ := mk fun k => coeff k (qfac (k + 1))

/-- The defining property: `coeff k (q;q)_∞` equals `coeff k` of any finite product `(q;q)_N`, `N ≥ k+1`.
So `(q;q)_∞` is the honest infinite product (no topology / `tprod` needed). -/
lemma coeff_qfacInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k qfacInf = coeff k (qfac N) := by
  rw [qfacInf, coeff_mk, coeff_qfac_stable (Nat.lt_succ_self k) hN]

@[simp] lemma coeff_zero_qfacInf : coeff 0 qfacInf = 1 := by
  rw [coeff_qfacInf (le_refl 1)]; simp [qfac, Finset.prod_range_one]

/-- `(q;q)_∞` is a unit (constant term 1), so `1/(q;q)_∞` — the partition generating function — is a
genuine formal power series. -/
lemma isUnit_qfacInf : IsUnit qfacInf := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_qfacInf]
  exact isUnit_one

/-- The partition generating function `1/(q;q)_∞ = Σ p(n) qⁿ` as a formal power series. -/
noncomputable def partitionGF : PowerSeries ℤ := Ring.inverse qfacInf

end MockTheta5.JTP
