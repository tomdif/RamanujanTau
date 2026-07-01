/-
# The master one-sided Euler / Cauchy identity (base `q`)

`∏_{i≥0}(1 + t qⁱ) = Σ_{k≥0} q^{k(k-1)/2} tᵏ / (q;q)_k`   (`euler_cauchy`),

the `n→∞` limit of the finite q-binomial theorem `qbinom`, via the base-`q` Gaussian-binomial limit
`[N,k]_q → 1/(q;q)_k` (`gaussBinom_stable`). This is the master `t`-general, base-`q` form of which the repo's
base-`q²` `oneSidedCauchy` (`SZ = ∏(1+z q^{2i+1})`) and `t=1` `prodOnePlus = ∏(1+qⁿ)` are specializations.

## Why the famous *product* theta identities stop here
The pentagonal number theorem `(q;q)_∞ = Σ_{n∈ℤ}(−1)ⁿ q^{n(3n-1)/2}` and both Rogers–Ramanujan products
are all a *bilateral* theta `Σ_{n∈ℤ} zⁿ q^{f(n)}` evaluated at `z = ±q` or `−q²` (e.g. RR1's `α`-sum is the
triangular JTP at base `q⁵`, `z=−q²`). The bilateral form needs `z⁻¹`, so `z` must be a **unit** — but
`±q, −q²` are non-units in `PowerSeries ℤ`. That is exactly why the repo keeps `z` formal
(`classical_jacobi_triple_product` / `jtpProdQInf`) and only specializes at `z=±1` (units, giving the
Gauss-type `GaussTheta`/`AltTheta`). Unlocking the famous products needs a Laurent-series-in-`q` framework
(`ℤ((q))`) for the bilateral sum — a genuine infrastructure gap, not a missing lemma. No `sorry`.
-/
import RamanujanTau.MockTheta5QBinom
import RamanujanTau.MockTheta5BaileyChain
import RamanujanTau.MockTheta5JacobiCauchy
import RamanujanTau.MockTheta5BaileyTransform

namespace MockTheta5.Bailey
open PowerSeries

/-- `[N,k]_q = (q^{N-k+1};q)_k · (q;q)_k⁻¹`. -/
lemma gaussBinom_eq_rfac' (N k : ℕ) (hk : k ≤ N) :
    gaussBinom N k = rfac (N - k) k * Ring.inverse (qfac k) := by
  rw [gaussBinom_eq_inv N k hk, rfac_eq_inv, show (N - k) + k = N from by omega]
  ring

/-- **Base-`q` Gaussian binomial limit**: `[N,k]_q → 1/(q;q)_k`, agreeing up to q-degree `N-k+1`. -/
lemma gaussBinom_stable (N k : ℕ) (hk : k ≤ N) {m : ℕ} (hm : m < N - k + 1) :
    coeff m (gaussBinom N k) = coeff m (Ring.inverse (qfac k)) := by
  rw [gaussBinom_eq_rfac' N k hk]
  have hdvd : (X : PowerSeries ℤ) ^ (N - k + 1) ∣ (rfac (N - k) k - 1) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m' hm'
    rw [map_sub, coeff_rfac_low (N - k) k (by omega), sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have he : rfac (N - k) k = 1 + X ^ (N - k + 1) * g := by rw [← hg]; ring
  rw [he, add_mul, one_mul, map_add, mul_assoc,
      MockTheta5.mt_coeff_Xpow_mul_zero _ (N - k + 1) m hm, add_zero]

/-- **The one-sided Euler / Cauchy identity** (base `q`, general `t`):
`∏_{i≥0}(1 + t qⁱ) = Σ_{k≥0} q^{k(k-1)/2} tᵏ / (q;q)_k`. Stated as coefficient stabilization: the `qᵐ`
coefficient of the `tᵏ` coefficient of the finite product `∏_{i<N}(1+t qⁱ)` (= `qprod N`) agrees with that
of `q^{C(k,2)}/(q;q)_k` once `m < N-k+1`. The `n→∞` limit of the finite q-binomial theorem `qbinom`; the
master form of which the base-`q²` `oneSidedCauchy` (`SZ`) and `t=1` `prodOnePlus` are specializations. -/
theorem euler_cauchy (k : ℕ) {N : ℕ} (hkN : k ≤ N) {m : ℕ} (hm : m < N - k + 1) :
    coeff m (Polynomial.coeff (qprod N) k) = coeff m (qq ^ (k.choose 2) * Ring.inverse (qfac k)) := by
  have hdvd : (X : PowerSeries ℤ) ^ (N - k + 1) ∣ (gaussBinom N k - Ring.inverse (qfac k)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m' hm'
    rw [map_sub, gaussBinom_stable N k hkN hm', sub_self]
  rw [qbinom, qbRHS, coeff_Csum (fun j => qcoeff N j) (N + 1) k, if_pos (by omega), qcoeff]
  exact MockTheta5.JTP.coeff_mul_congr_right (f := qq ^ (k.choose 2))
    ((pow_dvd_pow X (show m + 1 ≤ N - k + 1 by omega)).trans hdvd)

end MockTheta5.Bailey
