/-
# Jacobi triple product campaign, Rung 4 steps L2–L4: the one-sided Cauchy/Euler identity

Building on L1 (`jtpProdInf`, the one-sided infinite product), this file proves the **one-sided Cauchy/Euler
identity** — the first genuinely-new q-series identity on the JTP route:

  **`oneSidedCauchy`:**  the `zᵏ`-coefficient of `∏_{i≥0}(1 + z q^{2i+1})` is `q^{k²} / (q²;q²)_k`.

Equivalently `∏_{i≥0}(1+z q^{2i+1}) = Σ_{k≥0} q^{k²} zᵏ / (q²;q²)_k`. It is obtained as the `n→∞` limit of
`finite_jtp`, where the only real content is **L2**, the limit `[n,k]_{q²} → 1/(q²;q²)_k`, proved purely by
q-degree coefficient stabilization (no analysis):

  L2a `gaussBinom_eq_rfac`  — `[N,k]_q = (q^{N-k+1};q)_k · (q;q)_k⁻¹` (isolates the `N`-dependence in `rfac`).
  L2b `E2_inverse_qfac`     — base change `E2 = (q↦q²)` commutes with `Ring.inverse` on the unit `(q;q)_k`.
      `coeff_rfac_low`, `coeff_E2`, `coeff_E2_rfac_low` — `rfac` / `E2(rfac)` are `≡ 1` in low q-degree.
  L2  `E2_gaussBinom_stable`— `[N,k]_{q²} = E2[N,k]_q` agrees with `1/(q²;q²)_k` up to q-degree `2(N-k+1)`.
  L4  `oneSidedCauchy`      — read off the `zᵏ`-coefficient of `jtpProdInf` via `coeff_jtpProdInf`+`finite_jtp`.

No `sorry`. (Remaining for the full bilateral JTP: L5 move to `ℤ[z;z⁻¹]`, L6 the `(q²;q²)_∞` prefactor, and the
hard L7 bilateralization; see `MockTheta5JacobiLimit`.)
-/
import RamanujanTau.MockTheta5JacobiLimit
import RamanujanTau.MockTheta5BaileyChain

namespace MockTheta5.Bailey
open PowerSeries

/-- L2a: `[N,k]_q = (q^{N-k+1};q)_k · (q;q)_k⁻¹` — the `N`-dependence sits entirely in `rfac (N-k) k`. -/
lemma gaussBinom_eq_rfac (N k : ℕ) (h : k ≤ N) :
    gaussBinom N k = rfac (N - k) k * Ring.inverse (qfac k) := by
  rw [gaussBinom_eq_inv N k h]
  have hq : qfac N = rfac (N - k) k * qfac (N - k) := by rw [rfac_mul_qfac]; congr 1; omega
  rw [hq, show rfac (N - k) k * qfac (N - k) * Ring.inverse (qfac k) * Ring.inverse (qfac (N - k))
        = rfac (N - k) k * Ring.inverse (qfac k) * (qfac (N - k) * Ring.inverse (qfac (N - k))) from by ring,
      Ring.mul_inverse_cancel (qfac (N - k)) (isUnit_qfac (N - k)), mul_one]

/-- L2b: the base change `E2 : q ↦ q²` commutes with `Ring.inverse` on the unit `(q;q)_k`. -/
lemma E2_inverse_qfac (k : ℕ) : E2 (Ring.inverse (qfac k)) = Ring.inverse (E2 (qfac k)) := by
  have hu : IsUnit (qfac k) := isUnit_qfac k
  have hu2 : IsUnit (E2 (qfac k)) := hu.map E2
  have h1 : E2 (qfac k) * E2 (Ring.inverse (qfac k)) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hu, map_one]
  calc E2 (Ring.inverse (qfac k))
      = Ring.inverse (E2 (qfac k)) * (E2 (qfac k) * E2 (Ring.inverse (qfac k))) := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hu2, one_mul]
    _ = Ring.inverse (E2 (qfac k)) := by rw [h1, mul_one]

/-- `(q^{s+1};q)_k ≡ 1` modulo q-degree `s+1` (each factor is). -/
lemma coeff_rfac_low (s k : ℕ) {m : ℕ} (h : m < s + 1) : coeff m (rfac s k) = coeff m 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rfac_succ, mul_sub, mul_one, map_sub, ih]
      have hz : coeff m (rfac s k * X ^ (s + k + 1)) = 0 := by
        rw [mul_comm]; exact MockTheta5.mt_coeff_Xpow_mul_zero (rfac s k) (s + k + 1) m (by omega)
      rw [hz, sub_zero]

/-- The base change doubles q-degrees: `coeff m (E2 f) = coeff (m/2) f` if `2 ∣ m`, else `0`. -/
lemma coeff_E2 (f : PowerSeries ℤ) (m : ℕ) :
    coeff m (E2 f) = if 2 ∣ m then coeff (m / 2) f else 0 := by
  have h0 : E2 f = PowerSeries.expand 2 (by norm_num) f := rfl
  rw [h0, PowerSeries.coeff_expand]

/-- `E2 (q^{s+1};q)_k ≡ 1` modulo q-degree `2(s+1)`. -/
lemma coeff_E2_rfac_low (s k : ℕ) {m : ℕ} (h : m < 2 * (s + 1)) : coeff m (E2 (rfac s k)) = coeff m 1 := by
  rw [coeff_E2]
  split_ifs with h2
  · rw [coeff_rfac_low s k (by omega), coeff_one, coeff_one]; split_ifs <;> omega
  · rw [coeff_one, if_neg (by omega)]

/-- **L2**: the Gaussian binomial limit. `[N,k]_{q²}` agrees with `1/(q²;q²)_k` up to q-degree `2(N-k+1)`;
i.e. `[N,k]_{q²} → 1/(q²;q²)_k` as `N → ∞`, purely by coefficient stabilization. -/
lemma E2_gaussBinom_stable (N k : ℕ) (hk : k ≤ N) {m : ℕ} (hm : m < 2 * (N - k + 1)) :
    coeff m (E2 (gaussBinom N k)) = coeff m (Ring.inverse (E2 (qfac k))) := by
  rw [gaussBinom_eq_rfac N k hk, map_mul, E2_inverse_qfac]
  have hdvd : (X : PowerSeries ℤ) ^ (2 * (N - k + 1)) ∣ (E2 (rfac (N - k) k) - 1) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m' hm'
    rw [map_sub, coeff_E2_rfac_low (N - k) k (by omega), sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have he : E2 (rfac (N - k) k) = 1 + X ^ (2 * (N - k + 1)) * g := by rw [← hg]; ring
  rw [he, add_mul, one_mul, map_add, mul_assoc,
      MockTheta5.mt_coeff_Xpow_mul_zero _ (2 * (N - k + 1)) m hm, add_zero]

/-- **L4 — the one-sided Cauchy/Euler identity.** The `zᵏ`-coefficient of the one-sided infinite product
`∏_{i≥0}(1 + z q^{2i+1})` is `q^{k²} / (q²;q²)_k`. Equivalently
`∏_{i≥0}(1+z q^{2i+1}) = Σ_{k≥0} q^{k²} zᵏ / (q²;q²)_k`. The `n→∞` limit of `finite_jtp`. -/
theorem oneSidedCauchy (k : ℕ) :
    PowerSeries.coeff k jtpProdInf = qq ^ (k ^ 2) * Ring.inverse (E2 (qfac k)) := by
  ext m
  rw [coeff_jtpProdInf k (show m < 2 * (m + k) + 1 by omega), jtpProd, finite_jtp,
      coeff_Csum (fun j => qq ^ (j ^ 2) * E2 (gaussBinom (m + k) j)) (m + k + 1) k, if_pos (by omega)]
  show coeff m (X ^ (k ^ 2) * E2 (gaussBinom (m + k) k))
      = coeff m (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)))
  rw [coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs with hkm
  · exact E2_gaussBinom_stable (m + k) k (by omega) (by omega)
  · rfl

end MockTheta5.Bailey
