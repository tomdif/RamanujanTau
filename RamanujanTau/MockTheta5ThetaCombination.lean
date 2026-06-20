/-
# Parity decomposition of the theta series — combining the `z = ±1` evaluations

The `z = 1` and `z = −1` specializations of the bilateral JTP (`gauss_theta`, `alternating_theta`)
have the same coefficient structure except for a `(−1)^{m+1}` sign on the `q^{(m+1)²}` term. Adding and
subtracting therefore split `Σ_{n∈ℤ} q^{n²}` by the **parity of `n`**:

  * `θ₃ + θ₄` keeps the **even** squares (`2 + 2(−1)^{m+1} = 0` when `m` is even),
  * `θ₃ − θ₄` keeps the **odd** squares (`2 − 2(−1)^{m+1} = 0` when `m` is odd),

with the clean algebraic form `θ₃ ± θ₄ = (q²;q²)_∞ · ((Σ q^{k²}/(q²;q²)_k)² ± (Σ (−1)ᵏ q^{k²}/(q²;q²)_k)²)`.
No `sorry`.
-/
import RamanujanTau.MockTheta5GaussTheta
import RamanujanTau.MockTheta5AltTheta

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- **algebraic combination** of the two theta evaluations: `θ₃ + θ₄` factors through the prefactor. -/
theorem map_ev1_add_evm1_bilateralTheta :
    PowerSeries.map ev1 bilateralTheta + PowerSeries.map evm1 bilateralTheta
      = qfac2Inf * ((PowerSeries.map ev1 SZ) ^ 2 + (PowerSeries.map evm1 SZ) ^ 2) := by
  rw [gauss_theta, alternating_theta, mul_add]

/-- the `θ₃ + θ₄` coefficient isolates **even** squares: the odd-root terms cancel
(`2 + 2(−1)^{m+1} = 0` when `m` is even). -/
lemma coeff_ev1_add_evm1 (k : ℕ) :
    coeff k (PowerSeries.map ev1 bilateralTheta) + coeff k (PowerSeries.map evm1 bilateralTheta)
      = (if k = 0 then 2 else 0)
        + ∑ m ∈ Finset.range (k + 1), (if k = (m + 1) ^ 2 then 2 + 2 * (-1) ^ (m + 1) else 0) := by
  rw [coeff_map_ev1_bilateralTheta, coeff_map_evm1_bilateralTheta, add_add_add_comm]
  congr 1
  · split_ifs <;> ring
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring

/-- the `θ₃ − θ₄` coefficient isolates **odd** squares: the even-root terms cancel
(`2 − 2(−1)^{m+1} = 0` when `m` is odd). -/
lemma coeff_ev1_sub_evm1 (k : ℕ) :
    coeff k (PowerSeries.map ev1 bilateralTheta) - coeff k (PowerSeries.map evm1 bilateralTheta)
      = ∑ m ∈ Finset.range (k + 1), (if k = (m + 1) ^ 2 then 2 - 2 * (-1) ^ (m + 1) else 0) := by
  rw [coeff_map_ev1_bilateralTheta, coeff_map_evm1_bilateralTheta,
      show ∀ a b c d : ℤ, (a + b) - (c + d) = (a - c) + (b - d) from fun a b c d => by ring,
      show (if k = 0 then (1:ℤ) else 0) - (if k = 0 then 1 else 0) = 0 by split_ifs <;> ring,
      zero_add, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring

end MockTheta5.JTP
