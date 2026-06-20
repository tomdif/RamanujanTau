/-
# Distinct even/odd split: `∏(1+qⁿ) = (−q;q²)_∞ · (−q²;q²)_∞`

Splitting the distinct-part product `(−q;q)_∞ = ∏(1+qⁿ)` by parity of `n` into distinct **odd** parts
`(−q;q²)_∞ = ∏(1+q^{2n−1})` and distinct **even** parts `(−q²;q²)_∞ = ∏(1+q^{2n}) = E2(∏(1+qⁿ))`.

Index split `range(2m) = evens ⊔ odds` (`distinctSplit_eq`, by induction) lifted to infinite products by
coefficient stabilization — the `(1+·)` analogue of `qfac2Inf_mul_oddPochInf`. No `sorry`.
-/
import RamanujanTau.MockTheta5OddPairing

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- finite distinct even/odd split `∏_{j<2m}(1+q^{j+1}) = ∏(1+q^{2k+1})·∏(1+q^{2(k+1)})`. -/
lemma distinctSplit_eq (m : ℕ) : negOddFac m * E2 (qfacPos m) = qfacPos (2 * m) := by
  induction m with
  | zero => simp [qfacPos, negOddFac]
  | succ m ih =>
      have he2 : E2 (qfacPos (m + 1)) = E2 (qfacPos m) * (1 + X ^ (2 * (m + 1))) := by
        rw [qfacPos_succ, map_mul, map_add, map_one, map_pow, E2_X, ← pow_mul]
      rw [he2, negOddFac_succ, show 2 * (m + 1) = 2 * m + 1 + 1 from by ring,
          qfacPos_succ (2 * m + 1), qfacPos_succ (2 * m), ← ih]
      ring

/-- `(−q²;q²)_∞ = E2((−q;q)_∞)` agrees with the finite even product below degree `2M`. -/
lemma coeff_E2prodOnePlus_eq {i M : ℕ} (h : i + 1 ≤ M) :
    coeff i (E2 prodOnePlus) = coeff i (E2 (qfacPos M)) := by
  have hdvd : (X : PowerSeries ℤ) ^ M ∣ (prodOnePlus - qfacPos M) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro j hj
    rw [map_sub, coeff_prodOnePlus (show j + 1 ≤ M by omega), sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have hz : coeff i (E2 prodOnePlus) - coeff i (E2 (qfacPos M)) = 0 := by
    rw [← map_sub, ← map_sub, hg, map_mul, E2_X_pow]
    exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ i (by omega)
  exact sub_eq_zero.mp hz

/-- **`∏(1+qⁿ) = (−q;q²)_∞ · (−q²;q²)_∞`** — distinct parts = distinct odd × distinct even. -/
theorem prodOnePlus_split : prodOnePlus = negOddPochInf * E2 prodOnePlus := by
  ext N
  have h1 : coeff N (negOddPochInf * E2 prodOnePlus)
      = coeff N (negOddFac (N + 1) * E2 (qfacPos (N + 1))) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_negOddPochInf (show p.1 + 1 ≤ N + 1 by omega),
        coeff_E2prodOnePlus_eq (show p.2 + 1 ≤ N + 1 by omega)]
  rw [h1, distinctSplit_eq, ← coeff_prodOnePlus (show N + 1 ≤ 2 * (N + 1) by omega)]

end MockTheta5.JTP
