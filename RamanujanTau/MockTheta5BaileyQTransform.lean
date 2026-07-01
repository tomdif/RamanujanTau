/-
# The `a = q` Bailey-transform limit — the mock-theta engine

For an `a = q` Bailey pair `(α, β)` (`IsBaileyPairQ`: `βₙ = Σ_{r≤n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r})`),

  **`Σ_{n≥0} q^{n²+n} βₙ  =  (1/(q²;q)_∞) · Σ_{n≥0} q^{n²+n} αₙ`**   (`bailey_transform_q`),

where `1/(q²;q)_∞ = (1−q)·(1/(q;q)_∞) = (1 - X)·partitionGF`. This is the `a = q` analogue of
`bailey_transform` and the engine that converts the `a = q` Bailey pairs of the fifth-order mock thetas into
sum/product identities.

The proof is the `n → ∞` limit of the `a = q` chain step `isBaileyPairQ_chain` read at `N = 2m+1`: the
`β`-side factor `1/(q;q)_{N-j}` stabilizes to `partitionGF` (`coeff_term_L_q`), and the `α`-side carries the
extra `1/(q²;q)_{N+r}` factor, which stabilizes to `(1−q)·partitionGF` via `inv_q2fac_dvd` (the `(q²;q)`
version of `inv_qfac_dvd`); the leading `partitionGF` unit then cancels.

Corollary (seed pair): the `a = q` Durfee-type identity
`Σ_{n≥0} q^{n²+n}/((q;q)_n (q²;q)_n) = 1/(q²;q)_∞` (`sum_qsqPlusN_div_qfac_q2fac`). No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyTransform
import RamanujanTau.MockTheta5BaileyQ
namespace MockTheta5.JTP
open PowerSeries MockTheta5 MockTheta5.Bailey

noncomputable def tsumQsqQ (f : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun m => coeff m (∑ n ∈ Finset.range (m + 1), X ^ (n ^ 2 + n) * f n)

lemma coeff_tsumQsqQ (f : ℕ → PowerSeries ℤ) {m M : ℕ} (hM : m + 1 ≤ M) :
    coeff m (tsumQsqQ f) = ∑ n ∈ Finset.range M, coeff m (X ^ (n ^ 2 + n) * f n) := by
  rw [tsumQsqQ, coeff_mk, map_sum]
  refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) hM)) (fun n _ hn => ?_)
  simp only [Finset.mem_range, not_lt] at hn
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by nlinarith [hn])]

lemma coeff_term_L_q (β : ℕ → PowerSeries ℤ) (m j : ℕ) :
    coeff m (X ^ (j ^ 2 + j) * Ring.inverse (qfac (2 * m + 1 - j)) * β j)
      = coeff m (X ^ (j ^ 2 + j) * partitionGF * β j) := by
  by_cases hj : j ≤ m
  · refine coeff_mul_congr_left (g := β j) ?_
    obtain ⟨c, hc⟩ := inv_qfac_dvd (k := m) (N := 2 * m + 1 - j) (by omega)
    exact ⟨X ^ (j ^ 2 + j) * c, by rw [← mul_sub, partitionGF, hc]; ring⟩
  · rw [show X ^ (j ^ 2 + j) * Ring.inverse (qfac (2 * m + 1 - j)) * β j
          = X ^ (j ^ 2 + j) * (Ring.inverse (qfac (2 * m + 1 - j)) * β j) from by ring,
        show X ^ (j ^ 2 + j) * partitionGF * β j = X ^ (j ^ 2 + j) * (partitionGF * β j) from by ring,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
        if_neg (by have := Nat.lt_of_not_le hj; nlinarith),
        if_neg (by have := Nat.lt_of_not_le hj; nlinarith)]

lemma inv_q2fac_dvd {k N : ℕ} (hN : k + 1 ≤ N) :
    (X : PowerSeries ℤ) ^ (k + 1) ∣ (Ring.inverse (q2fac N) - (1 - X) * partitionGF) := by
  obtain ⟨c, hc⟩ := inv_qfac_dvd (k := k) (N := N + 1) (by omega)
  rw [inv_q2fac, partitionGF]
  exact ⟨(1 - X) * c, by rw [← mul_sub, hc]; ring⟩

lemma coeff_term_R_q (α : ℕ → PowerSeries ℤ) (m r : ℕ) :
    coeff m (X ^ (r ^ 2 + r) * α r * Ring.inverse (qfac (2 * m + 1 - r))
        * Ring.inverse (q2fac (2 * m + 1 + r)))
      = coeff m (X ^ (r ^ 2 + r) * α r * partitionGF * ((1 - X) * partitionGF)) := by
  by_cases hr : r ≤ m
  · obtain ⟨c1, hc1⟩ := inv_qfac_dvd (k := m) (N := 2 * m + 1 - r) (by omega)
    rw [coeff_mul_congr_left (g := Ring.inverse (q2fac (2 * m + 1 + r)))
        (f := X ^ (r ^ 2 + r) * α r * Ring.inverse (qfac (2 * m + 1 - r)))
        (f' := X ^ (r ^ 2 + r) * α r * partitionGF)
        ⟨X ^ (r ^ 2 + r) * α r * c1, by rw [← mul_sub, partitionGF, hc1]; ring⟩,
      mul_comm (X ^ (r ^ 2 + r) * α r * partitionGF) (Ring.inverse (q2fac (2 * m + 1 + r))),
      mul_comm (X ^ (r ^ 2 + r) * α r * partitionGF) ((1 - X) * partitionGF),
      coeff_mul_congr_left (g := X ^ (r ^ 2 + r) * α r * partitionGF)
        (f := Ring.inverse (q2fac (2 * m + 1 + r))) (f' := (1 - X) * partitionGF)
        (inv_q2fac_dvd (by omega))]
  · rw [show X ^ (r ^ 2 + r) * α r * Ring.inverse (qfac (2 * m + 1 - r))
            * Ring.inverse (q2fac (2 * m + 1 + r))
          = X ^ (r ^ 2 + r) * (α r * Ring.inverse (qfac (2 * m + 1 - r))
            * Ring.inverse (q2fac (2 * m + 1 + r))) from by ring,
        show X ^ (r ^ 2 + r) * α r * partitionGF * ((1 - X) * partitionGF)
          = X ^ (r ^ 2 + r) * (α r * partitionGF * ((1 - X) * partitionGF)) from by ring,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
        if_neg (by have := Nat.lt_of_not_le hr; nlinarith),
        if_neg (by have := Nat.lt_of_not_le hr; nlinarith)]

lemma tsumQsqQ_dvd (g : ℕ → PowerSeries ℤ) (m : ℕ) :
    (X : PowerSeries ℤ) ^ (m + 1) ∣ (tsumQsqQ g - ∑ n ∈ Finset.range (2 * m + 2), X ^ (n ^ 2 + n) * g n) := by
  rw [PowerSeries.X_pow_dvd_iff]; intro k hk
  rw [map_sub, coeff_tsumQsqQ g (show k + 1 ≤ 2 * m + 2 by omega), map_sum, sub_self]

lemma coeff_prefactor_tsumQsqQ (P : PowerSeries ℤ) (g : ℕ → PowerSeries ℤ) (m : ℕ) :
    coeff m (P * tsumQsqQ g) = ∑ j ∈ Finset.range (2 * m + 2), coeff m (P * (X ^ (j ^ 2 + j) * g j)) := by
  rw [coeff_mul_congr_right (f := P) (tsumQsqQ_dvd g m), Finset.mul_sum, map_sum]

theorem bailey_transform_q {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPairQ α β) :
    tsumQsqQ β = (1 - X) * partitionGF * tsumQsqQ α := by
  have key : partitionGF * tsumQsqQ β = partitionGF * ((1 - X) * partitionGF) * tsumQsqQ α := by
    ext m
    have hchain := isBaileyPairQ_chain h (2 * m + 1)
    rw [coeff_prefactor_tsumQsqQ, coeff_prefactor_tsumQsqQ]
    have hL : ∑ j ∈ Finset.range (2 * m + 2), coeff m (partitionGF * (X ^ (j ^ 2 + j) * β j))
        = coeff m (chainBetaQ β (2 * m + 1)) := by
      rw [chainBetaQ, map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [coeff_term_L_q]; congr 1; ring)
    have hR : ∑ r ∈ Finset.range (2 * m + 2),
          coeff m (partitionGF * ((1 - X) * partitionGF) * (X ^ (r ^ 2 + r) * α r))
        = coeff m (chainBetaQ β (2 * m + 1)) := by
      rw [hchain, map_sum]
      exact Finset.sum_congr rfl (fun r _ => by rw [chainAlphaQ, coeff_term_R_q]; congr 1; ring)
    rw [hL, hR]
  have hu := isUnit_partitionGF
  rw [mul_assoc] at key
  exact (mul_right_inj' hu.ne_zero).mp key

lemma tsumQsqQ_seedAlphaQ : tsumQsqQ seedAlphaQ = 1 := by
  ext m
  rw [tsumQsqQ, coeff_mk,
      Finset.sum_eq_single 0 (fun n _ hn => by rw [seedAlphaQ, if_neg hn, mul_zero])
        (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h)]
  simp [seedAlphaQ]

theorem sum_qsqPlusN_div_qfac_q2fac : tsumQsqQ seedBetaQ = (1 - X) * partitionGF := by
  rw [bailey_transform_q isBaileyPairQ_seed, tsumQsqQ_seedAlphaQ, mul_one]

end MockTheta5.JTP
