/-
# The Bailey-transform limit — the Rogers–Ramanujan engine

For a Bailey pair `(α, β)` relative to `a = 1` (`IsBaileyPair`: `βₙ = Σ_{r≤n} αᵣ/((q;q)_{n-r}(q;q)_{n+r})`),

  **`Σ_{n≥0} q^{n²} βₙ  =  (1/(q;q)_∞) · Σ_{n≥0} q^{n²} αₙ`**   (`bailey_transform`).

This is the engine that converts a Bailey pair into a Rogers–Ramanujan-type sum/product identity: feeding in
the right Bailey pair makes the `α`-sum a theta function (→ a product by the Jacobi triple product), giving
the RR product side. The proof is the `n → ∞` limit of the (already-proved) Bailey chain step
`isBaileyPair_chain` read off at `N = 2m+1`: the finite factors `1/(q;q)_{N∓r}` stabilize to `1/(q;q)_∞`
(`inv_qfac_stable`/`inv_qfac_dvd`, swapped inside coefficients by `coeff_mul_congr_left`), and the unit
`1/(q;q)_∞` cancels.

Immediate corollary (the seed pair): the **Durfee-square generating function**
`Σ_{n≥0} q^{n²}/(q;q)_n² = 1/(q;q)_∞`. The remaining ingredient for Rogers–Ramanujan proper is the
**RR Bailey pair** (`βₙ = 1/(q;q)_n` with the pentagonal `α`), whose `α`-sum the Jacobi triple product turns
into the mod-5 product. No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyChain
import RamanujanTau.MockTheta5DurfeeInf
namespace MockTheta5.JTP
open PowerSeries MockTheta5 MockTheta5.Bailey

noncomputable def tsumQsq (f : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun m => coeff m (∑ n ∈ Finset.range (m + 1), X ^ (n ^ 2) * f n)

lemma coeff_tsumQsq (f : ℕ → PowerSeries ℤ) {m M : ℕ} (hM : m + 1 ≤ M) :
    coeff m (tsumQsq f) = ∑ n ∈ Finset.range M, coeff m (X ^ (n ^ 2) * f n) := by
  rw [tsumQsq, coeff_mk, map_sum]
  refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) hM)) (fun n _ hn => ?_)
  simp only [Finset.mem_range, not_lt] at hn
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by nlinarith [hn])]

lemma coeff_term_L (β : ℕ → PowerSeries ℤ) (m j : ℕ) :
    coeff m (X ^ (j ^ 2) * Ring.inverse (qfac (2 * m + 1 - j)) * β j)
      = coeff m (X ^ (j ^ 2) * partitionGF * β j) := by
  by_cases hj : j ≤ m
  · refine coeff_mul_congr_left (g := β j) ?_
    obtain ⟨c, hc⟩ := inv_qfac_dvd (k := m) (N := 2 * m + 1 - j) (by omega)
    exact ⟨X ^ (j ^ 2) * c, by rw [← mul_sub, partitionGF, hc]; ring⟩
  · rw [show X ^ (j ^ 2) * Ring.inverse (qfac (2 * m + 1 - j)) * β j
          = X ^ (j ^ 2) * (Ring.inverse (qfac (2 * m + 1 - j)) * β j) from by ring,
        show X ^ (j ^ 2) * partitionGF * β j = X ^ (j ^ 2) * (partitionGF * β j) from by ring,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
        if_neg (by have := Nat.lt_of_not_le hj; nlinarith),
        if_neg (by have := Nat.lt_of_not_le hj; nlinarith)]

lemma coeff_term_R (α : ℕ → PowerSeries ℤ) (m r : ℕ) :
    coeff m (X ^ (r ^ 2) * α r * Ring.inverse (qfac (2 * m + 1 - r)) * Ring.inverse (qfac (2 * m + 1 + r)))
      = coeff m (X ^ (r ^ 2) * α r * partitionGF * partitionGF) := by
  by_cases hr : r ≤ m
  · obtain ⟨c1, hc1⟩ := inv_qfac_dvd (k := m) (N := 2 * m + 1 - r) (by omega)
    obtain ⟨c2, hc2⟩ := inv_qfac_dvd (k := m) (N := 2 * m + 1 + r) (by omega)
    rw [coeff_mul_congr_left (g := Ring.inverse (qfac (2 * m + 1 + r)))
        (f := X ^ (r ^ 2) * α r * Ring.inverse (qfac (2 * m + 1 - r)))
        (f' := X ^ (r ^ 2) * α r * partitionGF)
        ⟨X ^ (r ^ 2) * α r * c1, by rw [← mul_sub, partitionGF, hc1]; ring⟩,
      mul_comm (X ^ (r ^ 2) * α r * partitionGF) (Ring.inverse (qfac (2 * m + 1 + r))),
      mul_comm (X ^ (r ^ 2) * α r * partitionGF) partitionGF,
      coeff_mul_congr_left (g := X ^ (r ^ 2) * α r * partitionGF)
        (f := Ring.inverse (qfac (2 * m + 1 + r))) (f' := partitionGF)
        ⟨c2, by rw [partitionGF]; exact hc2⟩]
  · rw [show X ^ (r ^ 2) * α r * Ring.inverse (qfac (2 * m + 1 - r)) * Ring.inverse (qfac (2 * m + 1 + r))
          = X ^ (r ^ 2) * (α r * Ring.inverse (qfac (2 * m + 1 - r)) * Ring.inverse (qfac (2 * m + 1 + r)))
          from by ring,
        show X ^ (r ^ 2) * α r * partitionGF * partitionGF
          = X ^ (r ^ 2) * (α r * partitionGF * partitionGF) from by ring,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
        if_neg (by have := Nat.lt_of_not_le hr; nlinarith),
        if_neg (by have := Nat.lt_of_not_le hr; nlinarith)]


lemma coeff_mul_congr_right {k : ℕ} {f g g' : PowerSeries ℤ}
    (h : (X : PowerSeries ℤ) ^ (k + 1) ∣ (g - g')) : coeff k (f * g) = coeff k (f * g') := by
  rw [mul_comm f g, mul_comm f g']; exact coeff_mul_congr_left h

lemma tsumQsq_dvd (g : ℕ → PowerSeries ℤ) (m : ℕ) :
    (X : PowerSeries ℤ) ^ (m + 1) ∣ (tsumQsq g - ∑ n ∈ Finset.range (2 * m + 2), X ^ (n ^ 2) * g n) := by
  rw [PowerSeries.X_pow_dvd_iff]; intro k hk
  rw [map_sub, coeff_tsumQsq g (show k + 1 ≤ 2 * m + 2 by omega), map_sum, sub_self]

lemma coeff_prefactor_tsumQsq (P : PowerSeries ℤ) (g : ℕ → PowerSeries ℤ) (m : ℕ) :
    coeff m (P * tsumQsq g) = ∑ j ∈ Finset.range (2 * m + 2), coeff m (P * (X ^ (j ^ 2) * g j)) := by
  rw [coeff_mul_congr_right (f := P) (tsumQsq_dvd g m), Finset.mul_sum, map_sum]

lemma isUnit_partitionGF : IsUnit partitionGF :=
  IsUnit.of_mul_eq_one qfacInf (by rw [partitionGF]; exact Ring.inverse_mul_cancel _ isUnit_qfacInf)

/-- **The Bailey-transform limit**: for any Bailey pair `(α,β)` (relative to `a=1`),
`Σ_{n≥0} q^{n²} βₙ = (1/(q;q)_∞) · Σ_{n≥0} q^{n²} αₙ`. The engine that turns a Bailey pair into a
Rogers–Ramanujan-type sum/product identity. -/
theorem bailey_transform {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPair α β) :
    tsumQsq β = partitionGF * tsumQsq α := by
  have key : partitionGF * tsumQsq β = partitionGF ^ 2 * tsumQsq α := by
    ext m
    have hchain := isBaileyPair_chain h (2 * m + 1)
    rw [coeff_prefactor_tsumQsq, coeff_prefactor_tsumQsq]
    have hL : ∑ j ∈ Finset.range (2 * m + 2), coeff m (partitionGF * (X ^ (j ^ 2) * β j))
        = coeff m (chainBeta β (2 * m + 1)) := by
      rw [chainBeta, map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [coeff_term_L]; congr 1; ring)
    have hR : ∑ r ∈ Finset.range (2 * m + 2), coeff m (partitionGF ^ 2 * (X ^ (r ^ 2) * α r))
        = coeff m (chainBeta β (2 * m + 1)) := by
      rw [hchain, map_sum]
      exact Finset.sum_congr rfl (fun r _ => by rw [chainAlpha, coeff_term_R]; congr 1; ring)
    rw [hL, hR]
  have hu := isUnit_partitionGF
  rw [sq, mul_assoc] at key
  exact (mul_right_inj' hu.ne_zero).mp key


lemma tsumQsq_seedAlpha : tsumQsq seedAlpha = 1 := by
  ext m
  rw [tsumQsq, coeff_mk,
      Finset.sum_eq_single 0 (fun n _ hn => by rw [seedAlpha, if_neg hn, mul_zero])
        (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h)]
  simp [seedAlpha]

/-- **Durfee-square generating function** (Bailey transform of the seed pair):
`Σ_{n≥0} q^{n²}/(q;q)_n² = 1/(q;q)_∞` — every partition has a unique Durfee square. -/
theorem sum_qsq_div_qfacSq : tsumQsq seedBeta = partitionGF := by
  rw [bailey_transform isBaileyPair_seed, tsumQsq_seedAlpha, mul_one]
end MockTheta5.JTP
