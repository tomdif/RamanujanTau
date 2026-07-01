/-
# The first Rogers–Ramanujan identity — the `a=1` pentagonal Bailey pair

Complementing the `a=q` pairs (`MockTheta5BaileyQPairA/B`), this file supplies the classical **`a=1`** Bailey
pair behind the *first* Rogers–Ramanujan identity, proved by the same creative telescoping and plugged into
the existing `a=1` `bailey_transform`:

  `α₀ = 1`,  `αₙ = (−1)ⁿ q^{n(3n-1)/2}(1+qⁿ)` (n ≥ 1),   `βₙ = 1/(q;q)_n`   (`isBaileyPair_C`).

`S(n) := Σ_{r≤n} αᵣ/((q;q)_{n-r}(q;q)_{n+r})` satisfies `(1−q^n)·S(n) = S(n−1)` (`SsumC_rec`) via the
certificate `G(n,r) = (−1)^{r+1} q^{n+3r(r-1)/2}(1−q^{n+r})/((q;q)_{n-r}(q;q)_{n+r})`. Because the 2-term `α`
coincides at `n=0` (giving `α₀=1`, not `2`), `r=0` is a genuine special case: the generic term-wise identity
`lemA_C` (r ≥ 1) is a pure `ring` fact (no geometric-sum factor), while the `r=0` base `lemA0_C` is a
separate boundary identity (the `(1−q^{m+1})` cancels its inverse). Pentagonal exponents use `Apent r =
3r(r-1)/2` and `pentM r = r(3r-1)/2`, both recursive to avoid ℕ-division.

Feeding the pair into `bailey_transform` gives RR1 in Bailey-transform form `Σ q^{n²}/(q;q)_n =
(1/(q;q)_∞)·Σ q^{n²} αₙ` (`rogersRamanujan1_transform`); the `α`-sum is the mod-5 pentagonal theta
`Σ_{n∈ℤ}(−1)ⁿ q^{n(5n-1)/2}` (since `n²+pentM(n)=n(5n-1)/2`), whose product form (the classical RR1 product)
needs the quintuple product not yet in Mathlib. No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyQPairA
import RamanujanTau.MockTheta5BaileyTransform

namespace MockTheta5.Bailey
open PowerSeries

lemma isUnit_oneSubXpow (k : ℕ) : IsUnit (1 - X ^ (k + 1) : PowerSeries ℤ) := by
  rw [isUnit_iff_constantCoeff, map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero]
  exact isUnit_one

def Apent : ℕ → ℕ
  | 0 => 0
  | (r + 1) => Apent r + 3 * r
lemma Apent_succ (r : ℕ) : Apent (r + 1) = Apent r + 3 * r := rfl

noncomputable def Bfac1 (a b : ℕ) : PowerSeries ℤ := Ring.inverse (qfac a) * Ring.inverse (qfac b)

lemma Bfac1_prev (r d : ℕ) :
    Bfac1 d (2 * r + d) = (1 - X ^ (d + 1)) * (1 - X ^ (2 * r + 1 + d)) * Bfac1 (d + 1) (2 * r + 1 + d) := by
  rw [Bfac1, Bfac1, inv_qfac_succ d, inv_qfac_succ (2 * r + d), show (2 * r + d) + 1 = 2 * r + 1 + d from by omega]
  ring

lemma Bfac1_next (r d : ℕ) :
    (1 - X ^ (2 * r + d + 2)) * Bfac1 d (2 * r + d + 2) = (1 - X ^ (d + 1)) * Bfac1 (d + 1) (2 * r + 1 + d) := by
  rw [Bfac1, Bfac1, inv_qfac_succ d, inv_qfac_succ (2 * r + 1 + d),
      show 2 * r + 1 + d + 1 = 2 * r + d + 2 from by omega]
  ring

noncomputable def alphaC (r : ℕ) : PowerSeries ℤ :=
  if r = 0 then 1 else (-1) ^ r * X ^ (Apent r + r) * (1 + X ^ r)

noncomputable def FtermC (n r : ℕ) : PowerSeries ℤ := alphaC r * Bfac1 (n - r) (n + r)

noncomputable def GtermCore (n r : ℕ) : PowerSeries ℤ :=
  (-1) ^ (r + 1) * X ^ (n + Apent r) * ((1 - X ^ (n + r)) * Bfac1 (n - r) (n + r))

lemma lemA_C (r d : ℕ) (hr : r ≠ 0) :
    (1 - X ^ (r + 1 + d)) * FtermC (r + 1 + d) r - FtermC (r + d) r
      = GtermCore (r + 1 + d) (r + 1) - GtermCore (r + 1 + d) r := by
  simp only [FtermC, GtermCore, alphaC, if_neg hr]
  rw [show (r + 1 + d) + (r + 1) = 2 * r + d + 2 from by omega,
      show (r + 1 + d) - r = d + 1 from by omega, show (r + 1 + d) + r = 2 * r + 1 + d from by omega,
      show (r + d) - r = d from by omega, show (r + d) + r = 2 * r + d from by omega,
      show (r + 1 + d) - (r + 1) = d from by omega,
      Bfac1_prev r d, Bfac1_next r d, Apent_succ r]
  simp only [two_mul, pow_add, pow_succ]
  ring

lemma lemB_C (n : ℕ) (hn : n ≠ 0) : (1 - X ^ n) * FtermC n n = - GtermCore n n := by
  simp only [FtermC, GtermCore, alphaC, if_neg hn]
  rw [show n + n = 2 * n from by omega, show n - n = 0 from by omega,
      show Apent n + n = n + Apent n from by ring]
  simp only [two_mul, pow_add, pow_succ]
  ring

lemma inv_qfac_succ' (n : ℕ) :
    Ring.inverse (qfac (n + 1)) = Ring.inverse (1 - X ^ (n + 1)) * Ring.inverse (qfac n) := by
  have h1 : Ring.inverse (1 - X ^ (n+1)) * Ring.inverse (qfac n) * qfac (n + 1) = 1 := by
    rw [qfac_succ, show Ring.inverse (1 - X ^ (n+1)) * Ring.inverse (qfac n) * (qfac n * (1 - X ^ (n+1)))
          = (Ring.inverse (1 - X ^ (n+1)) * (1 - X ^ (n+1))) * (Ring.inverse (qfac n) * qfac n) from by ring,
        Ring.inverse_mul_cancel _ (isUnit_oneSubXpow n), Ring.inverse_mul_cancel _ (isUnit_qfac n), mul_one]
  calc Ring.inverse (qfac (n + 1))
      = Ring.inverse (qfac (n + 1)) * (Ring.inverse (1 - X ^ (n+1)) * Ring.inverse (qfac n) * qfac (n + 1)) := by
        rw [h1, mul_one]
    _ = (Ring.inverse (1 - X ^ (n+1)) * Ring.inverse (qfac n)) * (Ring.inverse (qfac (n + 1)) * qfac (n + 1)) := by ring
    _ = Ring.inverse (1 - X ^ (n+1)) * Ring.inverse (qfac n) := by
        rw [Ring.inverse_mul_cancel _ (isUnit_qfac (n + 1)), mul_one]

lemma lemA0_C (n : ℕ) (hn : 1 ≤ n) :
    (1 - X ^ n) * FtermC n 0 - FtermC (n - 1) 0 = GtermCore n 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have c0 : Ring.inverse (qfac m) * qfac m = 1 := Ring.inverse_mul_cancel _ (isUnit_qfac m)
  have c1 : Ring.inverse (qfac (m + 1)) * qfac (m + 1) = 1 := Ring.inverse_mul_cancel _ (isUnit_qfac (m + 1))
  have c2 : Ring.inverse (qfac (m + 2)) * qfac (m + 2) = 1 := Ring.inverse_mul_cancel _ (isUnit_qfac (m + 2))
  have hne : qfac (m + 2) * qfac (m + 2) ≠ 0 := mul_ne_zero (isUnit_qfac _).ne_zero (isUnit_qfac _).ne_zero
  have hq2' : qfac (m + 2) = qfac (m + 1) * (1 - X ^ (m + 2)) := by
    rw [show m + 2 = (m + 1) + 1 from rfl]; exact qfac_succ (m + 1)
  have b1 : Ring.inverse (qfac (m+1)) * Ring.inverse (qfac (m+1)) * (qfac (m+2) * qfac (m+2))
      = (1 - X^(m+2)) * (1 - X^(m+2)) := by
    rw [hq2', show Ring.inverse (qfac (m+1)) * Ring.inverse (qfac (m+1))
            * (qfac (m+1) * (1 - X^(m+2)) * (qfac (m+1) * (1 - X^(m+2))))
          = (Ring.inverse (qfac (m+1)) * qfac (m+1)) * ((Ring.inverse (qfac (m+1)) * qfac (m+1))
              * ((1 - X^(m+2)) * (1 - X^(m+2)))) from by ring, c1, one_mul, one_mul]
  have b0 : Ring.inverse (qfac m) * Ring.inverse (qfac m) * (qfac (m+2) * qfac (m+2))
      = ((1 - X^(m+1)) * (1 - X^(m+2))) * ((1 - X^(m+1)) * (1 - X^(m+2))) := by
    rw [hq2', qfac_succ m,
        show Ring.inverse (qfac m) * Ring.inverse (qfac m)
            * (qfac m * (1 - X^(m+1)) * (1 - X^(m+2)) * (qfac m * (1 - X^(m+1)) * (1 - X^(m+2))))
          = (Ring.inverse (qfac m) * qfac m) * ((Ring.inverse (qfac m) * qfac m)
              * (((1 - X^(m+1)) * (1 - X^(m+2))) * ((1 - X^(m+1)) * (1 - X^(m+2))))) from by ring,
        c0, one_mul, one_mul]
  have b2 : Ring.inverse (qfac m) * Ring.inverse (qfac (m+2)) * (qfac (m+2) * qfac (m+2))
      = (1 - X^(m+1)) * (1 - X^(m+2)) := by
    rw [show Ring.inverse (qfac m) * Ring.inverse (qfac (m+2)) * (qfac (m+2) * qfac (m+2))
          = (Ring.inverse (qfac (m+2)) * qfac (m+2)) * (Ring.inverse (qfac m) * qfac (m+2)) from by ring,
        c2, one_mul, hq2', qfac_succ m,
        show Ring.inverse (qfac m) * (qfac m * (1 - X^(m+1)) * (1 - X^(m+2)))
          = (Ring.inverse (qfac m) * qfac m) * ((1 - X^(m+1)) * (1 - X^(m+2))) from by ring, c0, one_mul]
  simp only [FtermC, GtermCore, alphaC, Bfac1, if_true,
    Nat.sub_zero, Nat.add_zero, show Apent 1 = 0 from rfl,
    show m + 1 - 1 = m from by omega, show m + 1 + 1 = m + 2 from by omega, pow_succ, pow_zero, one_mul]
  refine mul_right_cancel₀ hne ?_
  linear_combination (1 - X ^ m * X) * b1 - b0 - X ^ m * X * (1 - X ^ m * X * X) * b2



noncomputable def GtermC (n r : ℕ) : PowerSeries ℤ := if r = 0 then 0 else GtermCore n r
lemma GtermC_zero (n : ℕ) : GtermC n 0 = 0 := by simp [GtermC]
lemma GtermC_pos (n r : ℕ) (hr : r ≠ 0) : GtermC n r = GtermCore n r := by simp [GtermC, hr]

noncomputable def SsumC (n : ℕ) : PowerSeries ℤ := ∑ r ∈ Finset.range (n + 1), FtermC n r

lemma SsumC_rec (m : ℕ) : (1 - X ^ (m + 1)) * SsumC (m + 1) = SsumC m := by
  simp only [SsumC]
  rw [Finset.mul_sum, Finset.sum_range_succ]
  have hterm : ∀ r ∈ Finset.range (m + 1),
      (1 - X ^ (m + 1)) * FtermC (m + 1) r
        = FtermC m r + (GtermC (m + 1) (r + 1) - GtermC (m + 1) r) := by
    intro r hr
    rw [Finset.mem_range] at hr
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      rw [GtermC_zero, GtermC_pos _ 1 one_ne_zero, sub_zero]
      have h := lemA0_C (m + 1) (by omega)
      rw [show (m + 1) - 1 = m from by omega] at h
      linear_combination h
    · obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [GtermC_pos _ (r' + 1) (Nat.succ_ne_zero r'), GtermC_pos _ (r' + 1 + 1) (Nat.succ_ne_zero _)]
      have h := lemA_C (r' + 1) (m - (r' + 1)) (Nat.succ_ne_zero r')
      rw [show (r' + 1) + 1 + (m - (r' + 1)) = m + 1 from by omega,
          show (r' + 1) + (m - (r' + 1)) = m from by omega] at h
      linear_combination h
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_range_sub (fun r => GtermC (m + 1) r), GtermC_zero,
      lemB_C (m + 1) (Nat.succ_ne_zero m), GtermC_pos (m + 1) (m + 1) (Nat.succ_ne_zero m)]
  ring

lemma SsumC_eq (n : ℕ) : SsumC n = Ring.inverse (qfac n) := by
  induction n with
  | zero => simp [SsumC, FtermC, alphaC, Bfac1, qfac]
  | succ m ih =>
      have hrec := SsumC_rec m
      rw [ih] at hrec
      have hunit : qfac (m + 1) * SsumC (m + 1) = 1 := by
        rw [qfac_succ, mul_assoc, hrec, Ring.mul_inverse_cancel _ (isUnit_qfac m)]
      calc SsumC (m + 1)
          = Ring.inverse (qfac (m + 1)) * (qfac (m + 1) * SsumC (m + 1)) := by
            rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_qfac (m + 1)), one_mul]
        _ = Ring.inverse (qfac (m + 1)) := by rw [hunit, mul_one]

/-- **The first Rogers–Ramanujan `a=1` Bailey pair**:
`(α₀ = 1, αₙ = (−1)ⁿ q^{n(3n-1)/2}(1+qⁿ), βₙ = 1/(q;q)_n)`. -/
theorem isBaileyPair_C : IsBaileyPair alphaC (fun n => Ring.inverse (qfac n)) := by
  intro n
  show Ring.inverse (qfac n) = _
  rw [← SsumC_eq n, SsumC]
  apply Finset.sum_congr rfl
  intro r _
  rw [FtermC, Bfac1, ← mul_assoc]

end MockTheta5.Bailey

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- **The first Rogers–Ramanujan identity, Bailey-transform form**: feeding `isBaileyPair_C` into the
`a=1` `bailey_transform` gives `Σ_{n≥0} q^{n²}/(q;q)_n = (1/(q;q)_∞)·Σ_{n≥0} q^{n²}·αₙ` — the `α`-sum is the
mod-5 pentagonal theta `Σ_{n∈ℤ}(−1)ⁿ q^{n(5n-1)/2}`. -/
theorem rogersRamanujan1_transform :
    tsumQsq (fun n => Ring.inverse (qfac n)) = partitionGF * tsumQsq alphaC :=
  bailey_transform isBaileyPair_C

end MockTheta5.JTP
