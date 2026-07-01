/-
# The `a=q` Bailey pair for `1/(q;q)_n` — the second Rogers–Ramanujan identity

A second worked `a=q` Bailey pair, proved by the same creative telescoping as `MockTheta5BaileyQPairA`
(reusing all its foundations `geom`, `geom_eq`, `Bfac`, `Bfac_prev/next`, inverse shifts):

  `αₙ = (−1)ⁿ q^{n(3n+1)/2}(1+q+···+q^{2n})`,   `βₙ = 1/(q;q)_n`   (`isBaileyPairQ_B`).

`S(n) := Σ_{r≤n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r})` satisfies `(1−q^n)·S(n) = S(n−1)` (`SsumB_rec`) via the
certificate `G(n,r) = (−1)^{r+1} q^{n+pentM(r)}(1+···+q^{r-1})(1−q^{n+r+1})/((q;q)_{n-r}(q²;q)_{n+r})`, where
`pentM r = r(3r−1)/2` is defined **recursively** (`pentM(r+1)=pentM r+3r+1`) so the pentagonal exponents
carry no ℕ-division and `lemA_B`/`lemB_B` stay pure `ring` identities.

Feeding the pair into `bailey_transform_q` gives the second Rogers–Ramanujan identity in Bailey-transform
form `Σ q^{n²+n}/(q;q)_n = (1/(q²;q)_∞)·Σ q^{n²+n} αₙ` (`rogersRamanujan2_transform`); the `α`-sum is the mod-5
theta whose product form (the classical RR2 product) needs the quintuple product not yet in Mathlib. No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyQPairA

namespace MockTheta5.Bailey
open PowerSeries

/-- pentagonal numbers `pentM r = r(3r−1)/2`, defined recursively to avoid ℕ-division. -/
def pentM : ℕ → ℕ
  | 0 => 0
  | (r + 1) => pentM r + (3 * r + 1)

lemma pentM_succ (r : ℕ) : pentM (r + 1) = pentM r + (3 * r + 1) := rfl

/-- the RR2 Bailey `α`: `αᵣ = (−1)ʳ q^{r(3r+1)/2}(1+···+q^{2r})` (exponent `pentM r + r`). -/
noncomputable def alphaB (r : ℕ) : PowerSeries ℤ := (-1) ^ r * X ^ (pentM r + r) * geom (2 * r + 1)

noncomputable def FtermB (n r : ℕ) : PowerSeries ℤ := alphaB r * Bfac (n - r) (n + r)

noncomputable def GtermB (n r : ℕ) : PowerSeries ℤ :=
  (-1) ^ (r + 1) * X ^ (n + pentM r) * geom r * ((1 - X ^ (n + r + 1)) * Bfac (n - r) (n + r))

lemma GB_zero (n : ℕ) : GtermB n 0 = 0 := by simp [GtermB, geom]

lemma lemA_B (r d : ℕ) :
    (1 - X ^ (r + 1 + d)) * FtermB (r + 1 + d) r - FtermB (r + d) r
      = GtermB (r + 1 + d) (r + 1) - GtermB (r + 1 + d) r := by
  simp only [FtermB, GtermB, alphaB]
  rw [show (r + 1 + d) + r + 1 = 2 * r + d + 2 from by omega,
      show (r + 1 + d) + (r + 1) + 1 = 2 * r + d + 3 from by omega,
      show (r + 1 + d) - r = d + 1 from by omega, show (r + 1 + d) + r = 2 * r + 1 + d from by omega,
      show (r + d) - r = d from by omega, show (r + d) + r = 2 * r + d from by omega,
      show (r + 1 + d) - (r + 1) = d from by omega, show (r + 1 + d) + (r + 1) = 2 * r + d + 2 from by omega,
      Bfac_prev r d, Bfac_next r d, pentM_succ r,
      geom_eq (2 * r + 1), geom_eq r, geom_eq (r + 1)]
  simp only [two_mul, pow_add, pow_succ]
  ring

lemma lemB_B (n : ℕ) : (1 - X ^ n) * FtermB n n = - GtermB n n := by
  simp only [FtermB, GtermB, alphaB]
  rw [show n + n + 1 = 2 * n + 1 from by omega, show n - n = 0 from by omega,
      show n + n = 2 * n from by omega, show pentM n + n = n + pentM n from by ring,
      geom_eq (2 * n + 1), geom_eq n]
  simp only [two_mul, pow_add, pow_succ]
  ring

noncomputable def SsumB (n : ℕ) : PowerSeries ℤ := ∑ r ∈ Finset.range (n + 1), FtermB n r

lemma SsumB_rec (m : ℕ) : (1 - X ^ (m + 1)) * SsumB (m + 1) = SsumB m := by
  simp only [SsumB]
  rw [Finset.mul_sum, Finset.sum_range_succ, lemB_B (m + 1)]
  have hterm : ∀ r ∈ Finset.range (m + 1),
      (1 - X ^ (m + 1)) * FtermB (m + 1) r
        = FtermB m r + (GtermB (m + 1) (r + 1) - GtermB (m + 1) r) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have h := lemA_B r (m - r)
    rw [show r + 1 + (m - r) = m + 1 from by omega, show r + (m - r) = m from by omega] at h
    linear_combination h
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_range_sub (fun r => GtermB (m + 1) r), GB_zero]
  ring

lemma SsumB_eq (n : ℕ) : SsumB n = Ring.inverse (qfac n) := by
  induction n with
  | zero => simp [SsumB, FtermB, alphaB, Bfac, geom, pentM, qfac, q2fac]
  | succ m ih =>
      have hrec := SsumB_rec m
      rw [ih] at hrec
      have hunit : qfac (m + 1) * SsumB (m + 1) = 1 := by
        rw [qfac_succ, mul_assoc, hrec, Ring.mul_inverse_cancel _ (isUnit_qfac m)]
      calc SsumB (m + 1)
          = Ring.inverse (qfac (m + 1)) * (qfac (m + 1) * SsumB (m + 1)) := by
            rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_qfac (m + 1)), one_mul]
        _ = Ring.inverse (qfac (m + 1)) := by rw [hunit, mul_one]

/-- **The `a=q` Bailey pair for the second Rogers–Ramanujan identity**:
`(αₙ = (−1)ⁿ q^{n(3n+1)/2}(1+···+q^{2n}), βₙ = 1/(q;q)_n)`. -/
theorem isBaileyPairQ_B : IsBaileyPairQ alphaB (fun n => Ring.inverse (qfac n)) := by
  intro n
  show Ring.inverse (qfac n) = _
  rw [← SsumB_eq n, SsumB]
  apply Finset.sum_congr rfl
  intro r _
  rw [FtermB, Bfac, ← mul_assoc]

end MockTheta5.Bailey


namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- **The second Rogers–Ramanujan identity, Bailey-transform form**: feeding `isBaileyPairQ_B` into
`bailey_transform_q` gives `Σ_{n≥0} q^{n²+n}/(q;q)_n = (1/(q²;q)_∞)·Σ_{n≥0} q^{n²+n}·αₙ`. -/
theorem rogersRamanujan2_transform :
    tsumQsqQ (fun n => Ring.inverse (qfac n)) = (1 - X) * partitionGF * tsumQsqQ alphaB :=
  bailey_transform_q isBaileyPairQ_B

end MockTheta5.JTP
