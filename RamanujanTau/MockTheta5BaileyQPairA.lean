/-
# The `a=q` Bailey pair for `1/(q²;q²)_n` — closing Identity A

The `a=q` machinery (`bailey_transform_q`) is inert without a concrete non-trivial Bailey pair. This file
supplies one and proves it from scratch: the pair

  `αₙ = (−1)ⁿ q^{n²}(1+q+···+q^{2n})`,   `βₙ = 1/(q²;q²)_n`   (`isBaileyPairQ_A`),

i.e. `Σ_{r≤n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r}) = 1/(q²;q²)_n`. This finite `q`-identity does NOT collapse to the
shared `F_eq_one` core (the mixed-Pochhammer ratio is a genuine infinite series), so it is proved by
**creative telescoping**: `S(n) := Σ_{r≤n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r})` satisfies the first-order recurrence
`(1-q^{2n})·S(n) = S(n-1)` (`Ssum_rec`), via the explicit certificate

  `G(n,r) = (−1)^{r+1} q^{n+r(r-1)}(1+···+q^{2r-1})(1−q^{n+r+1})/((q;q)_{n-r}(q²;q)_{n+r})`

with the term-wise identity `(1-q^{2n})F(n,r) - F(n-1,r) = G(n,r+1) - G(n,r)` (`lemA`, a pure `ring` identity
after clearing `(q²;q)`→`(q;q)` and `geom(m)·(1−q) = 1−q^m`) and the top-term identity
`(1-q^{2n})F(n,n) = -G(n,n)` (`lemB`). Feeding the pair into `bailey_transform_q` gives Identity A in the
form `Σ q^{n²+n}/(q²;q²)_n = (1/(q²;q)_∞)·Σ q^{n²+n} αₙ` (`identityA_transform`). No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyQTransform

namespace MockTheta5.Bailey
open PowerSeries

noncomputable def geom (m : ℕ) : PowerSeries ℤ := ∑ i ∈ Finset.range m, X ^ i

lemma geom_mul (m : ℕ) : (1 - X) * geom m = 1 - X ^ m := by
  induction m with
  | zero => simp [geom]
  | succ m ih => rw [geom, Finset.sum_range_succ, ← geom, mul_add, ih, pow_succ]; ring

lemma isUnit_oneSubX : IsUnit (1 - X : PowerSeries ℤ) := by
  rw [isUnit_iff_constantCoeff, map_sub, map_one, constantCoeff_X, sub_zero]; exact isUnit_one

lemma geom_eq (m : ℕ) : geom m = Ring.inverse (1 - X) * (1 - X ^ m) := by
  rw [← geom_mul, ← mul_assoc, Ring.inverse_mul_cancel _ isUnit_oneSubX, one_mul]

lemma q2fac_succ (m : ℕ) : q2fac (m + 1) = q2fac m * (1 - X ^ (m + 2)) := by
  rw [q2fac, Finset.prod_range_succ, ← q2fac]

/-- `(q;q)_m⁻¹ = (1 - q^{m+1})·(q;q)_{m+1}⁻¹`. -/
lemma inv_qfac_succ (m : ℕ) :
    Ring.inverse (qfac m) = (1 - X ^ (m + 1)) * Ring.inverse (qfac (m + 1)) := by
  have h1 : (1 - X ^ (m+1)) * Ring.inverse (qfac (m+1)) * qfac (m+1) = 1 - X ^ (m+1) := by
    rw [mul_assoc, Ring.inverse_mul_cancel _ (isUnit_qfac (m+1)), mul_one]
  have h2 : Ring.inverse (qfac m) * qfac (m+1) = 1 - X ^ (m+1) := by
    rw [qfac_succ, ← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_qfac m), one_mul]
  exact mul_right_cancel₀ (isUnit_qfac (m+1)).ne_zero (h2.trans h1.symm)

/-- `(q²;q)_m⁻¹ = (1 - q^{m+2})·(q²;q)_{m+1}⁻¹`. -/
lemma inv_q2fac_succ (m : ℕ) :
    Ring.inverse (q2fac m) = (1 - X ^ (m + 2)) * Ring.inverse (q2fac (m + 1)) := by
  have h1 : (1 - X ^ (m+2)) * Ring.inverse (q2fac (m+1)) * q2fac (m+1) = 1 - X ^ (m+2) := by
    rw [mul_assoc, Ring.inverse_mul_cancel _ (isUnit_q2fac (m+1)), mul_one]
  have h2 : Ring.inverse (q2fac m) * q2fac (m+1) = 1 - X ^ (m+2) := by
    rw [q2fac_succ, ← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_q2fac m), one_mul]
  exact mul_right_cancel₀ (isUnit_q2fac (m+1)).ne_zero (h2.trans h1.symm)
/-- `1/((q;q)_a(q²;q)_b)` -- the common Bailey denominator. -/
noncomputable def Bfac (a b : ℕ) : PowerSeries ℤ := Ring.inverse (qfac a) * Ring.inverse (q2fac b)

lemma Bfac_prev (r d : ℕ) :
    Bfac d (2*r+d) = (1 - X^(d+1)) * (1 - X^(2*r+d+2)) * Bfac (d+1) (2*r+1+d) := by
  rw [Bfac, Bfac, inv_qfac_succ d, inv_q2fac_succ (2*r+d), show (2*r+d)+1 = 2*r+1+d from by omega]
  ring

lemma Bfac_next (r d : ℕ) :
    (1 - X^(2*r+d+3)) * Bfac d (2*r+d+2) = (1 - X^(d+1)) * Bfac (d+1) (2*r+1+d) := by
  rw [Bfac, Bfac, inv_qfac_succ d, inv_q2fac_succ (2*r+1+d),
      show 2*r+1+d+2 = 2*r+d+3 from by omega, show (2*r+1+d)+1 = 2*r+d+2 from by omega]
  ring

lemma hsq (r : ℕ) : r ^ 2 = r * (r - 1) + r := by
  rcases r with _ | k
  · rfl
  · simp only [Nat.succ_sub_one]; ring

lemma hnext' (r : ℕ) : (r + 1) * ((r + 1) - 1) = r * (r - 1) + 2 * r := by
  rcases r with _ | k
  · rfl
  · simp only [Nat.succ_sub_one]; ring

/-- the Bailey `α` for `β = 1/(q²;q²)_n`: `αᵣ = (−1)ʳ q^{r²}(1+q+···+q^{2r})`. -/
noncomputable def alphaA (r : ℕ) : PowerSeries ℤ := (-1) ^ r * X ^ (r ^ 2) * geom (2 * r + 1)

/-- the Bailey summand `αᵣ / ((q;q)_{n-r}(q²;q)_{n+r})`. -/
noncomputable def Fterm (n r : ℕ) : PowerSeries ℤ := alphaA r * Bfac (n - r) (n + r)

/-- the telescoping certificate `G(n,r)`. -/
noncomputable def Gterm (n r : ℕ) : PowerSeries ℤ :=
  (-1) ^ (r + 1) * X ^ (n + r * (r - 1)) * geom (2 * r)
    * ((1 - X ^ (n + r + 1)) * Bfac (n - r) (n + r))

/-- **The creative-telescoping step** (`r < n`, here `n = r+1+d`):
`(1-q^{2n})·F(n,r) - F(n-1,r) = G(n,r+1) - G(n,r)`. -/
lemma lemA (r d : ℕ) :
    (1 - X ^ (2 * (r + 1 + d))) * Fterm (r + 1 + d) r - Fterm (r + d) r
      = Gterm (r + 1 + d) (r + 1) - Gterm (r + 1 + d) r := by
  simp only [Fterm, Gterm, alphaA]
  rw [show (r + 1 + d) + r + 1 = 2 * r + d + 2 from by omega,
      show (r + 1 + d) + (r + 1) + 1 = 2 * r + d + 3 from by omega,
      show (r + 1 + d) - r = d + 1 from by omega, show (r + 1 + d) + r = 2 * r + 1 + d from by omega,
      show (r + d) - r = d from by omega, show (r + d) + r = 2 * r + d from by omega,
      show (r + 1 + d) - (r + 1) = d from by omega, show (r + 1 + d) + (r + 1) = 2 * r + d + 2 from by omega,
      Bfac_prev r d, Bfac_next r d, hsq r, hnext' r,
      show 2 * (r + 1) = 2 * r + 2 from by omega,
      geom_eq (2 * r + 1), geom_eq (2 * r), geom_eq (2 * r + 2)]
  simp only [two_mul, pow_add, pow_succ]
  ring

/-- boundary: `G(n,0) = 0` (empty geometric sum). -/
lemma G_zero (n : ℕ) : Gterm n 0 = 0 := by simp [Gterm, geom]

/-- **The top-term identity** (`r = n`): `(1-q^{2n})·F(n,n) = -G(n,n)`. -/
lemma lemB (n : ℕ) : (1 - X ^ (2 * n)) * Fterm n n = - Gterm n n := by
  simp only [Fterm, Gterm, alphaA]
  rw [show n + n + 1 = 2 * n + 1 from by omega, show n - n = 0 from by omega,
      show n + n = 2 * n from by omega, hsq n,
      show n + n * (n - 1) = n * (n - 1) + n from by ring,
      geom_eq (2 * n + 1), geom_eq (2 * n)]
  simp only [two_mul, pow_add, pow_succ]
  ring

/-- `(q²;q²)_n = ∏_{k<n}(1 − q^{2k+2})` — the Bailey `β` denominator for Identity A. -/
noncomputable def q2q2 (n : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range n, (1 - X ^ (2 * k + 2))

lemma q2q2_succ (m : ℕ) : q2q2 (m + 1) = q2q2 m * (1 - X ^ (2 * m + 2)) := by
  rw [q2q2, Finset.prod_range_succ, ← q2q2]

lemma isUnit_q2q2 (n : ℕ) : IsUnit (q2q2 n) := by
  rw [isUnit_iff_constantCoeff, q2q2, map_prod,
      Finset.prod_eq_one (fun x _ => by
        rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero])]
  exact isUnit_one

/-- the `q^{n²+n}`-Bailey partial sum `S(n) = Σ_{r≤n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r})`. -/
noncomputable def Ssum (n : ℕ) : PowerSeries ℤ := ∑ r ∈ Finset.range (n + 1), Fterm n r

/-- **The first-order recurrence** `(1-q^{2(m+1)})·S(m+1) = S(m)` — the telescoped creative-telescoping. -/
lemma Ssum_rec (m : ℕ) : (1 - X ^ (2 * (m + 1))) * Ssum (m + 1) = Ssum m := by
  simp only [Ssum]
  rw [Finset.mul_sum, Finset.sum_range_succ, lemB (m + 1)]
  have hterm : ∀ r ∈ Finset.range (m + 1),
      (1 - X ^ (2 * (m + 1))) * Fterm (m + 1) r
        = Fterm m r + (Gterm (m + 1) (r + 1) - Gterm (m + 1) r) := by
    intro r hr
    rw [Finset.mem_range] at hr
    have h := lemA r (m - r)
    rw [show r + 1 + (m - r) = m + 1 from by omega, show r + (m - r) = m from by omega] at h
    linear_combination h
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_range_sub (fun r => Gterm (m + 1) r), G_zero]
  ring

/-- **`S(n) = 1/(q²;q²)_n`** — the finite `a=q` Bailey identity for Identity A, by induction. -/
lemma Ssum_eq (n : ℕ) : Ssum n = Ring.inverse (q2q2 n) := by
  induction n with
  | zero => simp [Ssum, Fterm, alphaA, Bfac, geom, q2q2, qfac, q2fac]
  | succ m ih =>
      have hrec := Ssum_rec m
      rw [ih] at hrec
      have hunit : q2q2 (m + 1) * Ssum (m + 1) = 1 := by
        rw [q2q2_succ, mul_assoc, show 2 * m + 2 = 2 * (m + 1) from by omega, hrec,
            Ring.mul_inverse_cancel _ (isUnit_q2q2 m)]
      calc Ssum (m + 1)
          = Ring.inverse (q2q2 (m + 1)) * (q2q2 (m + 1) * Ssum (m + 1)) := by
            rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_q2q2 (m + 1)), one_mul]
        _ = Ring.inverse (q2q2 (m + 1)) := by rw [hunit, mul_one]

/-- **The `a=q` Bailey pair for Identity A**: `(αₙ = (−1)ⁿ q^{n²}(1+···+q^{2n}), βₙ = 1/(q²;q²)_n)`. -/
theorem isBaileyPairQ_A : IsBaileyPairQ alphaA (fun n => Ring.inverse (q2q2 n)) := by
  intro n
  show Ring.inverse (q2q2 n) = _
  rw [← Ssum_eq n, Ssum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fterm, Bfac, ← mul_assoc]

end MockTheta5.Bailey

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- **Identity A through the `a=q` engine**: feeding the Bailey pair `isBaileyPairQ_A` into
`bailey_transform_q` yields `Σ_{n≥0} q^{n²+n}/(q²;q²)_n = (1/(q²;q)_∞)·Σ_{n≥0} q^{n²+n}·αₙ`
(with `1/(q²;q)_∞ = (1−q)·partitionGF`). -/
theorem identityA_transform :
    tsumQsqQ (fun n => Ring.inverse (q2q2 n)) = (1 - X) * partitionGF * tsumQsqQ alphaA :=
  bailey_transform_q isBaileyPairQ_A

end MockTheta5.JTP
