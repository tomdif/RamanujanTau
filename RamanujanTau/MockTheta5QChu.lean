/-
# Bailey campaign, Tier 2c: the q-Chu–Vandermonde core of Bailey's lemma

The limiting Bailey-chain step (`MockTheta5BaileyLemma`) was pinned to one identity, `bailey_inner`:
`Σ_{i≤m} q^{i²+2ri}·[m,i]_q·(q^{2r+i+1};q)_{m-i} = 1`. This file proves it.

The key idea: `bailey_inner m r` is the `b = 2r` case of a more general statement `F m b = 1`, where
`F m b = Σ_{i≤m} q^{i²+b·i}·[m,i]_q·(q^{b+i+1};q)_{m-i}`. The generalized `F` satisfies a clean two-term
recurrence `F (m+1) b = (1 - q^{b+m+1})·F m b + q^{b+m+1}·F m (b+1)`, which makes `F m b = 1` fall out by
induction on `m` for ALL `b` simultaneously (`(1-x)·1 + x·1 = 1`).

The recurrence needs the *other* q-Pascal rule (`gaussBinom_pascal1`), whose crux is the multiplicative
ratio relation `gaussBinom_ratio`. Those are proved first. No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyLemma
import Mathlib.Tactic.LinearCombination

namespace MockTheta5.Bailey
open PowerSeries

/-- `(1 - q)·(1 + q + q² + ⋯ + qᵐ) = 1 - q^{m+1}` (finite geometric series). -/
lemma geomX (m : ℕ) :
    (1 - X) * (1 + X * ∑ j ∈ Finset.range m, (X : PowerSeries ℤ) ^ j) = 1 - X ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ihm => rw [Finset.sum_range_succ]; linear_combination ihm

/-- The multiplicative ratio relation `(1-q^{i+1})·[m,i+1]_q = (1-q^{m-i})·[m,i]_q`. The real obstruction
behind the second q-Pascal rule; proved by induction on `m` using the first q-Pascal rule. -/
theorem gaussBinom_ratio (m i : ℕ) :
    (1 - X ^ (i + 1)) * gaussBinom m (i + 1) = (1 - X ^ (m - i)) * gaussBinom m i := by
  induction m generalizing i with
  | zero => cases i <;> simp [gaussBinom]
  | succ m ih =>
      cases i with
      | zero =>
          simp only [gaussBinom_succ_succ, gaussBinom_zero_right, Nat.sub_zero, zero_add,
            pow_one, mul_one]
          rw [gaussBinom_one]
          exact geomX m
      | succ i =>
          by_cases hmi : i + 1 ≤ m
          · rw [gaussBinom_succ_succ, gaussBinom_succ_succ]
            have e1 := ih i
            have e2 := ih (i + 1)
            have hsub : m + 1 - (i + 1) = m - i := by omega
            have hsub2 : m - (i + 1) = m - i - 1 := by omega
            rw [hsub2] at e2
            have p1 : (X : PowerSeries ℤ) ^ (i + 1 + 1) * X ^ (m - i - 1) = X ^ (m + 1) := by
              rw [← pow_add]; congr 1; omega
            have p2 : (X : PowerSeries ℤ) ^ (i + 1) * X ^ (m - i) = X ^ (m + 1) := by
              rw [← pow_add]; congr 1; omega
            rw [hsub]
            linear_combination X ^ (i + 1 + 1) * e2 + e1
              + gaussBinom m (i + 1) * p2 - gaussBinom m (i + 1) * p1
          · push_neg at hmi
            have v1 : gaussBinom m (i + 1) = 0 := gaussBinom_eq_zero_of_lt (by omega)
            have v2 : gaussBinom m (i + 1 + 1) = 0 := gaussBinom_eq_zero_of_lt (by omega)
            rw [gaussBinom_succ_succ, gaussBinom_succ_succ, v1, v2]
            rcases Nat.lt_or_ge m i with h | h
            · rw [gaussBinom_eq_zero_of_lt h]; simp
            · have hmi2 : m = i := by omega
              subst hmi2; simp

/-- The second q-Pascal rule `[m+1,i+1]_q = [m,i+1]_q + q^{m-i}·[m,i]_q`, from the ratio relation. -/
lemma gaussBinom_pascal1 (m i : ℕ) :
    gaussBinom (m + 1) (i + 1) = gaussBinom m (i + 1) + X ^ (m - i) * gaussBinom m i := by
  rw [gaussBinom_succ_succ]
  linear_combination -gaussBinom_ratio m i

/-- The generalized q-Chu–Vandermonde sum `F m b = Σ_{i≤m} q^{i²+b·i}·[m,i]_q·(q^{b+i+1};q)_{m-i}`.
`bailey_inner` is the `b = 2r` case; generalizing `b` is exactly what makes the induction close. -/
noncomputable def F (m b : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range (m + 1), X ^ (i ^ 2 + b * i) * gaussBinom m i * rfac (b + i) (m - i)

/-- Multiplying `F m b` by `(1 - q^{b+m+1})` extends each `rfac` length by one (the factor is the same,
`q^{b+m+1}`, for every term). -/
lemma F_mul (m b : ℕ) :
    (1 - X ^ (b + m + 1)) * F m b
      = ∑ i ∈ Finset.range (m + 1),
          X ^ (i ^ 2 + b * i) * gaussBinom m i * rfac (b + i) (m + 1 - i) := by
  rw [F, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hlen : m + 1 - i = (m - i) + 1 := by omega
  rw [hlen, rfac_succ]
  have he : b + i + (m - i) + 1 = b + m + 1 := by omega
  rw [he]; ring

/-- The `q^{m-i}·[m,i]_q` half of the q-Pascal split reindexes to `q^{b+m+1}·F m (b+1)`. -/
lemma Qpart_eq (m b : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
        X ^ ((i + 1) ^ 2 + b * (i + 1)) * (X ^ (m - i) * gaussBinom m i) * rfac (b + i + 1) (m - i))
      = X ^ (b + m + 1) * F m (b + 1) := by
  rw [F, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  obtain ⟨d, rfl⟩ : ∃ d, m = i + d := ⟨m - i, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  rw [show b + i + 1 = b + 1 + i from by ring]
  ring

/-- **The Bailey-chain recurrence** `F (m+1) b = (1 - q^{b+m+1})·F m b + q^{b+m+1}·F m (b+1)`,
from the second q-Pascal rule + `rfac` telescoping. This is what makes `F m b = 1` close. -/
lemma F_rec (m b : ℕ) :
    F (m + 1) b = (1 - X ^ (b + m + 1)) * F m b + X ^ (b + m + 1) * F m (b + 1) := by
  rw [F_mul, ← Qpart_eq, F, Finset.sum_range_succ']
  have hsplit : (∑ i ∈ Finset.range (m + 1),
        X ^ ((i+1)^2 + b*(i+1)) * gaussBinom (m+1) (i+1) * rfac (b+(i+1)) (m+1-(i+1)))
      = (∑ i ∈ Finset.range (m + 1),
          X ^ ((i+1)^2 + b*(i+1)) * gaussBinom m (i+1) * rfac (b+i+1) (m-i))
        + (∑ i ∈ Finset.range (m + 1),
          X ^ ((i+1)^2 + b*(i+1)) * (X^(m-i) * gaussBinom m i) * rfac (b+i+1) (m-i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hlen : m + 1 - (i+1) = m - i := by omega
    have harg : b + (i+1) = b + i + 1 := by ring
    rw [hlen, harg, gaussBinom_pascal1]; ring
  rw [hsplit]
  have ht0 : X ^ (0^2 + b*0) * gaussBinom (m+1) 0 * rfac (b+0) (m+1-0) = rfac b (m+1) := by simp
  rw [ht0]
  have hP : (∑ i ∈ Finset.range (m + 1),
        X ^ ((i+1)^2 + b*(i+1)) * gaussBinom m (i+1) * rfac (b+i+1) (m-i)) + rfac b (m+1)
      = ∑ i ∈ Finset.range (m + 1), X ^ (i^2 + b*i) * gaussBinom m i * rfac (b+i) (m+1-i) := by
    conv_rhs => rw [Finset.sum_range_succ']
    conv_lhs => rw [Finset.sum_range_succ]
    rw [gaussBinom_eq_zero_of_lt (Nat.lt_succ_self m)]
    have hs0 : X ^ (0^2 + b*0) * gaussBinom m 0 * rfac (b+0) (m+1-0) = rfac b (m+1) := by simp
    rw [hs0]
    have hbody : ∀ i ∈ Finset.range m,
        X ^ ((i+1)^2 + b*(i+1)) * gaussBinom m (i+1) * rfac (b+i+1) (m-i)
        = X ^ ((i+1)^2 + b*(i+1)) * gaussBinom m (i+1) * rfac (b+(i+1)) (m+1-(i+1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have : m + 1 - (i+1) = m - i := by omega
      rw [this, show b + (i+1) = b + i + 1 from by ring]
    rw [Finset.sum_congr rfl hbody]
    ring
  linear_combination hP

/-- `F m b = 1` for ALL `m, b` — by induction on `m` via `F_rec` (`(1-x)·1 + x·1 = 1`). -/
theorem F_eq_one (m b : ℕ) : F m b = 1 := by
  induction m generalizing b with
  | zero => simp [F, rfac]
  | succ m ih => rw [F_rec, ih, ih]; ring

/-- **The finite q-Chu–Vandermonde identity** powering (limiting) Bailey's lemma:
`Σ_{i≤m} q^{i²+2ri}·[m,i]_q·(q^{2r+i+1};q)_{m-i} = 1`. The `b = 2r` case of `F_eq_one`. -/
theorem bailey_inner (m r : ℕ) :
    ∑ i ∈ Finset.range (m + 1),
      X ^ (i ^ 2 + 2 * r * i) * gaussBinom m i * rfac (2 * r + i) (m - i) = 1 := by
  have h := F_eq_one m (2 * r)
  rwa [F] at h

end MockTheta5.Bailey
