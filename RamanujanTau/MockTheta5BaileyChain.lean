/-
# Bailey campaign, Tier 2 COMPLETE: the (limiting) Bailey's lemma, unconditionally

This file discharges the chain-preservation theorem that `MockTheta5BaileyLemma` left as the remaining goal:

  **`isBaileyPair_chain`:**  `IsBaileyPair α β → IsBaileyPair (chainAlpha α) (chainBeta β)`,

i.e. the limiting (ρ,σ→∞) Bailey chain step `(αₙ, βₙ) ↦ (qⁿ²αₙ, Σ_{j≤n} qʲ²/(q;q)_{n-j}·βⱼ)` really does map
Bailey pairs to Bailey pairs. Iterating it from the seed pair `isBaileyPair_seed` is the Bailey chain.

The proof is the "mechanical" reduction the campaign had deferred: substitute the Bailey relation into
`chainBeta`, swap the triangular double sum, factor out `αᵣ`, and apply the q-Chu–Vandermonde core
(`bailey_inner`/`inner_inv`) to the inner sum. The infrastructure built here:

  * `qfac_succ`, `rfac_mul_qfac` — q-factorial recurrence and `(q^{s+1};q)_t·(q;q)_s = (q;q)_{s+t}`.
  * `gaussBinom_mul_qfac` — the closed form `[m,i]_q·(q;q)_i·(q;q)_{m-i} = (q;q)_m` (induction via q-Pascal).
  * `gaussBinom_eq_inv`, `rfac_eq_inv` — the inverse forms (`Ring.inverse`).
  * `inner_inv` — `bailey_inner` rewritten with inverses (the `(q;q)_m·(q;q)_{2r+m}` unit cancelled).
  * `inner_chain` — the inner sum over `Ico r (n+1)`, reindexed and evaluated via `inner_inv`.

No `sorry`. This closes Tier 2 of the Bailey campaign.
-/
import RamanujanTau.MockTheta5QChu
import Mathlib.Tactic.LinearCombination

namespace MockTheta5.Bailey
open PowerSeries

/-- q-factorial recurrence `(q;q)_{m+1} = (q;q)_m·(1 - q^{m+1})`. -/
lemma qfac_succ (m : ℕ) : qfac (m + 1) = qfac m * (1 - X ^ (m + 1)) := by
  rw [qfac, Finset.prod_range_succ, ← qfac]

/-- `(q^{s+1};q)_t · (q;q)_s = (q;q)_{s+t}`. -/
lemma rfac_mul_qfac (s t : ℕ) : rfac s t * qfac s = qfac (s + t) := by
  induction t with
  | zero => simp
  | succ t ih => rw [rfac_succ, mul_right_comm, ih, ← qfac_succ]; ring_nf

/-- **Closed form of the Gaussian binomial** `[m,i]_q·(q;q)_i·(q;q)_{m-i} = (q;q)_m` for `i ≤ m`. -/
lemma gaussBinom_mul_qfac : ∀ (m i : ℕ), i ≤ m →
    gaussBinom m i * qfac i * qfac (m - i) = qfac m := by
  intro m
  induction m with
  | zero => intro i hi; obtain rfl : i = 0 := Nat.le_zero.mp hi; simp
  | succ m ih =>
      intro i hi
      match i with
      | 0 => simp
      | k + 1 =>
          by_cases hk : k + 1 ≤ m
          · have e1 := ih k (by omega)
            have e2 := ih (k + 1) hk
            have hmsub : m - (k + 1) = m - k - 1 := by omega
            rw [hmsub] at e2
            have hqmk : qfac (m - k) = qfac (m - k - 1) * (1 - X ^ (m - k)) := by
              obtain ⟨d, hd1, hd2⟩ : ∃ d, m - k - 1 = d ∧ m - k = d + 1 := ⟨m - k - 1, rfl, by omega⟩
              rw [hd1, hd2, qfac_succ]
            have p : (X : PowerSeries ℤ) ^ (k + 1) * X ^ (m - k) = X ^ (m + 1) := by
              rw [← pow_add]; congr 1; omega
            rw [gaussBinom_succ_succ, show m + 1 - (k + 1) = m - k from by omega,
                qfac_succ k, hqmk, qfac_succ m]
            rw [qfac_succ k] at e2
            rw [hqmk] at e1
            linear_combination (1 - X ^ (k + 1)) * e1
              + X ^ (k + 1) * (1 - X ^ (m - k)) * e2 - qfac m * p
          · have hi2 : k + 1 = m + 1 := by omega
            rw [hi2]; simp [gaussBinom_self, qfac_succ]

/-- Inverse form of the closed formula: `[m,i]_q = (q;q)_m·(q;q)_i⁻¹·(q;q)_{m-i}⁻¹` for `i ≤ m`. -/
lemma gaussBinom_eq_inv (m i : ℕ) (h : i ≤ m) :
    gaussBinom m i = qfac m * Ring.inverse (qfac i) * Ring.inverse (qfac (m - i)) := by
  have key := gaussBinom_mul_qfac m i h
  have h1 : gaussBinom m i * qfac i * qfac (m - i)
        * (Ring.inverse (qfac i) * Ring.inverse (qfac (m - i)))
      = qfac m * (Ring.inverse (qfac i) * Ring.inverse (qfac (m - i))) := by rw [key]
  rw [show gaussBinom m i * qfac i * qfac (m - i) * (Ring.inverse (qfac i) * Ring.inverse (qfac (m - i)))
        = gaussBinom m i * (qfac i * Ring.inverse (qfac i)) * (qfac (m - i) * Ring.inverse (qfac (m - i)))
        from by ring,
      Ring.mul_inverse_cancel (qfac i) (isUnit_qfac i),
      Ring.mul_inverse_cancel (qfac (m - i)) (isUnit_qfac (m - i)), mul_one, mul_one] at h1
  rw [h1]; ring

/-- Inverse form of `rfac`: `(q^{s+1};q)_t = (q;q)_{s+t}·(q;q)_s⁻¹`. -/
lemma rfac_eq_inv (s t : ℕ) : rfac s t = qfac (s + t) * Ring.inverse (qfac s) := by
  have key := rfac_mul_qfac s t
  have h1 : rfac s t * qfac s * Ring.inverse (qfac s) = qfac (s + t) * Ring.inverse (qfac s) := by rw [key]
  rwa [mul_assoc, Ring.mul_inverse_cancel (qfac s) (isUnit_qfac s), mul_one] at h1

/-- `bailey_inner` in inverse form: `Σ_i q^{i²+2ri}·(q;q)_i⁻¹·(q;q)_{m-i}⁻¹·(q;q)_{2r+i}⁻¹
= (q;q)_m⁻¹·(q;q)_{2r+m}⁻¹` (the unit `(q;q)_m·(q;q)_{2r+m}` cancelled). -/
lemma inner_inv (m r : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
        X ^ (i ^ 2 + 2 * r * i) * Ring.inverse (qfac i) * Ring.inverse (qfac (m - i))
          * Ring.inverse (qfac (2 * r + i)))
      = Ring.inverse (qfac m) * Ring.inverse (qfac (2 * r + m)) := by
  have hb := bailey_inner m r
  have hrw : (∑ i ∈ Finset.range (m + 1),
        X ^ (i ^ 2 + 2 * r * i) * gaussBinom m i * rfac (2 * r + i) (m - i))
      = (qfac m * qfac (2 * r + m)) * (∑ i ∈ Finset.range (m + 1),
          X ^ (i ^ 2 + 2 * r * i) * Ring.inverse (qfac i) * Ring.inverse (qfac (m - i))
            * Ring.inverse (qfac (2 * r + i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gaussBinom_eq_inv m i (by omega), rfac_eq_inv, show 2 * r + i + (m - i) = 2 * r + m from by omega]
    ring
  rw [hrw] at hb
  have heq : (qfac m * qfac (2 * r + m))
      * (Ring.inverse (qfac m) * Ring.inverse (qfac (2 * r + m))) = 1 := by
    rw [show (qfac m * qfac (2 * r + m)) * (Ring.inverse (qfac m) * Ring.inverse (qfac (2 * r + m)))
          = (qfac m * Ring.inverse (qfac m)) * (qfac (2 * r + m) * Ring.inverse (qfac (2 * r + m)))
          from by ring,
        Ring.mul_inverse_cancel (qfac m) (isUnit_qfac m),
        Ring.mul_inverse_cancel (qfac (2 * r + m)) (isUnit_qfac (2 * r + m)), mul_one]
  exact mul_left_cancel₀ (((isUnit_qfac m).mul (isUnit_qfac (2 * r + m))).ne_zero) (hb.trans heq.symm)

/-- The inner sum of the Bailey-chain reduction, over `Ico r (n+1)`, evaluated via `inner_inv`. -/
lemma inner_chain (n r : ℕ) (hr : r ≤ n) :
    (∑ j ∈ Finset.Ico r (n + 1),
        X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * Ring.inverse (qfac (j - r))
          * Ring.inverse (qfac (j + r)))
      = X ^ (r ^ 2) * Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r)) := by
  have hkey := inner_inv (n - r) r
  rw [show 2 * r + (n - r) = n + r from by omega] at hkey
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 from by omega,
      show X ^ (r ^ 2) * Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r))
        = X ^ (r ^ 2) * (Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r))) from by ring,
      ← hkey, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [show n - (r + i) = (n - r) - i from by omega, show r + i - r = i from by omega,
      show r + i + r = 2 * r + i from by omega,
      show (r + i) ^ 2 = r ^ 2 + (i ^ 2 + 2 * r * i) from by ring, pow_add]
  ring

/-- **Limiting Bailey's lemma (unconditional).** The Bailey chain step preserves Bailey pairs:
if `(α,β)` is a Bailey pair (relative to `a=1`), then so is `(chainAlpha α, chainBeta β)`. Iterating from
the seed pair `isBaileyPair_seed` is the Bailey chain that generates Rogers–Ramanujan / mock-theta sums. -/
theorem isBaileyPair_chain {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPair α β) :
    IsBaileyPair (chainAlpha α) (chainBeta β) := by
  intro n
  rw [chainBeta]
  have step1 : ∀ j ∈ Finset.range (n + 1),
      X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * β j
      = ∑ r ∈ Finset.range (j + 1),
          X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
            * Ring.inverse (qfac (j + r)) := by
    intro j _
    rw [h j, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _; ring
  have swap : (∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (j + 1),
        X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
          * Ring.inverse (qfac (j + r)))
      = ∑ r ∈ Finset.range (n + 1), ∑ j ∈ Finset.Ico r (n + 1),
        X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
          * Ring.inverse (qfac (j + r)) := by
    apply Finset.sum_comm'
    intro j r; simp only [Finset.mem_range, Finset.mem_Ico]; omega
  rw [Finset.sum_congr rfl step1, swap]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  rw [chainAlpha,
      show (∑ j ∈ Finset.Ico r (n + 1),
          X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
            * Ring.inverse (qfac (j + r)))
        = α r * ∑ j ∈ Finset.Ico r (n + 1),
          (X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * Ring.inverse (qfac (j - r))
            * Ring.inverse (qfac (j + r)))
        from by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring,
      inner_chain n r (by omega)]
  ring

end MockTheta5.Bailey
