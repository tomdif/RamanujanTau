/-
# The `a = q` Bailey chain (the mock-theta engine)

The `a = 1` Bailey machinery (`IsBaileyPair`, `isBaileyPair_chain`, `bailey_transform`) powers Rogers–
Ramanujan but is **inert** on the fifth-order mock thetas: the Bailey `α` for `βₙ = (−q;q²)ₙ` has no closed
form there. The mock thetas live in the **`a = q`** Bailey world, with the shifted denominator
`(aq;q)_{n+r} = (q²;q)_{n+r}` (here `q2fac`) in place of `(q;q)_{n+r}`.

This file builds the `a = q` chain in parallel to the `a = 1` chain:

* `IsBaileyPairQ α β`  :  `βₙ = Σ_{r≤n} αᵣ / ((q;q)_{n-r}·(q²;q)_{n+r})`
* seed pair `(δ_{·,0}, 1/((q;q)ₙ(q²;q)ₙ))` (`isBaileyPairQ_seed`)
* chain step `α'ₙ = q^{n²+n}αₙ`, `β'ₙ = Σ_{j≤n} q^{j²+j}/(q;q)_{n-j}·βⱼ` (`chainAlphaQ`/`chainBetaQ`)
* **`isBaileyPairQ_chain`** : the chain step preserves `a = q` Bailey pairs.

The hard q-Chu–Vandermonde core is **shared** with `a = 1`: `F_eq_one m b = 1` holds for *all* `b`, so the
`a = q` inner identity is simply the **odd** case `b = 2r+1` (`bailey_inner_q`) of the same `F`, versus the
even case `b = 2r` used by `a = 1`. The `(q²;q)` factors are converted to `(q;q)` by the one-step relation
`(q;q)_{k+1} = (q²;q)_k·(1−q)` (`qfac_succ_eq_q2fac`). No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyChain

namespace MockTheta5.Bailey
open PowerSeries

/-- `(q²;q)_n = ∏_{k<n}(1 − q^{k+2})` — the `(aq;q)_n` factor for the base case `a = q`. -/
noncomputable def q2fac (n : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range n, (1 - X ^ (k + 2))

/-- A **Bailey pair relative to `a = q`**: `βₙ = Σ_{r≤n} αᵣ / ((q;q)_{n-r}·(q²;q)_{n+r})`. -/
def IsBaileyPairQ (α β : ℕ → PowerSeries ℤ) : Prop :=
  ∀ n, β n = ∑ r ∈ Finset.range (n + 1),
    α r * Ring.inverse (qfac (n - r)) * Ring.inverse (q2fac (n + r))

/-- seed pair (`a = q`): `αₙ = δ_{n,0}`. -/
noncomputable def seedAlphaQ (n : ℕ) : PowerSeries ℤ := if n = 0 then 1 else 0
/-- seed pair (`a = q`): `βₙ = 1/((q;q)ₙ (q²;q)ₙ)`. -/
noncomputable def seedBetaQ (n : ℕ) : PowerSeries ℤ := Ring.inverse (qfac n) * Ring.inverse (q2fac n)

/-- The seed pair `(δ_{·,0}, 1/((q;q)·(q²;q)·))` is an `a = q` Bailey pair — the base of the chain. -/
theorem isBaileyPairQ_seed : IsBaileyPairQ seedAlphaQ seedBetaQ := by
  intro n
  rw [seedBetaQ, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos n))
        (fun r _ hr => by simp [seedAlphaQ, hr])]
  simp [seedAlphaQ]

/-- **`a = q` chain step on α** (limiting form): `α'ₙ = aⁿq^{n²}·αₙ = q^{n²+n}·αₙ`. -/
noncomputable def chainAlphaQ (α : ℕ → PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ := X ^ (n ^ 2 + n) * α n

/-- **`a = q` chain step on β** (limiting form): `β'ₙ = Σ_{j≤n} q^{j²+j}/(q;q)_{n-j}·βⱼ`. -/
noncomputable def chainBetaQ (β : ℕ → PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  ∑ j ∈ Finset.range (n + 1), X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * β j

/-- `(q;q)_{k+1} = (q²;q)_k · (1 − q)`: the one-step shift relating the two Pochhammer families. -/
lemma qfac_succ_eq_q2fac (k : ℕ) : qfac (k + 1) = q2fac k * (1 - X) := by
  rw [qfac, Finset.prod_range_succ', q2fac]; simp [pow_succ]

/-- The `a = q` inner identity: `bailey_inner` at the **odd** parameter `b = 2r+1`, from `F_eq_one`. -/
lemma bailey_inner_q (m r : ℕ) :
    ∑ i ∈ Finset.range (m + 1),
      X ^ (i ^ 2 + (2 * r + 1) * i) * gaussBinom m i * rfac (2 * r + 1 + i) (m - i) = 1 := by
  have h := F_eq_one m (2 * r + 1); rwa [F] at h

/-- inverse form of `bailey_inner_q`: `Σ_i q^{i²+(2r+1)i}·(q;q)_i⁻¹(q;q)_{m-i}⁻¹(q;q)_{2r+1+i}⁻¹
= (q;q)_m⁻¹·(q;q)_{2r+1+m}⁻¹`. -/
lemma inner_inv_q (m r : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
        X ^ (i ^ 2 + (2 * r + 1) * i) * Ring.inverse (qfac i) * Ring.inverse (qfac (m - i))
          * Ring.inverse (qfac (2 * r + 1 + i)))
      = Ring.inverse (qfac m) * Ring.inverse (qfac (2 * r + 1 + m)) := by
  have hb := bailey_inner_q m r
  have hrw : (∑ i ∈ Finset.range (m + 1),
        X ^ (i ^ 2 + (2 * r + 1) * i) * gaussBinom m i * rfac (2 * r + 1 + i) (m - i))
      = (qfac m * qfac (2 * r + 1 + m)) * (∑ i ∈ Finset.range (m + 1),
          X ^ (i ^ 2 + (2 * r + 1) * i) * Ring.inverse (qfac i) * Ring.inverse (qfac (m - i))
            * Ring.inverse (qfac (2 * r + 1 + i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [gaussBinom_eq_inv m i (by omega), rfac_eq_inv,
        show 2 * r + 1 + i + (m - i) = 2 * r + 1 + m from by omega]
    ring
  rw [hrw] at hb
  have heq : (qfac m * qfac (2 * r + 1 + m))
      * (Ring.inverse (qfac m) * Ring.inverse (qfac (2 * r + 1 + m))) = 1 := by
    rw [show (qfac m * qfac (2*r+1+m)) * (Ring.inverse (qfac m) * Ring.inverse (qfac (2*r+1+m)))
          = (qfac m * Ring.inverse (qfac m)) * (qfac (2*r+1+m) * Ring.inverse (qfac (2*r+1+m)))
          from by ring,
        Ring.mul_inverse_cancel (qfac m) (isUnit_qfac m),
        Ring.mul_inverse_cancel (qfac (2*r+1+m)) (isUnit_qfac (2*r+1+m)), mul_one]
  exact mul_left_cancel₀ (((isUnit_qfac m).mul (isUnit_qfac (2*r+1+m))).ne_zero) (hb.trans heq.symm)

/-- `(q²;q)_k` is a unit (constant term `1`). -/
lemma isUnit_q2fac (k : ℕ) : IsUnit (q2fac k) := by
  rw [isUnit_iff_constantCoeff, q2fac, map_prod,
      Finset.prod_eq_one (fun x _ => by
        rw [map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero])]
  exact isUnit_one

/-- inverse of `(q²;q)_k` via the shift: `(q²;q)_k⁻¹ = (1−q)·(q;q)_{k+1}⁻¹`. -/
lemma inv_q2fac (k : ℕ) : Ring.inverse (q2fac k) = (1 - X) * Ring.inverse (qfac (k + 1)) := by
  have h1 : q2fac k * ((1 - X) * Ring.inverse (qfac (k + 1))) = 1 := by
    rw [← mul_assoc, ← qfac_succ_eq_q2fac, Ring.mul_inverse_cancel _ (isUnit_qfac (k + 1))]
  calc Ring.inverse (q2fac k)
      = Ring.inverse (q2fac k) * (q2fac k * ((1 - X) * Ring.inverse (qfac (k + 1)))) := by
        rw [h1, mul_one]
    _ = (Ring.inverse (q2fac k) * q2fac k) * ((1 - X) * Ring.inverse (qfac (k + 1))) := by ring
    _ = (1 - X) * Ring.inverse (qfac (k + 1)) := by
        rw [Ring.inverse_mul_cancel _ (isUnit_q2fac k), one_mul]

/-- The inner Bailey-chain sum in the pure-`(q;q)` form (`(q²;q)` cleared to `(q;q)_{·+1}`). -/
lemma inner_chain_q_reduced (n r : ℕ) (hr : r ≤ n) :
    (∑ j ∈ Finset.Ico r (n + 1),
        X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * Ring.inverse (qfac (j - r))
          * Ring.inverse (qfac (j + r + 1)))
      = X ^ (r ^ 2 + r) * Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r + 1)) := by
  have hkey := inner_inv_q (n - r) r
  rw [show 2 * r + 1 + (n - r) = n + r + 1 from by omega] at hkey
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - r = (n - r) + 1 from by omega,
      show X ^ (r ^ 2 + r) * Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r + 1))
        = X ^ (r ^ 2 + r) * (Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r + 1))) from by ring,
      ← hkey, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [show n - (r + i) = (n - r) - i from by omega, show r + i - r = i from by omega,
      show r + i + r + 1 = 2 * r + 1 + i from by omega,
      show (r + i) ^ 2 + (r + i) = (r ^ 2 + r) + (i ^ 2 + (2 * r + 1) * i) from by ring, pow_add]
  ring

/-- The inner Bailey-chain sum in the native `(q²;q)` form (evaluated via `inner_chain_q_reduced`). -/
lemma inner_chain_q (n r : ℕ) (hr : r ≤ n) :
    (∑ j ∈ Finset.Ico r (n + 1),
        X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * Ring.inverse (qfac (j - r))
          * Ring.inverse (q2fac (j + r)))
      = X ^ (r ^ 2 + r) * Ring.inverse (qfac (n - r)) * Ring.inverse (q2fac (n + r)) := by
  simp only [inv_q2fac]
  rw [show (∑ j ∈ Finset.Ico r (n + 1), X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j))
              * Ring.inverse (qfac (j - r)) * ((1 - X) * Ring.inverse (qfac (j + r + 1))))
        = (1 - X) * (∑ j ∈ Finset.Ico r (n + 1), X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j))
              * Ring.inverse (qfac (j - r)) * Ring.inverse (qfac (j + r + 1)))
      from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring),
      inner_chain_q_reduced n r hr]
  ring

/-- **Limiting Bailey's lemma at `a = q` (unconditional).** The `a = q` chain step preserves `a = q`
Bailey pairs: if `(α,β)` is an `a = q` Bailey pair, then so is `(chainAlphaQ α, chainBetaQ β)`. Iterating
from `isBaileyPairQ_seed` is the `a = q` Bailey chain that reaches the fifth-order mock thetas. -/
theorem isBaileyPairQ_chain {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPairQ α β) :
    IsBaileyPairQ (chainAlphaQ α) (chainBetaQ β) := by
  intro n
  rw [chainBetaQ]
  have step1 : ∀ j ∈ Finset.range (n + 1),
      X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * β j
      = ∑ r ∈ Finset.range (j + 1),
          X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
            * Ring.inverse (q2fac (j + r)) := by
    intro j _; rw [h j, Finset.mul_sum]; exact Finset.sum_congr rfl (fun r _ => by ring)
  have swap : (∑ j ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (j + 1),
        X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
          * Ring.inverse (q2fac (j + r)))
      = ∑ r ∈ Finset.range (n + 1), ∑ j ∈ Finset.Ico r (n + 1),
        X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
          * Ring.inverse (q2fac (j + r)) := by
    apply Finset.sum_comm'; intro j r; simp only [Finset.mem_range, Finset.mem_Ico]; omega
  rw [Finset.sum_congr rfl step1, swap]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  rw [chainAlphaQ,
      show (∑ j ∈ Finset.Ico r (n + 1),
          X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * α r * Ring.inverse (qfac (j - r))
            * Ring.inverse (q2fac (j + r)))
        = α r * ∑ j ∈ Finset.Ico r (n + 1),
          (X ^ (j ^ 2 + j) * Ring.inverse (qfac (n - j)) * Ring.inverse (qfac (j - r))
            * Ring.inverse (q2fac (j + r)))
        from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring),
      inner_chain_q n r (by omega)]
  ring

end MockTheta5.Bailey
