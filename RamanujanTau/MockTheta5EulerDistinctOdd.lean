/-
# Euler's "distinct = odd" theorem (generating-function heart)

`∏_{n≥1}(1+qⁿ) · (q;q)_∞ = (q²;q²)_∞`, equivalently `∏_{n≥1}(1+qⁿ) = (q²;q²)_∞/(q;q)_∞ = 1/(q;q²)_∞`.

The left side `∏(1+qⁿ)` generates partitions into **distinct** parts; `1/(q;q²)_∞ = 1/∏(1−q^{2n−1})`
generates partitions into **odd** parts — so the identity is Euler's theorem that these are equinumerous.

The proof is the factorwise pairing `(1+qᵏ)(1−qᵏ) = 1−q^{2k}` (`qfacPos_mul_qfac`), lifted to the infinite
products by coefficient stabilization (the same divisibility argument as `(q;q)_∞`). No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiL8

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- the finite product `∏_{k<m}(1 + q^{k+1})` (generating distinct partitions with parts `≤ m`). -/
noncomputable def qfacPos (m : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range m, (1 + X ^ (k + 1))

lemma qfacPos_succ (m : ℕ) : qfacPos (m + 1) = qfacPos m * (1 + X ^ (m + 1)) := by
  rw [qfacPos, qfacPos, Finset.prod_range_succ]

/-- the `q^k` coefficient of `∏_{n≤N}(1+qⁿ)` stabilizes once `N > k`. -/
lemma coeff_qfacPos_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (qfacPos N) = coeff k (qfacPos M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [qfacPos_succ, mul_add, mul_one, map_add]
        have hz : coeff k (qfacPos N * X ^ (N + 1)) = 0 := by
          rw [mul_comm]; exact MockTheta5.mt_coeff_Xpow_mul_zero (qfacPos N) (N + 1) k (by omega)
        rw [hz, add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{n≥1}(1+qⁿ)`** as a formal power series (distinct-partition generating function). -/
noncomputable def prodOnePlus : PowerSeries ℤ := mk fun k => coeff k (qfacPos (k + 1))

lemma coeff_prodOnePlus {k N : ℕ} (hN : k + 1 ≤ N) : coeff k prodOnePlus = coeff k (qfacPos N) := by
  rw [prodOnePlus, coeff_mk, coeff_qfacPos_stable (Nat.lt_succ_self k) hN]

/-- finite pairing `∏(1+qᵏ)·∏(1−qᵏ) = ∏(1−q^{2k}) = E2(∏(1−qᵏ))`. -/
lemma qfacPos_mul_qfac (m : ℕ) : qfacPos m * qfac m = E2 (qfac m) := by
  have hL : qfacPos m * qfac m = ∏ k ∈ Finset.range m, (1 - X ^ (2 * (k + 1)) : PowerSeries ℤ) := by
    rw [qfacPos, qfac, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by ring
  have hR : E2 (qfac m) = ∏ k ∈ Finset.range m, (1 - X ^ (2 * (k + 1)) : PowerSeries ℤ) := by
    rw [qfac, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_sub, map_one, map_pow, E2_X, ← pow_mul]
  rw [hL, hR]

/-- **Euler's distinct = odd (generating-function form): `∏_{n≥1}(1+qⁿ) · (q;q)_∞ = (q²;q²)_∞`.**
Equivalently `∏(1+qⁿ) = (q²;q²)_∞/(q;q)_∞ = 1/(q;q²)_∞` — distinct parts ↔ odd parts. -/
theorem prodOnePlus_mul_qfacInf : prodOnePlus * qfacInf = qfac2Inf := by
  ext N
  have h1 : coeff N (prodOnePlus * qfacInf) = coeff N (qfacPos (N + 1) * qfac (N + 1)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_prodOnePlus (show p.1 + 1 ≤ N + 1 by omega),
        coeff_qfacInf (show p.2 + 1 ≤ N + 1 by omega)]
  rw [h1, qfacPos_mul_qfac]
  have hdvd : (X : PowerSeries ℤ) ^ (N + 1) ∣ (qfac (N + 1) - qfacInf) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, coeff_qfacInf (show i + 1 ≤ N + 1 by omega), sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have hz : coeff N (E2 (qfac (N + 1))) - coeff N qfac2Inf = 0 := by
    rw [← map_sub, qfac2Inf, ← map_sub, hg, map_mul, E2_X_pow]
    exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ N (by omega)
  exact sub_eq_zero.mp hz

/-- the distinct-partition generating function as `(q²;q²)_∞ · (partition gen. func.)`. -/
theorem prodOnePlus_eq : prodOnePlus = qfac2Inf * partitionGF := by
  rw [partitionGF, ← prodOnePlus_mul_qfacInf, mul_assoc, Ring.mul_inverse_cancel _ isUnit_qfacInf,
      mul_one]

end MockTheta5.JTP
