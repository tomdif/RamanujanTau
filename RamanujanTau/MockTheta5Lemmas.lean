import RamanujanTau.MockTheta5Series

/-! # 5th-order mock theta — layer-1 lemmas (proofworld-proposed, kernel-verified)

q-Pochhammer building blocks over `PowerSeries ℤ`, toward the infinite identities. Each PROOF was
proposed by the proofworld loop and accepted by the Lean kernel; nothing unproven appears here. -/

namespace MockTheta5
open PowerSeries

theorem mt_qpoch_one (a : PowerSeries ℤ) : qpoch a 1 = 1 - a := by simp [qpoch_succ]

theorem mt_qpoch_inv_cancel (a : PowerSeries ℤ) (ha : constantCoeff a = 0) (n : ℕ) : Ring.inverse (qpoch a n) * qpoch a n = 1 := by exact Ring.inverse_mul_cancel _ (isUnit_qpoch a ha n)

theorem mt_qpoch_mul_inv (a : PowerSeries ℤ) (ha : constantCoeff a = 0) (n : ℕ) : qpoch a n * Ring.inverse (qpoch a n) = 1 := by exact Ring.mul_inverse_cancel _ (isUnit_qpoch a ha n)

theorem mt_qpoch_split (a : PowerSeries ℤ) (m n : ℕ) : qpoch a (m + n) = qpoch a m * qpoch (a * X ^ m) n := by induction n with | zero => simp | succ k ih => rw [Nat.add_succ, qpoch_succ, qpoch_succ, ih, pow_add]; ring

theorem mt_coeff_Xpow_mul_zero (φ : PowerSeries ℤ) (j k : ℕ) (h : k < j) : coeff k ((X : PowerSeries ℤ) ^ j * φ) = 0 := by rw [coeff_X_pow_mul', if_neg (Nat.not_le.mpr h)]

theorem mt_coeff_sum_eq (f : ℕ → PowerSeries ℤ) (k : ℕ) (hf : ∀ n, k < n → coeff k (f n) = 0) (M : ℕ) (hM : k + 1 ≤ M) : coeff k (∑ n ∈ Finset.range M, f n) = ∑ n ∈ Finset.range (k + 1), coeff k (f n) := by rw [map_sum]; symm; apply Finset.sum_subset (by intro x hx; exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hM)); intro n _ hn; exact hf n (by simp only [Finset.mem_range, not_lt] at hn; omega)

end MockTheta5
