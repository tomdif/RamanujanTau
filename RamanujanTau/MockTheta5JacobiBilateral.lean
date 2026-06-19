/-
# Jacobi triple product campaign, Rung 2: the bilateral theta series `Σ_{n∈ℤ} zⁿ q^{n²}`

The right-hand side of the Jacobi triple product is a *bilateral* sum over all integers `n`, with `zⁿ` for
negative `n` too. Since `PowerSeries` is ℕ-indexed, the `z`-variable must live in the coefficient ring as a
**Laurent polynomial** `ℤ[z;z⁻¹] = LaurentPolynomial ℤ` (`z = T 1`, `z⁻¹ = T (-1)`). The series then lives in
`PowerSeries (ℤ[z;z⁻¹])` with `q = X`.

As with `(q;q)_∞` (Rung 1), the bilateral sum is a genuine formal power series via coefficient stabilization:
the paired term `(zᵐ⁺¹ + z⁻⁽ᵐ⁺¹⁾)·q^{(m+1)²}` has `q`-degree `(m+1)²`, so only finitely many terms touch any
fixed coefficient. No `sorry`.

This is Rung 2 of the JTP campaign (Rung 1 = `(q;q)_∞`, this = the bilateral RHS; Rung 3 = the finite/one-sided
JTP from `qbinom` in base `q²`; Rung 4 = the limit assembling the full identity).
-/
import RamanujanTau.MockTheta5JacobiTriple
import Mathlib.Algebra.Polynomial.Laurent

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- The paired `n = ±(m+1)` term of the bilateral theta series: `(zᵐ⁺¹ + z⁻⁽ᵐ⁺¹⁾)·q^{(m+1)²}`. -/
noncomputable def bilatTerm (m : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  X ^ ((m + 1) ^ 2) * PowerSeries.C (T ((m : ℤ) + 1) + T (-((m : ℤ) + 1)))

/-- The finite truncation `Σ_{n=-M}^{M} zⁿ q^{n²}` (the leading `1` is the `n = 0` term). -/
noncomputable def bilatFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  1 + ∑ m ∈ Finset.range M, bilatTerm m

/-- **The bilateral theta series `Σ_{n∈ℤ} zⁿ q^{n²}`**, as a formal power series over `ℤ[z;z⁻¹]`,
defined by coefficient stabilization. This is the right-hand side of the Jacobi triple product. -/
noncomputable def bilateralTheta : PowerSeries (LaurentPolynomial ℤ) :=
  mk fun k => coeff k (bilatFinite (k + 1))

/-- The paired term has `q`-degree `(m+1)²`, so its coefficients below that vanish. -/
lemma coeff_bilatTerm_zero {m k : ℕ} (h : k < (m + 1) ^ 2) : coeff k (bilatTerm m) = 0 := by
  rw [bilatTerm, coeff_X_pow_mul', if_neg (Nat.not_le.mpr h)]

/-- coeff `k` of the truncated sum stabilizes once `M > k`. -/
lemma coeff_bilat_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (bilatFinite N) = coeff k (bilatFinite M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : bilatFinite (N + 1) = bilatFinite N + bilatTerm N := by
          rw [bilatFinite, bilatFinite, Finset.sum_range_succ]; ring
        rw [hsucc, map_add, coeff_bilatTerm_zero (by nlinarith [hkM, h]), add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- coeff `k` of the bilateral theta series equals any finite truncation `Σ_{|n|≤M}` with `M ≥ k+1`. -/
lemma coeff_bilateralTheta {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k bilateralTheta = coeff k (bilatFinite M) := by
  rw [bilateralTheta, coeff_mk, coeff_bilat_stable (Nat.lt_succ_self k) hM]

/-- The constant term is `1` (the `n = 0` term). -/
@[simp] lemma coeff_zero_bilateralTheta : coeff 0 bilateralTheta = 1 := by
  rw [coeff_bilateralTheta (le_refl 1), bilatFinite, Finset.sum_range_one, map_add,
      coeff_bilatTerm_zero (by norm_num)]
  simp

/-- Correctness sanity check: the `q¹` coefficient is `z + z⁻¹` (the `n = ±1` terms). -/
lemma coeff_one_bilateralTheta : coeff 1 bilateralTheta = T 1 + T (-1) := by
  rw [coeff_bilateralTheta (show 1 + 1 ≤ 2 from le_refl 2), bilatFinite,
      Finset.sum_range_succ, Finset.sum_range_one, map_add, map_add,
      coeff_bilatTerm_zero (show (1 : ℕ) < (1 + 1) ^ 2 by norm_num), bilatTerm]
  simp [coeff_X_pow_mul']

end MockTheta5.JTP
