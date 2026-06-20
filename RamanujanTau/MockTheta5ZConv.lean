/-
# JTP step L8 (the z-Cauchy product): `SZ · SZinv`

The genuine crux of the bilateral Jacobi triple product. `SZ` carries z-degrees `≥ 0`, `SZinv` carries
z-degrees `≤ 0`; their product's `z^N` coefficient is the Cauchy convolution
`Σ_{k-j=N} (q^{k²}/(q²;q²)_k)(q^{j²}/(q²;q²)_j)`. We compute it *without* infinite-support `Finsupp`
machinery: each q-degree coefficient of `SZ`/`SZinv` is a finite sum of `single`s, so the product is a
finite `single`-convolution (`single a x * single b y = single (a+b) (x·y)`), and applying at z-degree `N`
selects the diagonal `k - j = N`.

This file builds that diagonal double-sum (`prodSZ_apply`). The downstream assembly collapses the diagonal
(`k = N + j` for `N ≥ 0`) into `Σ_j coeff m (q^{(N+j)²+j²}/((q²;q²)_{N+j}(q²;q²)_j))`, recognises the summand
as `q^{N²}·E2(rectTerm N j)` via `(N+j)²+j² = N² + 2(j²+Nj)`, and finishes with `durfee_rect_base_Q`.
No `sorry`.
-/
import RamanujanTau.MockTheta5ZProj

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the `k`-th Cauchy coefficient at q-degree `p`: `[q^p] q^{k²}/(q²;q²)_k`. -/
noncomputable def szc (p k : ℕ) : ℤ := coeff p (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)))

lemma coeff_SZterm_single (p k : ℕ) : coeff p (SZterm k) = Finsupp.single (k : ℤ) (szc p k) := by
  ext n; rw [SZterm_apply, Finsupp.single_apply]; rfl

lemma coeff_SZinvTerm_single (r j : ℕ) :
    coeff r (SZinvTerm j) = Finsupp.single (-(j : ℤ)) (szc r j) := by
  ext n; rw [SZinvTerm_apply, Finsupp.single_apply]; rfl

/-- **the z-Cauchy product, diagonal form**: the `z^N` coefficient of `coeff p SZ · coeff r SZinv`
is the diagonal double-sum `Σ_{k,j} [k - j = N] szc p k · szc r j` over the finite ranges. -/
lemma prodSZ_apply (p r : ℕ) (N : ℤ) :
    (coeff p SZ * coeff r SZinv) N
      = ∑ k ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (r + 1),
          (if (k : ℤ) - j = N then szc p k * szc r j else 0) := by
  rw [coeff_SZ (le_refl (p + 1)), coeff_SZinv (le_refl (r + 1)), SZfinite, SZinvFinite,
      map_sum, map_sum]
  simp_rw [coeff_SZterm_single, coeff_SZinvTerm_single]
  rw [Finset.sum_mul_sum]
  simp_rw [AddMonoidAlgebra.single_mul_single]
  rw [laurentSum_apply]
  simp_rw [laurentSum_apply, Finsupp.single_apply, ← sub_eq_add_neg]

end MockTheta5.JTP
