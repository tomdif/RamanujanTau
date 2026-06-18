/-
# Rung-3 foundation: q-Pochhammer over formal power series (toward the 5th-order mock theta identities)

`MockTheta5.lean` certified the Ramanujan relations at TRUNCATED order (`native_decide`, rung 2). Rung 3 is
the *infinite* identity, which requires the mock theta functions as genuine formal power series — and for
that we need the q-Pochhammer symbol and the fact that `1/(q;q²)_n` etc. are honest power series.

This file is that foundation, over Mathlib `PowerSeries ℤ`:
  qpoch a n = (a; q)_n = ∏_{k<n} (1 - a·Xᵏ)   (q := X)
with its defining recurrence and — the load-bearing fact — invertibility when `constantCoeff a = 0`
(so the denominators in F₀, χ₀, … are units, hence well-defined power series).

Honest scope: this is infrastructure, fully proven (no `sorry`). The full identity χ₀ = 2F₀ − φ₀(−q) needs,
on top of this, a summable-family-of-power-series framework and a Bailey-pair argument — a substantial
further build. This commits only what the kernel accepts.
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

namespace MockTheta5
open PowerSeries

/-- The q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a·qᵏ)` with `q := X`, over `ℤ`-power series. -/
noncomputable def qpoch (a : PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ Finset.range n, (1 - a * X ^ k)

@[simp] lemma qpoch_zero (a : PowerSeries ℤ) : qpoch a 0 = 1 := by
  simp [qpoch]

/-- Defining recurrence: `(a;q)_{n+1} = (a;q)_n · (1 - a·qⁿ)`. -/
lemma qpoch_succ (a : PowerSeries ℤ) (n : ℕ) :
    qpoch a (n + 1) = qpoch a n * (1 - a * X ^ n) := by
  simp [qpoch, Finset.prod_range_succ]

/-- If `a` has no constant term, every factor `(1 - a·Xᵏ)` has constant term 1, so does the product. -/
lemma constantCoeff_qpoch (a : PowerSeries ℤ) (ha : constantCoeff a = 0) (n : ℕ) :
    constantCoeff (qpoch a n) = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : constantCoeff (1 - a * X ^ k) = 1 := by
        rw [map_sub, map_one, map_mul, ha, zero_mul, sub_zero]
      rw [qpoch_succ, map_mul, ih, h1, mul_one]

/-- **The load-bearing fact**: when `constantCoeff a = 0`, `(a;q)_n` is a unit in `ℤ⟦X⟧`,
so `1/(a;q)_n` is a genuine formal power series (the denominators in F₀, χ₀, … are well-defined). -/
lemma isUnit_qpoch (a : PowerSeries ℤ) (ha : constantCoeff a = 0) (n : ℕ) :
    IsUnit (qpoch a n) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_qpoch a ha n]
  exact isUnit_one

/-- The specific denominators appearing in the 5th-order functions are units:
`(X;X²)_n` etc. (from F₀, F₁) and `(q^{n+1};q)_m` (from χ₀, χ₁) all have a base `a = Xʲ` with `j ≥ 1`. -/
lemma isUnit_qpoch_Xpow (j : ℕ) (hj : 0 < j) (n : ℕ) : IsUnit (qpoch (X ^ j) n) := by
  apply isUnit_qpoch
  rw [map_pow, constantCoeff_X]
  exact zero_pow hj.ne'

end MockTheta5
