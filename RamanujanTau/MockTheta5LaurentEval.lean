/-
# Toward the `ℤ((q))` bilateral-theta framework: the non-unit `z`-evaluation primitive

The repo's `classical_jacobi_triple_product` keeps `z` **formal** (in `PowerSeries (LaurentPolynomial ℤ)`),
because the pentagonal/Rogers–Ramanujan products need it evaluated at `z = ±q, −q²` — **non-units** in
`PowerSeries ℤ`, and the bilateral form needs `z⁻¹`. The fix is to land in the field of formal Laurent
series `ℤ((q)) = LaurentSeries ℤ`, where `q = X` **is** a unit.

This file builds the core enabling primitive: **`evalZ a : ℤ[z;z⁻¹] →+* ℤ((q))`, `z ↦ qᵃ`** (`evalZ_T`:
`evalZ a (zⁿ) = q^{aⁿ}`). Since `qᵃ = single a 1` is a unit in `ℤ((q))` (`uSingle`), this is a genuine ring
hom — the evaluation that was impossible into `PowerSeries ℤ`.

## What remains (the grading-addition flatten)
To turn the repo's identity `A = B` in `PowerSeries (LaurentPolynomial ℤ)` (outer `q`, inner `z`) into a
concrete `ℤ((q))` identity, one applies `evalZ a` to coefficients (`PowerSeries.map (evalZ a)`, a clean ring
hom) and then **substitutes the outer `q ↦ X`**, collapsing `PowerSeries (ℤ((q))) → ℤ((q))`. That last step is
the summation of the family `n ↦ evalZ a (coeff n ·) · Xⁿ`, summable exactly when `ord + n → ∞` (which holds
for the sparse `bilateralTheta`: its `q^{k²}` coefficient is `zᵏ+z⁻ᵏ ↦ q^{ak}+q^{-ak}`, giving terms of order
`k²−ak → ∞`). Mathlib's `heval`/`powerSeriesFamily` do **not** do this directly: they keep the two gradings
separate (a fresh Hahn variable), whereas here `z` and `q` must be *added* into one grading. So the flatten is
a custom `HahnSeries.SummableFamily` construction (with `hsum_mul` for multiplicativity on the product side
`qfac2InfL·SZ·SZinv`). With it, pentagonal (`a=1`, base `q³`), RR1 (`a=−1` in `−q²`, base `q⁵`), RR2, and
Identity A's theta all follow by evaluating `classical_jacobi_triple_product` at the right `(a, base)`. No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiBilateral
import Mathlib.RingTheory.LaurentSeries

namespace MockTheta5.Laurent
open HahnSeries LaurentPolynomial

/-- the monomial `qᵃ = Xᵃ ∈ ℤ((q))` packaged as a unit (inverse `q⁻ᵃ`). -/
noncomputable def uSingle (a : ℤ) : (LaurentSeries ℤ)ˣ :=
  ⟨single a 1, single (-a) 1, by rw [single_mul_single]; simp, by rw [single_mul_single]; simp⟩

@[simp] lemma val_uSingle (a : ℤ) :
    ((uSingle a : (LaurentSeries ℤ)ˣ) : LaurentSeries ℤ) = single a 1 := rfl
@[simp] lemma val_uSingle_inv (a : ℤ) :
    ((↑(uSingle a)⁻¹ : LaurentSeries ℤ)) = single (-a) 1 := rfl

lemma val_uSingle_zpow (a n : ℤ) :
    ((uSingle a ^ n : (LaurentSeries ℤ)ˣ) : LaurentSeries ℤ) = single (a * n) 1 := by
  refine Int.induction_on n ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simp
  · rw [zpow_add_one, Units.val_mul, ih, val_uSingle, single_mul_single]; ring_nf
  · rw [show (-(k : ℤ) - 1) = (-(k : ℤ)) + (-1) from by ring, zpow_add, zpow_neg_one, Units.val_mul,
        ih, val_uSingle_inv, single_mul_single]; ring_nf

/-- **The non-unit evaluation `z ↦ qᵃ`** `: ℤ[z;z⁻¹] →+* ℤ((q))`. Valid (a ring hom) because `qᵃ` is a unit
in `ℤ((q))`, unlike in `PowerSeries ℤ` — the primitive that unblocks bilateral-theta specialization. -/
noncomputable def evalZ (a : ℤ) : LaurentPolynomial ℤ →+* LaurentSeries ℤ :=
  LaurentPolynomial.eval₂ (Int.castRingHom (LaurentSeries ℤ)) (uSingle a)

/-- `evalZ a (zⁿ) = q^{aⁿ}`. -/
@[simp] lemma evalZ_T (a n : ℤ) : evalZ a (T n) = single (a * n) 1 := by
  rw [evalZ, LaurentPolynomial.eval₂_T, val_uSingle_zpow]

/-- `evalZ a (C c) = c` (constants map to constants). -/
@[simp] lemma evalZ_C (a : ℤ) (c : ℤ) : evalZ a (LaurentPolynomial.C c) = HahnSeries.C c := by
  rw [evalZ, LaurentPolynomial.eval₂_C]; rfl

end MockTheta5.Laurent
