import RamanujanTau.Basic
import RamanujanTau.SmallValues
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Parity
import Mathlib.Data.Nat.Prime.Basic

/-! # Ramanujan's congruence mod 23 (the dihedral case)

```
τ(p) ≡ 0  (mod 23)        for p prime, p ≠ 23, with (p / 23) = -1
```

i.e. `τ(p) ≡ 0 (mod 23)` whenever `p` is a quadratic non-residue mod 23.

* **Source.** Wilton (1929) "Congruence properties of Ramanujan's
  function τ(n)", Proc. London Math. Soc. **31**, 1–10. The original
  observation that τ vanishes mod 23 on a Chebotarev-density-1/2 set
  of primes is also in Ramanujan's notebooks.
* **Modern interpretation.** ℓ = 23 is the unique prime in Serre's
  classification where the mod-ℓ Galois representation `ρ̄_Δ : Gal(Q̄/Q)
  → GL_2(F_23)` has *dihedral* image (rather than reducible or full).
  The image is contained in the normalizer of a non-split Cartan; the
  fixed field is `Q(√-23)`. Splitting of `p` in `Q(√-23)` is governed
  by the Legendre symbol `(p / 23)`, and τ(p) = trace of Frobenius is
  forced to vanish mod 23 precisely on the inert primes — i.e. when
  `(p / 23) = -1`.

We expose the global statement as a hypothesis class. The non-residue
condition is stated via `¬ IsSquare ((p : ZMod 23))`, which avoids the
`Fact p.Prime` instance plumbing of `legendreSym`. The two forms are
equivalent for `p ≠ 23` prime.

We verify the congruence numerically at `p = 5`, the smallest prime
quadratic non-residue mod 23. The squares in `(ZMod 23)*` are
`{1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18}`; non-residues are
`{5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22}`. So `(5 / 23) = -1` and
`τ(5) = 4830 = 23 · 210 ≡ 0 (mod 23)`.
-/

namespace RamanujanTau

/-- **Hypothesis class**: Wilton's mod-23 dihedral congruence for `τ`.

`τ(p) ≡ 0 (mod 23)` for every prime `p ≠ 23` that is a quadratic
non-residue mod 23. -/
class TauMod23 : Prop where
  congruence : ∀ {p : ℕ}, p.Prime → p ≠ 23 →
    ¬ IsSquare ((p : ZMod 23)) → τ p ≡ 0 [ZMOD 23]

/-! ## Numerical sanity check at `p = 5`

The smallest applicable prime: `5` is not a square in `ZMod 23` (the
squares are `{1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18}`), so the hypothesis
class predicts `τ(5) ≡ 0 (mod 23)`. We verify this directly. -/

theorem cong_23_five : τ 5 ≡ 0 [ZMOD 23] := by
  rw [tau_five]; decide

/-- For comparison: `5` is genuinely a non-residue mod 23. The decision
procedure for `IsSquare (5 : ZMod 23)` reduces to a finite check. -/
theorem five_not_square_mod_23 : ¬ IsSquare ((5 : ZMod 23)) := by
  decide

end RamanujanTau
