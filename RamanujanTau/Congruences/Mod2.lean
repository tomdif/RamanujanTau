import RamanujanTau.Basic
import RamanujanTau.SmallValues
import RamanujanTau.Congruences
import Mathlib.Data.Int.ModEq

/-! # Ramanujan-style congruences mod powers of 2

The mod-2 family for τ is split into successively stronger statements
depending on the residue class of `n` mod 8:

```
τ(n) ≡ σ_11(n)  (mod 2^8 = 256)       if n is odd                   (Wilton 1929)
τ(n) ≡ σ_11(n)  (mod 2^11 = 2048)     if n ≡ 1 (mod 8)               (Kolberg 1962)
```

* **Source for mod 2⁸.** Wilton (1929) "Congruence properties of Ramanujan's
  function τ(n)", Proc. London Math. Soc. **31**, 1–10.
* **Source for mod 2¹¹.** Kolberg (1962) "Congruences for Ramanujan's
  function τ(n)", Aarbok Univ. Bergen Mat.-Natur. Ser. **11**, 1–8.
* **Modern interpretation.** ℓ = 2 is the most exceptional prime in
  Serre & Swinnerton-Dyer's (1973) classification: the mod-2 Galois
  representation factors through `S_3 = GL_2(F_2)`, and the various
  congruences mod 2^k correspond to lifts to higher 2-adic level.

We expose **two** hypothesis classes here. The user-facing "mod 2¹¹"
statement is restricted to `n ≡ 1 (mod 8)` because — as the numerical
check at `n = 3` reveals — the unrestricted "odd `n`" form is only valid
mod 2⁸:

* `τ(3) - σ_11(3) = -176896 = -256 · 691` — divisible by `2⁸` but not `2⁹`.

So the "odd `n`" hypothesis class is the mod-2⁸ form, and the mod-2¹¹
form requires the stricter residue condition.
-/

namespace RamanujanTau

/-- **Hypothesis class** (Wilton 1929): the mod-2⁸ Ramanujan congruence.

`τ(n) ≡ σ_11(n) (mod 2⁸)` for every odd `n`. -/
class TauMod2_8 : Prop where
  congruence : ∀ {n : ℕ}, n ≥ 1 → Odd n →
    τ n ≡ sigma11 n [ZMOD 256]

/-- **Hypothesis class** (Kolberg 1962): the mod-2¹¹ Ramanujan congruence.

`τ(n) ≡ σ_11(n) (mod 2¹¹)` for every `n ≡ 1 (mod 8)`. -/
class TauMod2_11 : Prop where
  congruence : ∀ {n : ℕ}, n ≥ 1 → n % 8 = 1 →
    τ n ≡ sigma11 n [ZMOD 2048]

/-! ## Numerical sanity checks for the mod-2⁸ form

Holds for every odd `n`. We check `n = 1, 3, 5`. -/

theorem cong_256_one : τ 1 ≡ sigma11 1 [ZMOD 256] := by
  rw [tau_one, sigma11_one]

theorem cong_256_three : τ 3 ≡ sigma11 3 [ZMOD 256] := by
  rw [tau_three, sigma11_three]; decide

theorem cong_256_five : τ 5 ≡ sigma11 5 [ZMOD 256] := by
  rw [tau_five]
  -- σ_11(5) = 1 + 5^11 = 48828126
  show (4830 : ℤ) ≡ sigma11 5 [ZMOD 256]
  have h : sigma11 5 = 48828126 := by unfold sigma11; decide
  rw [h]; decide

/-! ## Numerical sanity check for the mod-2¹¹ form

The smallest applicable `n` is `n = 1` (and the next is `n = 9`).
We check `n = 1` here; `n = 9` involves the value `τ(9) = -113643`
together with `σ_11(9) = 1 + 3¹¹ + 9¹¹ = 31381236757`, and
`τ(9) - σ_11(9) = -31381350400 = -2048 · 15322925`. -/

theorem cong_2048_one : τ 1 ≡ sigma11 1 [ZMOD 2048] := by
  rw [tau_one, sigma11_one]

theorem cong_2048_nine : τ 9 ≡ sigma11 9 [ZMOD 2048] := by
  rw [tau_nine]
  have h : sigma11 9 = 31381236757 := by unfold sigma11; decide
  rw [h]; decide

end RamanujanTau
