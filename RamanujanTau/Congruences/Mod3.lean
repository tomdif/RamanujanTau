import RamanujanTau.Basic
import RamanujanTau.SmallValues
import RamanujanTau.Congruences.Sigma
import Mathlib.Data.Int.ModEq

/-! # Ramanujan's congruence mod 3³ = 27

```
τ(n) ≡ n² · σ_7(n)  (mod 27)        for gcd(n, 3) = 1
```

* **Source.** Wilton (1929) "Congruence properties of Ramanujan's
  function τ(n)", Proc. London Math. Soc. **31**, 1–10.
* **Note on convention.** The literature also records a weaker form
  `τ(n) ≡ n · σ_1(n) (mod 9)` (Bambah-Chowla 1947). The mod-27 refinement
  with the `n²·σ_7` right-hand side is Wilton's; the choice of `n²`
  rather than `n` is not optional — see the numerical check at `n = 2`
  below, where `n · σ_7` gives `258` (not `≡ -24 (mod 27)`) but
  `n² · σ_7` gives `516` and `516 - (-24) = 540 = 27 · 20`. This is the
  form picked out by Serre's classification of the exceptional prime
  ℓ = 3 for Δ.

We expose the global statement as a hypothesis class and verify three small
numerical instances by `decide`.
-/

namespace RamanujanTau

/-- **Hypothesis class**: Wilton's mod-27 congruence for `τ`.

`τ(n) ≡ n² · σ_7(n) (mod 27)` for every `n` coprime to 3. -/
class TauMod27 : Prop where
  congruence : ∀ {n : ℕ}, n ≥ 1 → Nat.Coprime n 3 →
    τ n ≡ (n : ℤ)^2 * sigma7 n [ZMOD 27]

/-! ## Numerical sanity checks at `n = 1, 2, 4`

(Skipping `n = 3` since `gcd(3, 3) ≠ 1`.) -/

theorem cong_27_one : τ 1 ≡ (1 : ℤ)^2 * sigma7 1 [ZMOD 27] := by
  rw [tau_one, sigma7_one]; decide

theorem cong_27_two : τ 2 ≡ (2 : ℤ)^2 * sigma7 2 [ZMOD 27] := by
  rw [tau_two, sigma7_two]; decide

theorem cong_27_four : τ 4 ≡ (4 : ℤ)^2 * sigma7 4 [ZMOD 27] := by
  rw [tau_four, sigma7_four]; decide

end RamanujanTau
