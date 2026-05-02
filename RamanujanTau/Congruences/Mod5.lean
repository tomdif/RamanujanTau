import RamanujanTau.Basic
import RamanujanTau.SmallValues
import RamanujanTau.Congruences.Sigma
import Mathlib.Data.Int.ModEq

/-! # Ramanujan's congruence mod 5² = 25

```
τ(n) ≡ n · σ_9(n)  (mod 25)        for gcd(n, 5) = 1
```

* **Source.** Ramanujan (1916) "On certain arithmetical functions",
  Trans. Camb. Phil. Soc. **22**, 159–184.
* **Note on convention.** Numerical check at `n = 2` rules out the
  variant with `σ_3`: `2 · σ_3(2) = 18`, and `-24 - 18 = -42 ≢ 0 (mod 25)`
  (it is `8 (mod 25)`). The variant with `σ_9` works:
  `2 · σ_9(2) = 1026`, and `-24 - 1026 = -1050 = -42 · 25`. The 5² form
  with `σ_9` is the one picked out by Serre's classification at the
  exceptional prime ℓ = 5.

We expose the global statement as a hypothesis class and verify three small
numerical instances by `decide`.
-/

namespace RamanujanTau

/-- **Hypothesis class**: Ramanujan's mod-25 congruence for `τ`.

`τ(n) ≡ n · σ_9(n) (mod 25)` for every `n` coprime to 5. -/
class TauMod25 : Prop where
  congruence : ∀ {n : ℕ}, n ≥ 1 → Nat.Coprime n 5 →
    τ n ≡ (n : ℤ) * sigma9 n [ZMOD 25]

/-! ## Numerical sanity checks at `n = 1, 2, 3` -/

theorem cong_25_one : τ 1 ≡ (1 : ℤ) * sigma9 1 [ZMOD 25] := by
  rw [tau_one, sigma9_one]; decide

theorem cong_25_two : τ 2 ≡ (2 : ℤ) * sigma9 2 [ZMOD 25] := by
  rw [tau_two, sigma9_two]; decide

theorem cong_25_three : τ 3 ≡ (3 : ℤ) * sigma9 3 [ZMOD 25] := by
  rw [tau_three, sigma9_three]; decide

end RamanujanTau
