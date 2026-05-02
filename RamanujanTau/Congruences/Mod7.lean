import RamanujanTau.Basic
import RamanujanTau.SmallValues
import RamanujanTau.Congruences.Sigma
import Mathlib.Data.Int.ModEq

/-! # Ramanujan's congruence mod 7

```
τ(n) ≡ n · σ_3(n)  (mod 7)        for gcd(n, 7) = 1
```

* **Source.** Ramanujan (1916) "On certain arithmetical functions",
  Trans. Camb. Phil. Soc. **22**, 159–184.
* **Modern interpretation.** Serre's classification of mod-ℓ Galois
  representations attached to Δ identifies ℓ = 7 as one of the
  *exceptional* primes, where the representation has reducible image of
  the form `1 ⊕ χ³` (with `χ` the cyclotomic character mod 7). The
  congruence `τ(n) ≡ n · σ_3(n) (mod 7)` is the trace identity for that
  reducible representation.

We expose the global statement as a hypothesis class and verify three small
numerical instances by `decide`.
-/

namespace RamanujanTau

/-- **Hypothesis class**: Ramanujan's mod-7 congruence for `τ`.

`τ(n) ≡ n · σ_3(n) (mod 7)` for every `n` coprime to 7. -/
class TauMod7 : Prop where
  congruence : ∀ {n : ℕ}, n ≥ 1 → Nat.Coprime n 7 →
    τ n ≡ (n : ℤ) * sigma3 n [ZMOD 7]

/-! ## Numerical sanity checks at `n = 1, 2, 3` -/

theorem cong_7_one : τ 1 ≡ (1 : ℤ) * sigma3 1 [ZMOD 7] := by
  rw [tau_one, sigma3_one]; decide

theorem cong_7_two : τ 2 ≡ (2 : ℤ) * sigma3 2 [ZMOD 7] := by
  rw [tau_two, sigma3_two]; decide

theorem cong_7_three : τ 3 ≡ (3 : ℤ) * sigma3 3 [ZMOD 7] := by
  rw [tau_three, sigma3_three]; decide

end RamanujanTau
