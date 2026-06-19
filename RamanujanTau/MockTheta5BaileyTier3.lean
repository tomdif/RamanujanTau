/-
# Bailey campaign, Tier 3: exercising the chain on a concrete specialization

With the unconditional limiting Bailey's lemma in hand (`isBaileyPair_chain`), this file runs the machinery
end-to-end on the seed pair to derive a genuine q-series identity — a sanity-check that the whole stack
(seed pair → chain preservation → uniqueness of β) actually produces theorems, not just types.

The seed pair `(αₙ, βₙ) = (δ_{n,0}, 1/(q;q)ₙ²)` has `α` fixed by the chain step (`qⁿ²·δ = δ`), so by
uniqueness of `β` the seed is a *fixed point* of the whole chain. Reading off `β` gives:

  **`durfee_identity`:**  `Σ_{j≤n} qʲ² / ((q;q)_{n-j}·(q;q)ⱼ²) = 1/(q;q)ₙ²`.

This is a finite Durfee-square-type identity, obtained with NO direct sum manipulation — purely from the
abstract Bailey structure. No `sorry`.

**Honest scope toward the mock theta conjecture.** Closing `χ₀ = 2F₀ − φ₀(−q)` itself (Tier 4) is *not* a
short specialization of this: the fifth-order functions live in base `q²` (`(q;q²)ₙ`, `(−q;q²)ₙ`), and
Hickerson's proof routes through Hecke-type indefinite theta series and modular forms — machinery beyond the
limiting Bailey chain. That remains the genuine research frontier; this file demonstrates the chain works.
-/
import RamanujanTau.MockTheta5BaileyChain

namespace MockTheta5.Bailey
open PowerSeries

/-- The seed's `α = δ_{·,0}` is a fixed point of the chain step `αₙ ↦ qⁿ²·αₙ`. -/
lemma chainAlpha_seedAlpha : chainAlpha seedAlpha = seedAlpha := by
  funext n
  simp only [chainAlpha, seedAlpha]
  rcases n with _ | n <;> simp

/-- Hence `(seedAlpha, chainBeta seedBeta)` is a Bailey pair (with the seed's `α`). -/
lemma isBaileyPair_chainSeed : IsBaileyPair seedAlpha (chainBeta seedBeta) := by
  have h := isBaileyPair_chain isBaileyPair_seed
  rwa [chainAlpha_seedAlpha] at h

/-- Since `β` is determined by `α` in a Bailey pair, the seed is a fixed point of the chain on `β` too. -/
theorem chainBeta_seedBeta (n : ℕ) : chainBeta seedBeta n = seedBeta n := by
  rw [isBaileyPair_chainSeed n, ← isBaileyPair_seed n]

/-- **A finite Durfee-square-type identity** `Σ_{j≤n} qʲ²/((q;q)_{n-j}·(q;q)ⱼ²) = 1/(q;q)ₙ²`,
derived purely from the Bailey machinery (seed pair + chain preservation + uniqueness of `β`),
with no direct sum manipulation. -/
theorem durfee_identity (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
        X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * (Ring.inverse (qfac j) * Ring.inverse (qfac j)))
      = Ring.inverse (qfac n) * Ring.inverse (qfac n) := by
  have h := chainBeta_seedBeta n
  rw [chainBeta, seedBeta] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [seedBeta]

end MockTheta5.Bailey
