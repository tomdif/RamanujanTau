# Mock-theta Bailey campaign — roadmap

**Goal:** close the infinite 5th-order identity `χ₀ = 2·F₀ − φ₀(−q)`.
It reduces (kernel-verified: `MockTheta5.Formal.mtc5_chi0_of_coeff`) to the coefficient identity
`∀k, coeff k χ₀ = 2·coeff k F₀ − (−1)ᵏ·coeff k φ₀`. That ∀k equality is a Bailey-pair argument.

**Mathlib status (surveyed):** NONE of the needed q-series machinery exists — no Gaussian binomial,
no q-binomial theorem, no Bailey pairs, no Jacobi triple product, no Rogers–Ramanujan. Only the *analytic*
Jacobi theta (wrong object). So the campaign builds everything from the q-Pochhammer foundation up. This is
Mathlib-contribution scale (the q-series + Bailey's-lemma layer is itself a publishable formalization).

## Ladder (each tier kernel-gated; the proofworld loop proposes proofs rung by rung)
- **Tier 0 — DONE.** `qpoch`/`qpochG` + invertibility (`MockTheta5Series`); summable family
  (`MockTheta5Lemmas`); `F₀,χ₀,φ₀ : PowerSeries ℤ`, reduction to coeffs, order-0 base case (`MockTheta5Defs`).
- **Tier 1 — STARTED (`MockTheta5Bailey`).** Gaussian binomial `gaussBinom` + q-Pascal + diagonal vanishing +
  `gaussBinom_self`. NEXT: symmetry `[n,k]=[n,n−k]`; connection to `(q;q)_n`; the **q-binomial theorem**
  `∏_{k<n}(1+x qᵏ) = Σ_k q^{k(k−1)/2} [n,k]_q xᵏ` (induction via q-Pascal).
- **Tier 2.** Bailey pair (def): `(α,β)` is a Bailey pair rel. `a` iff `β_n = Σ_{r≤n} α_r/((q;q)_{n−r}(aq;q)_{n+r})`.
  Bailey's lemma (the iteration producing a new pair). Hardest infrastructure tier.
- **Tier 3.** The specific 5th-order Bailey pair (unit pair specialization) giving the F₀/χ₀/φ₀ series.
- **Tier 4.** Assemble the coefficient identity from the Bailey pair → discharge `mtc5_chi0_of_coeff`'s
  hypothesis → identity closed.

**Honest scale:** Tiers 1–4 are a multi-month research formalization, driven incrementally through the loop
(`proofworld.mocktheta_pipeline`, `PROOFWORLD_LLM=1`), the Lean kernel gating every rung. No shortcut, no sorry.
