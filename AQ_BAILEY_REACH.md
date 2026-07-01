# The `a=q` Bailey machinery: verified reach map

Machinery built this session (axiom-clean, no `sorry`):
- `MockTheta5BaileyQ.lean` — `IsBaileyPairQ`, seed, `isBaileyPairQ_chain` (commit `332e78c`)
- `MockTheta5BaileyQTransform.lean` — `bailey_transform_q`, seed corollary (commit `e003b09`)

`bailey_transform_q`: for an `a=q` Bailey pair `(α,β)` (`βₙ = Σ_{r≤n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r})`),

    Σ_{n≥0} q^{n²+n} βₙ  =  (1/(q²;q)_∞) · Σ_{n≥0} q^{n²+n} αₙ.

## Numerically mapped reach (all verified to q²⁴ via `a=q` Bailey inversion, `/tmp/aq_scope.py`)

The inversion `αₙ = (q²;q)_{2n}·(βₙ − Σ_{r<n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r}))` was validated against the
seed (`β = 1/((q;q)ₙ(q²;q)ₙ) ⟹ α = δ_{·,0}`, exact).

### Structural finding: mock-theta summands have MESSY α
For `βₙ = 1/(−q;q)ₙ`, `(−q;q²)ₙ`, `1/(q;q²)ₙ` the `a=q` Bailey `α` is dense, sign-irregular, and has no
closed form — the same verdict the `a=1` inversion gave. This is **not** a defect of the machinery: a Bailey
pair with theta-closed-form `α` makes `Σ q^{n²+n}βₙ` a theta quotient, i.e. **modular**. Mock thetas are by
definition non-modular, so they *cannot* have clean Bailey `α`. Reaching them needs Hecke-type double sums,
not a single clean pair — this reframes the R1 (`χ₀ = 2F₀ − φ₀(−q)`) route.

### Clean reachable identities (unit β's)
Two "unit" `β`'s give clean, terminating, theta-like `α` of the telescoping form
`αₙ = (−1)ⁿ(q^{P(n)} − q^{P(n+1)})/(1−q)`:

**Identity A** — `βₙ = 1/(q²;q²)ₙ`, `αₙ = (−1)ⁿ q^{n²}(1+q+···+q^{2n}) = (−1)ⁿ(q^{n²}−q^{(n+1)²})/(1−q)`:

    Σ_{n≥0} q^{n²+n}/(q²;q²)ₙ  =  (1/(q;q)_∞) · Σ_{n∈ℤ} (−1)ⁿ q^{2n²+n}.

**Identity B = second Rogers–Ramanujan** — `βₙ = 1/(q;q)ₙ`,
`αₙ = (−1)ⁿ q^{n(3n+1)/2}(1+q+···+q^{2n})` (pentagonal):

    Σ_{n≥0} q^{n²+n}/(q;q)ₙ  =  (1/(q;q)_∞) · Σ_{n∈ℤ} (−1)ⁿ q^{(5n²+3n)/2}.

Both bilateral thetas are exactly the `Σ_{n∈ℤ} zⁿ Q^{n²}` shape that `classical_jacobi_triple_product`
turns into a product — so these are reachable **without** the `q^{1/2}` product-side flatten that blocks the
pentagonal/RR route elsewhere.

## Next milestone (to make Identity A a sorry-free theorem)
Only one lemma is missing: the finite `a=q` Bailey identity
`Σ_{r≤n} (−1)ʳ(q^{r²}−q^{(r+1)²})/((1−q)(q;q)_{n-r}(q²;q)_{n+r}) = 1/(q²;q²)ₙ`
(i.e. `IsBaileyPairQ α β` for the explicit telescoping `α`). Unlike the seed and the shared `F_eq_one` core,
this does not collapse to a single Gaussian binomial and needs its own induction (a fresh `F`-style
generalization). With it, `bailey_transform_q` + the bilateral-theta reindex `Σ_{n≥0}(...) = Σ_{n∈ℤ}(...)`
+ the JTP close Identity A end-to-end.
