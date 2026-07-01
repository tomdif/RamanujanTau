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

## Gap CLOSED (`MockTheta5BaileyQPairA.lean`, axiom-clean, no `sorry`)
The finite `a=q` Bailey identity `IsBaileyPairQ α β` for the explicit `α` (`isBaileyPairQ_A`) is now proven.
It does not collapse to the shared `F_eq_one` core (the mixed-Pochhammer ratio is a genuine infinite series),
so it is proved by **creative telescoping**: `S(n) := Σ_{r≤n} αᵣ/((q;q)_{n-r}(q²;q)_{n+r})` satisfies
`(1-q^{2n})·S(n) = S(n-1)` (`Ssum_rec`) via the explicit certificate
`G(n,r) = (−1)^{r+1} q^{n+r(r-1)}(1+···+q^{2r-1})(1−q^{n+r+1})/((q;q)_{n-r}(q²;q)_{n+r})`, whose term-wise
identity (`lemA`) is a pure `ring` fact after clearing `(q²;q)`→`(q;q)` and using `geom(m)(1−q)=1−q^m`.
Feeding the pair into `bailey_transform_q` gives Identity A as `Σ q^{n²+n}/(q²;q²)_n = (1/(q²;q)_∞)·Σ q^{n²+n}αₙ`
(`identityA_transform`).

Remaining (optional, to reach the closed bilateral-theta/product RHS): evaluate `Σ q^{n²+n} αₙ` as the
bilateral theta `Σ_{n∈ℤ}(−1)ⁿq^{2n²+n}` (reindex `Σ_{n≥0}→Σ_{n∈ℤ}`) via the JTP — a repackaging, not a new
obstruction. (Note the LHS `Σ q^{n²+n}/(q²;q²)_n` also equals `(−q²;q²)_∞` by the repo's Euler identity
`E2prodOnePlus_eq_pthetaPosSum`.)
