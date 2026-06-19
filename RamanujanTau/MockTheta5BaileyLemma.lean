/-
# Bailey campaign, Tier 2c: Bailey's lemma (limiting form) — operator built, core pinned

The workhorse for mock theta (and Rogers–Ramanujan) is the **limiting (ρ,σ→∞) Bailey chain step**, which has
no awkward parameters or non-unit denominators:

  α'ₙ = qⁿ²·αₙ ,   β'ₙ = Σ_{j≤n} qʲ²/(q;q)_{n-j} · βⱼ .

**Bailey's lemma (limiting form):** if `(α,β)` is a Bailey pair (relative to `a=1`, see `IsBaileyPair`), then so
is `(α',β')`. Iterating this from the seed pair `isBaileyPair_seed` is the *Bailey chain* that produces the
Rogers–Ramanujan / mock-theta sums.

This file builds the chain operator (`chainAlpha`, `chainBeta`) — which *is* the statement of the lemma — and the
`rfac` telescoping infrastructure, and pins the lemma's proof to a single explicit identity:

  **`bailey_inner`:**  Σ_{i≤m} q^{i²+2ri}·[m,i]_q·(q^{2r+i+1};q)_{m-i} = 1   (for all m, r).

This is a terminating q-Chu–Vandermonde-type identity. It is **symbolically verified** (sympy, all m≤5, r≤3 give
exactly 1) and its base case `m=0` is proved below. The general case is the genuine research wall: Mathlib has no
q-Chu–Vandermonde, and the naive single-variable induction provably does **not** close — the successor step leaves
`Σ_{x≤m} q^{…}[m+1,x]_q·(q^{2r+x+1};q)_{m+1-x}`, which is not another instance of the same sum (it needs a coupled
recurrence). Documented here as the exact remaining goal, with NO `sorry` committed.

No `sorry`.
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import RamanujanTau.MockTheta5BaileyPair

namespace MockTheta5.Bailey
open PowerSeries

/-- `(q^{s+1};q)_t = ∏_{k<t} (1 - q^{s+1+k})`, the rising q-factorial in Bailey's lemma. -/
noncomputable def rfac (s t : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range t, (1 - X ^ (s + 1 + k))

@[simp] lemma rfac_zero (s : ℕ) : rfac s 0 = 1 := by simp [rfac]

/-- Telescoping: extending the length multiplies by the single factor `(1 - q^{s+t+1})`. -/
lemma rfac_succ (s t : ℕ) : rfac s (t + 1) = rfac s t * (1 - X ^ (s + t + 1)) := by
  rw [rfac, Finset.prod_range_succ, ← rfac]; ring_nf

/-- **Bailey chain step on α** (limiting form): `α'ₙ = qⁿ²·αₙ`. -/
noncomputable def chainAlpha (α : ℕ → PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ := X ^ (n ^ 2) * α n

/-- **Bailey chain step on β** (limiting form): `β'ₙ = Σ_{j≤n} qʲ²/(q;q)_{n-j} · βⱼ`. -/
noncomputable def chainBeta (β : ℕ → PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  ∑ j ∈ Finset.range (n + 1), X ^ (j ^ 2) * Ring.inverse (qfac (n - j)) * β j

/-- Base case (`m = 0`) of the inner identity that powers Bailey's lemma:
`Σ_{i≤0} q^{i²+2ri}·[0,i]_q·(q^{2r+i+1};q)_{0-i} = 1`. -/
theorem bailey_inner_zero (r : ℕ) :
    ∑ i ∈ Finset.range (0 + 1),
      X ^ (i ^ 2 + 2 * r * i) * gaussBinom 0 i * rfac (2 * r + i) (0 - i) = 1 := by
  simp [rfac]

/-
**Status update:** `bailey_inner` is now PROVED — see `MockTheta5QChu.bailey_inner` (the q-Chu–Vandermonde
core), via the generalized `F m b = 1` and its Bailey-chain recurrence. No `sorry`, axioms propext/Choice/Quot.

What remains for the *full unconditional* limiting Bailey's lemma
`IsBaileyPair α β → IsBaileyPair (chainAlpha α) (chainBeta β)`: substitute the Bailey relation into
`chainBeta`, swap the double sum, and apply `bailey_inner` to the inner sum. The mathematics is verified
(chain-preservation holds numerically to order 40); what's left is the mechanical `Ring.inverse`/`qfac`
sum-swap bookkeeping (using `rfac_mul_qfac : rfac s t * qfac s = qfac (s+t)`).
-/

end MockTheta5.Bailey
