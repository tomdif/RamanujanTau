import RamanujanTau.Gegenbauer

/-! # The same machinery is elliptic-curve machinery: `a_{p^r}` via Gegenbauer

The Gegenbauer closed form we proved for `τ` is **weight-agnostic** — `gegen` and `gegen_eq_sum` are about
the bare recurrence `a_{r+2} = s·a_{r+1} − q·a_r`, with no mention of `τ` or weight 12. So the *entire*
elliptic-curve story falls out with **zero new proof**:

| | Ramanujan `Δ` (weight 12) | Elliptic curve `E` (weight 2) |
|---|---|---|
| Hecke recurrence | `τ(p^{r+1}) = τ(p)τ(p^r) − p^{11}τ(p^{r-1})` | `a_{p^{r+1}} = a_p a_{p^r} − p·a_{p^{r-1}}` |
| closed form | `τ(p^r) = G_r(τ(p), p^{11})` | `a_{p^r} = G_r(a_p, p)` |
| Deligne / **Hasse** | `\|τ(p)\| ≤ 2 p^{11/2}` | `\|a_p\| ≤ 2√p` |

Only `q = p^{11}` becomes `q = p`. Below: the weight-agnostic core `seq_eq_gegen` (extracted from
`tau_ppow_eq_gegen`), its elliptic-curve instantiation giving `a_{p^r} = Σ_j (−1)^j C(r−j,j) p^j a_p^{r−2j}`,
the closed form `a_{p²} = a_p² − p`, and a **computable** `a_p` (point counting) with a `native_decide`-
verified **Hasse bound** — the weight-1 shadow of the `DeligneBound` we formalized for `τ`.
-/

open Finset

namespace RamanujanTau

/-- **Weight-agnostic core.** Any integer sequence with `a_{r+2} = s·a_{r+1} − q·a_r`, `a_0 = 1`, `a_1 = s`
equals the Gegenbauer / Chebyshev-U polynomial `G_r(s,q)`. Both `τ` (`q = p^{11}`) and elliptic-curve
`L`-coefficients (`q = p`) are instances. -/
theorem seq_eq_gegen (s q : ℤ) (a : ℕ → ℤ) (h0 : a 0 = 1) (h1 : a 1 = s)
    (hrec : ∀ r, a (r + 2) = s * a (r + 1) - q * a r) : ∀ r, a r = gegen s q r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | _ | k
    · rw [h0, gegen_zero]
    · rw [h1, gegen_one]
    · rw [show k + 1 + 1 = k + 2 from rfl, hrec k, gegen_succ_succ,
          ih (k + 1) (by omega), ih k (by omega)]

/-- **Elliptic-curve `L`-coefficients via Gegenbauer (weight 1, `q = p`).** If `a_{p^r}` satisfies the
Hecke recurrence `a_{p^{r+1}} = a_p·a_{p^r} − p·a_{p^{r-1}}` (with `a_{p^0}=1`, `a_{p^1}=a_p`), then
`a_{p^r} = Σ_j (−1)^j C(r−j,j) p^j a_p^{r−2j}` — the *same* binomial sum as `tau_ppow_eq_sum`, with `p`
in place of `p^{11}`. -/
theorem ell_coeff_eq_sum (ap : ℤ) (p : ℕ) (a : ℕ → ℤ)
    (h0 : a 0 = 1) (h1 : a 1 = ap) (hrec : ∀ r, a (r + 2) = ap * a (r + 1) - (p : ℤ) * a r) (r : ℕ) :
    a r = ∑ j ∈ range (r + 1), (-1) ^ j * (Nat.choose (r - j) j : ℤ) * (p : ℤ) ^ j * ap ^ (r - 2 * j) := by
  rw [seq_eq_gegen ap (p : ℤ) a h0 h1 hrec r, gegen_eq_sum]

/-- The weight-1 analog of `tau_prime_sq`: `a_{p²} = a_p² − p`. -/
theorem ell_ap_sq (ap : ℤ) (p : ℕ) (a : ℕ → ℤ)
    (h0 : a 0 = 1) (h1 : a 1 = ap) (hrec : ∀ r, a (r + 2) = ap * a (r + 1) - (p : ℤ) * a r) :
    a 2 = ap ^ 2 - (p : ℤ) := by
  have h := hrec 0; rw [h0, h1] at h; rw [h]; ring

/-! ## Computable `a_p` and the Hasse bound -/

/-- `#E(𝔽_p)` for `y² = x³ + a x + b` (affine points + the point at infinity), by brute force. -/
def ecOrder (p a b : ℕ) : ℕ :=
  1 + ((range p ×ˢ range p).filter
        (fun xy => (xy.2 ^ 2) % p = (xy.1 ^ 3 + a * xy.1 + b) % p)).card

/-- The trace of Frobenius `a_p = p + 1 − #E(𝔽_p)` (the weight-2 Hecke eigenvalue at `p`). -/
def ecAp (p a b : ℕ) : ℤ := (p : ℤ) + 1 - (ecOrder p a b : ℤ)

/-- `a_p = −9` for `y² = x³ + 4x + 4` over `𝔽₁₀₃` (`#E = 113`). -/
theorem ecAp_example : ecAp 103 4 4 = -9 := by native_decide

/-- **Hasse bound** `a_p² ≤ 4p` for the same curve — the weight-1 shadow of Deligne's `|τ(p)| ≤ 2p^{11/2}`
(`DeligneBound`). Here `81 ≤ 412`. -/
theorem ecHasse_example : (ecAp 103 4 4) ^ 2 ≤ 4 * 103 := by native_decide

end RamanujanTau
