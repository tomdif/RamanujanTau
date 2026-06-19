/-
# Jacobi triple product campaign, Rung 4 (step L1): the one-sided infinite product

Rung 4 bridges the finite one-sided JTP (`finite_jtp`) to the full bilateral JTP (`bilateralTheta`). A
multi-agent route scout established the most formalizable path and — crucially — that there is **no hidden
analysis wall**: every `n→∞` limit is *coefficient stabilization*, the purely-algebraic idiom already used for
`(q;q)_∞` and the bilateral theta series. The route (each step lands on lemmas we already have, except the two
genuinely-new q-series identities L4 and L7):

  L1  [HERE]  `jtpProd_coeff_stable` + `jtpProdInf` — the one-sided infinite product `∏_{i≥0}(1+z q^{2i+1})`
              via q-degree stabilization (clone of `coeff_qfac_stable`).
  L2          `[n,k]_{q²} → 1/(q²;q²)_k` as `n→∞` (from `gaussBinom_eq_inv` + qfac stabilization).
  L3          the finite RHS sum stabilizes to `Σ_k q^{k²} zᵏ / (q²;q²)_k`.
  L4  [NEW]   one-sided Cauchy/Euler identity `jtpProdInf = Σ_k q^{k²} zᵏ/(q²;q²)_k` (= limit of `finite_jtp`).
  L5          move to `ℤ[z;z⁻¹]`-coefficients; the `z⁻¹` mirror identity.
  L6          `(q²;q²)_∞` prefactor (instantiate `qfacInf` at `q²` via `expand 2`).
  L7  [NEW]   bilateralization: `(q²;q²)_∞ · (Σ q^{k²}zᵏ/(q²;q²)_k)(Σ q^{j²}z⁻ʲ/(q²;q²)_j) = Σ_{n∈ℤ} zⁿ q^{n²}`
              (per-diagonal q-Vandermonde; reuses `gaussBinom_mul_qfac` / the q-Chu–Vandermonde core).
  L8          assemble the full JTP.

Honest scope: Rung 4 is multi-session; L4 and L7 are original combinatorial formalization, not template-copying.
This file is L1 (the safe, decoupled entry). No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiFinite
import RamanujanTau.MockTheta5Lemmas

namespace MockTheta5.Bailey
open Polynomial

/-- The one-sided JTP product `∏_{i<N}(1 + z·q^{2i+1})`, over `Polynomial (ℤ⟦q⟧)` (`z = X`). -/
noncomputable def jtpProd (N : ℕ) : Polynomial (PowerSeries ℤ) :=
  ∏ i ∈ Finset.range N, (1 + C (qq ^ (2 * i + 1)) * Polynomial.X)

/-- **L1**: q-degree stabilization. The `q^k` coefficient of every `z^j` coefficient of the product is the
same for all `N` with `2N+1 > k` — the new factor `(1 + z·q^{2N+1})` is `1` modulo `q`-degree `2N+1`.
This is the product analogue of `coeff_qfac_stable`. -/
lemma jtpProd_coeff_stable {k : ℕ} : ∀ {M N : ℕ}, k < 2 * M + 1 → M ≤ N → ∀ j,
    PowerSeries.coeff k (Polynomial.coeff (jtpProd N) j)
      = PowerSeries.coeff k (Polynomial.coeff (jtpProd M) j) := by
  intro M N hk hMN
  induction N with
  | zero => obtain rfl : M = 0 := Nat.le_zero.mp hMN; intro j; rfl
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · intro j
        have hstep : jtpProd (N + 1)
            = jtpProd N + C (qq ^ (2 * N + 1)) * Polynomial.X * jtpProd N := by
          rw [jtpProd, Finset.prod_range_succ, ← jtpProd]; ring
        rw [hstep, Polynomial.coeff_add, map_add]
        have hz : PowerSeries.coeff k
            (Polynomial.coeff (C (qq ^ (2 * N + 1)) * Polynomial.X * jtpProd N) j) = 0 := by
          rw [mul_assoc, Polynomial.coeff_C_mul]
          exact MockTheta5.mt_coeff_Xpow_mul_zero _ (2 * N + 1) k (by omega)
        rw [hz, add_zero, ih (by omega) j]
      · obtain rfl : M = N + 1 := by omega
        intro j; rfl

/-- **The one-sided infinite product `∏_{i≥0}(1 + z·q^{2i+1})`** as a double power series `ℤ⟦q⟧⟦z⟧`,
defined by q-degree coefficient stabilization (the `z^j` coefficient is a genuine `q`-series). -/
noncomputable def jtpProdInf : PowerSeries (PowerSeries ℤ) :=
  PowerSeries.mk fun j => PowerSeries.mk fun k =>
    PowerSeries.coeff k (Polynomial.coeff (jtpProd (k + 1)) j)

/-- Defining property: the `q^k`-coefficient of the `z^j`-coefficient of the infinite product equals that of
any finite truncation `jtpProd N` with `2N+1 > k`. -/
lemma coeff_jtpProdInf (j : ℕ) {k N : ℕ} (hN : k < 2 * N + 1) :
    PowerSeries.coeff k (PowerSeries.coeff j jtpProdInf)
      = PowerSeries.coeff k (Polynomial.coeff (jtpProd N) j) := by
  rw [jtpProdInf, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  rcases le_total N (k + 1) with h | h
  · exact jtpProd_coeff_stable hN h j
  · exact (jtpProd_coeff_stable (by omega) h j).symm

end MockTheta5.Bailey
