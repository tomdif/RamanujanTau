import RamanujanTau.Basic
import RamanujanTau.SmallValues
import RamanujanTau.HeckeRecurrence
import RamanujanTau.Multiplicativity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # The Euler factor of the Ramanujan L-function, and prime-power closed forms

Everything here is a *proven* general theorem (for all primes `p`), derived from the
`TauHeckeRecurrence` hypothesis class — not a `native_decide` instance. Where the
repo previously had only numerical checks (`τ(4) = τ(2)² − 2¹¹`, etc.), we prove the
general closed forms and assemble them into the local **Euler factor**

`L_p(Δ, X) := (1 − τ(p) X + p¹¹ X²)⁻¹ = ∑_{r≥0} τ(p^r) X^r`,

i.e. `(1 − τ(p) X + p¹¹ X²) · (∑_{r} τ(p^r) X^r) = 1` in `ℤ⟦X⟧`. This is the heart of
the Hecke theory of `τ`: it says the Dirichlet series `∑ τ(n) n^{-s}` has an Euler
product `∏_p (1 − τ(p) p^{-s} + p^{11-2s})⁻¹`. Under multiplicativity we also prove
`τ` is determined by its prime-power values.
-/

namespace RamanujanTau

open PowerSeries

section Recurrence
variable [TauHeckeRecurrence]

omit [TauHeckeRecurrence] in
/-- `τ(p⁰) = 1` (boundary value of the prime-power sequence). -/
@[simp]
theorem tau_ppow_zero (p : ℕ) : τ (p ^ 0) = 1 := by rw [pow_zero]; exact tau_one

omit [TauHeckeRecurrence] in
/-- `τ(p¹) = τ(p)`. -/
@[simp]
theorem tau_ppow_one (p : ℕ) : τ (p ^ 1) = τ p := by rw [pow_one]

/-- **General closed form:** `τ(p²) = τ(p)² − p¹¹` for every prime `p`. -/
theorem tau_prime_sq {p : ℕ} (hp : p.Prime) : τ (p ^ 2) = τ p ^ 2 - (p : ℤ) ^ 11 := by
  have h := TauHeckeRecurrence.hecke hp 1 (le_refl 1)
  rw [show (1 : ℕ) + 1 = 2 from rfl, show (1 : ℕ) - 1 = 0 from rfl,
      tau_ppow_zero, tau_ppow_one] at h
  rw [h]; ring

/-- **General closed form:** `τ(p³) = τ(p)³ − 2 p¹¹ τ(p)`. -/
theorem tau_prime_cube {p : ℕ} (hp : p.Prime) :
    τ (p ^ 3) = τ p ^ 3 - 2 * (p : ℤ) ^ 11 * τ p := by
  have h := TauHeckeRecurrence.hecke hp 2 (by norm_num)
  rw [show (2 : ℕ) + 1 = 3 from rfl, show (2 : ℕ) - 1 = 1 from rfl, tau_ppow_one] at h
  rw [h, tau_prime_sq hp]; ring

/-- **Three-term recurrence** (clean form), for every prime `p` and `r ≥ 1`:
`τ(p^{r+1}) − τ(p)·τ(p^r) + p¹¹·τ(p^{r-1}) = 0`. -/
theorem tau_three_term {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) :
    τ (p ^ (r + 1)) - τ p * τ (p ^ r) + (p : ℤ) ^ 11 * τ (p ^ (r - 1)) = 0 := by
  have h := TauHeckeRecurrence.hecke hp r hr; linarith

/-- The recurrence re-indexed so it holds for **all** `r ≥ 0` (the Euler-factor coefficient
relation): `τ(p^{r+2}) − τ(p)·τ(p^{r+1}) + p¹¹·τ(p^r) = 0`. -/
theorem euler_factor_coeff {p : ℕ} (hp : p.Prime) (r : ℕ) :
    τ (p ^ (r + 2)) - τ p * τ (p ^ (r + 1)) + (p : ℤ) ^ 11 * τ (p ^ r) = 0 := by
  have h := TauHeckeRecurrence.hecke hp (r + 1) (by omega)
  rw [show r + 1 + 1 = r + 2 from rfl, show r + 1 - 1 = r from rfl] at h
  linarith

/-- The generating function of `τ` along the powers of a fixed prime `p`:
`G_p(X) = ∑_{r≥0} τ(p^r) X^r ∈ ℤ⟦X⟧`. -/
noncomputable def tauPrimeGF (p : ℕ) : PowerSeries ℤ := PowerSeries.mk fun r => τ (p ^ r)

omit [TauHeckeRecurrence] in
@[simp]
theorem coeff_tauPrimeGF (p r : ℕ) :
    (coeff r) (tauPrimeGF p) = τ (p ^ r) := coeff_mk r _

/-- **Euler factor of the Ramanujan L-function.** For every prime `p`,
`(1 − τ(p) X + p¹¹ X²) · ∑_{r} τ(p^r) X^r = 1` in `ℤ⟦X⟧`.

Equivalently `∑_r τ(p^r) X^r = (1 − τ(p) X + p¹¹ X²)⁻¹`, the local factor of
`L(Δ, s) = ∏_p (1 − τ(p) p^{-s} + p^{11 - 2s})⁻¹`. -/
theorem euler_factor {p : ℕ} (hp : p.Prime) :
    (1 - C (τ p) * X + C ((p : ℤ) ^ 11) * X ^ 2) * tauPrimeGF p = 1 := by
  ext n
  have e1 : (coeff n) (X * tauPrimeGF p) = if 1 ≤ n then τ (p ^ (n - 1)) else 0 := by
    have h := coeff_X_pow_mul' (tauPrimeGF p) 1 n
    rw [pow_one] at h; rw [h]; simp
  have e2 : (coeff n) (X ^ 2 * tauPrimeGF p) = if 2 ≤ n then τ (p ^ (n - 2)) else 0 := by
    have h := coeff_X_pow_mul' (tauPrimeGF p) 2 n
    rw [h]; simp
  rw [coeff_one, add_mul, sub_mul, one_mul, map_add, map_sub,
      mul_assoc (C (τ p)) X (tauPrimeGF p),
      mul_assoc (C ((p : ℤ) ^ 11)) (X ^ 2) (tauPrimeGF p),
      coeff_C_mul, coeff_C_mul, coeff_tauPrimeGF, e1, e2]
  rcases n with _ | _ | k
  · simp [tau_one]
  · simp [tau_one]
  · have h1 : (1 : ℕ) ≤ k + 1 + 1 := by omega
    have h2 : (2 : ℕ) ≤ k + 1 + 1 := by omega
    have h0 : ¬ (k + 1 + 1 = 0) := by omega
    have ea : k + 1 + 1 - 1 = k + 1 := by omega
    have eb : k + 1 + 1 - 2 = k := by omega
    have ec : k + 1 + 1 = k + 2 := by omega
    rw [if_pos h1, if_pos h2, if_neg h0, ea, eb, ec]
    have hrec := euler_factor_coeff hp k
    linarith

end Recurrence

section Multiplicative
variable [TauMultiplicative]

/-- **τ is determined by its prime-power values.** For `n ≠ 0`,
`τ(n) = ∏_{p^k ‖ n} τ(p^k)` (product over the prime factorization). -/
theorem tauArith_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    tauArith n = n.factorization.prod fun p k => tauArith (p ^ k) :=
  tauArith_isMultiplicative.multiplicative_factorization _ hn

end Multiplicative

end RamanujanTau
