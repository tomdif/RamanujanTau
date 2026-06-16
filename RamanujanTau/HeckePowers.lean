import RamanujanTau.EulerFactor

/-! # Higher prime-power closed forms for `τ`, discovered via proofworld + kernel-gated

`τ(p⁴)` and `τ(p⁵)` as polynomials in `τ(p)` and `p`, derived from the Hecke recurrence and the
lower closed forms. These were PROPOSED by the proofworld LLM generator and VERIFIED by the Lean
kernel (each via `rw [recurrence, lower forms]; ring`); only kernel-certified forms appear here.
They continue the Euler-factor / Chebyshev-style structure: the coefficients are the Gegenbauer
numbers of the recurrence `τ(p^{r+1}) = τ(p)·τ(p^r) − p¹¹·τ(p^{r-1})`. -/

namespace RamanujanTau

variable [TauHeckeRecurrence]

/-- **τ(p⁴)** closed form (proofworld-discovered, kernel-verified). -/
theorem tau_prime_p4 {p : ℕ} (hp : p.Prime) : τ (p ^ 4) = τ p ^ 4 - 3 * (p:ℤ)^11 * τ p ^ 2 + (p:ℤ)^22 := by
  have h := TauHeckeRecurrence.hecke hp 3 (by norm_num)
  rw [show (3 : ℕ) + 1 = 4 from rfl, show (3 : ℕ) - 1 = 2 from rfl] at h
  rw [h, tau_prime_cube hp, tau_prime_sq hp]; ring

/-- **τ(p⁵)** closed form (proofworld-discovered, kernel-verified). -/
theorem tau_prime_p5 {p : ℕ} (hp : p.Prime) : τ (p ^ 5) = τ p ^ 5 - 4 * (p:ℤ)^11 * τ p ^ 3 + 3 * (p:ℤ)^22 * τ p := by
  have h := TauHeckeRecurrence.hecke hp 4 (by norm_num)
  rw [show (4 : ℕ) + 1 = 5 from rfl, show (4 : ℕ) - 1 = 3 from rfl] at h
  rw [h, tau_prime_p4 hp, tau_prime_cube hp]; ring

end RamanujanTau
