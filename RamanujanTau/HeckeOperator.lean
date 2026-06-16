import RamanujanTau.HeckeEigenform
import RamanujanTau.HeckeTheory

/-! # The Hecke operator interface, and `TauHeckeMaster` reduced to it

Fully *constructing* the Hecke operator `T_p` on `CuspForm 𝒮ℒ k` (the double-coset sum, with proofs of
`SL₂(ℤ)`-invariance, holomorphy, and the cusp condition) is a large piece of missing Mathlib
infrastructure — not done here. What we *do* is formalize the **interface** any genuine `T_p` must satisfy
and prove that `TauHeckeMaster` follows from it. The load-bearing step is the eigenform mechanism
(`discriminant_isEigenvector`): because `dim_ℂ S₁₂ = 1`, the action of `T_p` on `Δ`'s `q`-expansion forces
its eigenvalue to be `τ(p)`, and the master identity drops out by reading off coefficients.

This **reduces** `TauHeckeMaster` to constructing one `HeckeData` term — i.e. to building `T_p` with its
standard `q`-expansion action. It does *not* discharge it unconditionally; that needs the operator
construction (the genuine Mathlib gap). The kernel will not let us pretend otherwise.
-/

open scoped MatrixGroups
open ModularForm

namespace RamanujanTau

/-- The interface a genuine Hecke operator system on weight-12 cusp forms must satisfy:
* `T p` — a ℂ-linear endomorphism of `CuspForm 𝒮ℒ 12` for each prime `p` (the operator `T_p`);
* `coeff` — the `q`-expansion coefficient functional, ℂ-linear in the form;
* `coeff_discriminant` — the bridge `coeff Δ n = τ(n)` (this repo's `MathlibBridge`, still TBD);
* `hecke_action` — the standard action `(T_p f)_n = f_{p n} + p¹¹ · f_{n/p}`.

Constructing a term of this structure is exactly the missing infrastructure (build `T_p`, prove it lands
in cusp forms with this action). Given one, `TauHeckeMaster` follows (`HeckeData.tauHeckeMaster`). -/
structure HeckeData where
  T : ℕ → Module.End ℂ (CuspForm 𝒮ℒ 12)
  coeff : CuspForm 𝒮ℒ 12 → ℕ → ℂ
  coeff_smul : ∀ (c : ℂ) (f : CuspForm 𝒮ℒ 12) (n : ℕ), coeff (c • f) n = c * coeff f n
  coeff_discriminant : ∀ n : ℕ, coeff CuspForm.discriminant n = (tau n : ℂ)
  hecke_action : ∀ {p : ℕ}, p.Prime → ∀ (f : CuspForm 𝒮ℒ 12) (n : ℕ),
    coeff (T p f) n = coeff f (p * n) + (p : ℂ) ^ 11 * (if p ∣ n then coeff f (n / p) else 0)

/-- **`TauHeckeMaster` follows from the Hecke operator interface.** Given `HeckeData`, the eigenform
mechanism forces `T_p Δ = τ(p) • Δ`, and reading off the `q`-expansion gives the master identity. -/
theorem HeckeData.tauHeckeMaster (H : HeckeData) : TauHeckeMaster where
  master {p} hp n _ := by
    -- 1-dimensionality ⟹ Δ is an eigenvector of T_p:  T_p Δ = c • Δ
    obtain ⟨c, hc⟩ := discriminant_isEigenvector (H.T p)
    have hp1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
    -- read coefficient 1 to pin the eigenvalue:  c = τ(p)
    have hcval : c = (tau p : ℂ) := by
      have e := H.hecke_action hp CuspForm.discriminant 1
      rw [hc, H.coeff_smul] at e
      simp only [H.coeff_discriminant, mul_one, if_neg hp1, mul_zero, add_zero, tau_one] at e
      simpa using e
    -- read coefficient n:  τ(p)·τ(n) = τ(pn) + p¹¹·[p∣n] τ(n/p)   (in ℂ), then cast to ℤ
    have en := H.hecke_action hp CuspForm.discriminant n
    rw [hc, H.coeff_smul, hcval] at en
    simp only [H.coeff_discriminant] at en
    rw [mul_ite, mul_zero] at en
    by_cases hpn : p ∣ n
    · rw [if_pos hpn] at en ⊢; exact_mod_cast en
    · rw [if_neg hpn] at en ⊢; exact_mod_cast en

end RamanujanTau
