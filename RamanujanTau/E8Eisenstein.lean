import Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne

/-! # Completing the bridge: `Θ_{E₈} = E₄`

`OctonionBridge` anchored the `unifiedtheory` octonion/E₈ sector to Ramanujan's modular world through the
number `240` (E₈ roots `=` E₄'s first `q`-coefficient). The conceptual capstone is the theorem
`Θ_{E₈} = E₄`: the theta series of the E₈ lattice *is* the weight-4 Eisenstein series.

Its hard half — that the theta series of an even unimodular rank-8 lattice is a **modular form of weight
4** (Poisson summation / the `S,T` transformation law of lattice theta) — is not in Mathlib, and we do not
fake it. We capture it as a hypothesis: an `E8ThetaData` packages `Θ_{E₈}` *as* a `ModularForm 𝒮ℒ 4`
(its modularity) together with constant term `1` (unimodularity: a single vector of norm 0).

The other half — **rigidity** — we prove outright: because `dim_ℂ M₄(SL₂ℤ) = 1` (Mathlib), any weight-4
modular form with constant term `1` *equals* `E₄`. Hence, given `E8ThetaData`, `Θ_{E₈} = E₄`, and its
`q¹` coefficient is forced to be `240` — so the **240 E₈ roots are not a numerical coincidence with E₄;
they are determined by the one-dimensionality of `M₄`.** That completes the bridge, conditional on the one
honest, standard gap (lattice-theta modularity).
-/

open UpperHalfPlane ModularForm SlashInvariantForm SlashInvariantFormClass ModularFormClass EisensteinSeries
open scoped MatrixGroups

namespace RamanujanTau

/-- **Rigidity of weight-4 forms.** Since `dim_ℂ M₄(SL₂ℤ) = 1` and `E₄` has constant term `1`, any
weight-4 modular form with constant term `1` equals `E₄`. -/
theorem weight4_eq_E4_of_const (f : ModularForm 𝒮ℒ 4)
    (h : (qExpansion 1 (f : ℍ → ℂ)).coeff 0 = 1) : f = E₄ := by
  obtain ⟨c, hc⟩ : ∃ c, c • E₄ = f :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) _
  have key : c = 1 := by
    have hq : c • qExpansion 1 (E₄ : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) := by
      rw [← ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL c E₄,
          show (c • (E₄ : ℍ → ℂ)) = (f : ℍ → ℂ) from congrArg DFunLike.coe hc]
    have e : (PowerSeries.coeff (R := ℂ) 0) (c • qExpansion 1 (E₄ : ℍ → ℂ))
           = (PowerSeries.coeff (R := ℂ) 0) (qExpansion 1 (f : ℍ → ℂ)) := by rw [hq]
    rw [map_smul, E_qExpansion_coeff_zero _ ⟨2, rfl⟩, h] at e
    simpa using e
  rw [← hc, key, one_smul]

/-- The theta series of the E₈ lattice, presented as the data Mathlib does not yet supply: it **is** a
weight-4 modular form (the missing Poisson-summation modularity theorem, here a hypothesis), with constant
term `1` (the lattice is even unimodular — one vector of norm `0`). -/
structure E8ThetaData where
  /-- `Θ_{E₈}` as a weight-4 modular form (encodes the modularity of the lattice theta series). -/
  Θ : ModularForm 𝒮ℒ 4
  /-- Constant term `1`: the even unimodular lattice has a unique vector of norm `0`. -/
  const_one : (qExpansion 1 (Θ : ℍ → ℂ)).coeff 0 = 1

/-- **`Θ_{E₈} = E₄`.** Given the E₈ theta series as a weight-4 modular form with constant term `1`, the
rigidity of `M₄` forces it to equal the Eisenstein series `E₄`. -/
theorem E8ThetaData.eq_E4 (D : E8ThetaData) : D.Θ = E₄ :=
  weight4_eq_E4_of_const D.Θ D.const_one

/-- **The 240 E₈ roots, forced by modularity.** Consequently `Θ_{E₈}`'s `q¹` coefficient is `240`: the
E₈ root count is determined — not coincident — because `M₄` is one-dimensional. -/
theorem E8ThetaData.root_count (D : E8ThetaData) :
    (qExpansion 1 (D.Θ : ℍ → ℂ)).coeff 1 = 240 := by
  rw [D.eq_E4]; exact E₄_qExpansion_coeff_one

end RamanujanTau
