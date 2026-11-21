import PrimePairNB.Paper2.M2.Lambda
import PrimePairNB.Paper2.M2.Fill.Binf_eq_half_of_Hinf

/-!
# Targets for the boundary theorem for `T` (Paper, Theorem 1.1)

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a proof from the lemmas of this directory and of `M1`. Each target
is proved in the file that its dependants import:

| Target | File |
|---|---|
| `lem_Q_iii_proof` | `QCount.lean` |
| `lem_rigidity_proof`, `lem_rigidity_converse_proof` | `Rigidity.lean` |
| `thm_single_proof` | `Single.lean` |
| `lem_far_proof`, `lem_far_abs_proof` | `Far.lean` |
| `prop_Lambda_proof` | `Lambda.lean` |
| `thm_boundary_proof` | this file |

`thm_boundary` is proved from `prop_Lambda_proof` (its counting core) and the residue theorem: a point `s₀ = 1 + ρ/q`
with `𝓡(s₀) ≠ 0` is a pole of every admissible `F`, because
`Res_{s₀} F = 𝓡(s₀)` (`hasResidue_Tcont`, `eventuallyEq_Tcont_of_codiscrete`) and a non-zero residue of a
meromorphic function is a simple pole (`HasResidue.meromorphicOrderAt_eq_neg_one`).

Of the hypotheses, `lem_far` and `lem_far_abs` use (Z6) (Stirling on `[1 - B, B]`); `thm_boundary` carries (Z6)
through them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `thm_boundary` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_boundary_proof (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      (∀ y ε : ℝ, 0 < ε →
        {s | s ∈ ball (1 + (y : ℂ) * I) ε ∧ s ∈ HH ∧ meromorphicOrderAt F s < 0}.Infinite) ∧
      IsNaturalBoundary F HH lineOne := by
  have hB : Bsup < 1 := Bsup_lt_one_of_Hinf hH
  have hBinf : Binf = 1 / 2 := Binf_eq_half_of_Hinf hZ1 hH
  have hHH : halfPlane (2 * Binf) = HH := by
    rw [hBinf]
    norm_num
  obtain ⟨hmero, -, -⟩ := Tcont_props hZ1 hZ2 hZ3
  rw [hHH] at hmero
  refine ⟨⟨Tcont, hmero, Tcont_eqOn_T hZ1 hZ2 hZ3⟩, fun F hF hFT => ?_⟩
  have hF' : MeromorphicOn F (halfPlane (2 * Binf)) := by
    rw [hHH]
    exact hF
  have hpoles : ∀ y ε : ℝ, 0 < ε →
      {s | s ∈ ball (1 + (y : ℂ) * I) ε ∧ s ∈ HH ∧ meromorphicOrderAt F s < 0}.Infinite := by
    intro y ε hε
    refine (prop_Lambda_proof hZ1 hZ2 hZ4 hZ5 hZ6 hB y ε hε).mono ?_
    rintro s ⟨ρ, hρ, -, q, hq, rfl, hball, hne⟩
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hre : 1 < (1 + ρ / (q : ℂ)).re := by
      have h : (1 + ρ / (q : ℂ)).re = 1 + ρ.re / q := by simp
      rw [h]
      have := div_pos hρ.2.1 hq0
      linarith
    have hsH : 1 + ρ / (q : ℂ) ∈ HH := hre
    have hs₀ : 2 * Binf < (1 + ρ / (q : ℂ)).re := by
      rw [hBinf]
      linarith
    have hev := eventuallyEq_Tcont_of_codiscrete hZ1 hZ2 hZ3 hF' hFT hs₀
    have hres : HasResidue F (1 + ρ / (q : ℂ)) (pairSum (1 + ρ / (q : ℂ))) :=
      (hasResidue_Tcont hZ1 hZ2 hZ3 hs₀).congr hev.symm
    refine ⟨hball, hsH, ?_⟩
    rw [hres.meromorphicOrderAt_eq_neg_one (hF _ hsH) hne]
    decide
  refine ⟨hpoles, fun z₀ hz₀ => ?_⟩
  have hz₀re : z₀.re = 1 := hz₀
  refine noMeromorphicExtensionAt_of_poles_in_every_ball (isOpen_halfPlane 1) fun ε hε => ?_
  have hz : (1 : ℂ) + (z₀.im : ℂ) * I = z₀ := by
    apply Complex.ext <;> simp [hz₀re]
  obtain ⟨s, hs⟩ := (hpoles z₀.im ε hε).nonempty
  obtain ⟨hsb, hsH, hso⟩ := hs
  rw [hz] at hsb
  refine ⟨s, hsH, ?_, hsb, hso⟩
  intro h
  have h1 : 1 < s.re := hsH
  rw [h, hz₀re] at h1
  exact lt_irrefl _ h1

end GoldbachBoundaries.Paper2.M2
