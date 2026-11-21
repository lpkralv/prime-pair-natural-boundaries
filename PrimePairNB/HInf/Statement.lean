import PrimePairNB.HInf.Boundary
import PrimePairNB.HInf.Fill.exists_admS
import PrimePairNB.HInf.Fill.no_extension_any_path_G
import PrimePairNB.HInf.Fill.exists_admG

/-!
# HInf: the main statements

The two main statements of the `(H_∞)` development: `boundary_GS`, the natural boundary of `G` and `S`
(paper, Theorem 1.2), and `every_path_GS`, the any-path form (paper, Corollary 8.3). Each closes with
lemmas of `HInf/`: `boundary_GS` from `boundary_G`, `boundary_S`, and `every_path_GS` from `every_path_G`,
`every_path_S` of `Boundary.lean`. The file also records that the hypotheses are met (`exists_admG`,
`exists_admS`).

The premises: `(H_∞)` is the hypothesis. (Z1) to (Z6) are `Paper2/Defs.lean`'s, the same `Prop`s.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-! ## The natural boundary of `G` and `S` -/

/-- **`boundary_GS`**: paper, Theorem 1.2 for `G` and `S` together. Under `(H_∞)` (for every `δ > 0` only
finitely many zeros have `β > 1/2 + δ`), the line `Re s = 1` is a natural boundary of `G` and `Re s = 0` of `S`, on
every admissible branch. RH is not assumed.

The shape is `Statements.thm_G_boundary`, with `catG` (`(Σ + Σ) ∩ {σ > 1}`) for the RH development's `catalogue`. -/
theorem boundary_GS (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    (∀ (g : ℂ → ℂ) (s₁ : ℂ), AdmG g s₁ → ∀ y r : ℝ, 0 < r → s₁ ∈ ball (1 + (y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r)) ∧
    (∀ (g : ℂ → ℂ) (s₁ : ℂ), AdmS g s₁ → ∀ y r : ℝ, 0 < r → s₁ ∈ ball ((y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g s₁ (ball ((y : ℂ) * I) r)) :=
  ⟨fun _ _ hg y r hr hs => boundary_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 hg y r hr hs,
    fun _ _ hg y r hr hs => boundary_S hH hZ1 hZ2 hZ3 hZ4 hZ5 hg y r hr hs⟩

/-! ## Non-vacuity -/

/-- `G` itself is an admissible germ at `3`. -/
theorem exists_admG : AdmG G 3 :=
  @Fill.exists_admG

/-- `S` itself is an admissible germ at `2`. -/
theorem exists_admS : AdmS Sser 2 :=
  @Fill.exists_admS

/-! ## Any-path form -/

/-- **`every_path_GS`**: paper, Corollary 8.3 for `G` and `S` together. A germ reached from the start region along any
path in `ℂ` and ending off the catalogue is admissible, for `G` and for `S`. The end-point restriction is removed by
`no_extension_any_path_*` and `every_path_stays_*` of `Boundary.lean`. -/
theorem every_path_GS (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    (∀ γ : C(unitInterval, ℂ), 2 < (γ 0).re → ∀ g : ℂ → ℂ, IsTerminalGerm G γ g → γ 1 ∉ catG → AdmG g (γ 1)) ∧
    (∀ γ : C(unitInterval, ℂ), 1 < (γ 0).re → ∀ g : ℂ → ℂ, IsTerminalGerm Sser γ g → γ 1 ∉ catS → AdmS g (γ 1)) :=
  ⟨fun _ h0 _ hg h1 => every_path_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 h0 hg h1,
    fun _ h0 _ hg h1 => every_path_S hH hZ1 hZ2 hZ3 hZ4 hZ5 h0 hg h1⟩

end GoldbachBoundaries.HInf
