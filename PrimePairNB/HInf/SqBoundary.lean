import PrimePairNB.HInf.SqBoundaryV

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

/-- Natural boundary at `Re s = 1/2`, with seven explicit premises. -/
theorem boundary_Sq (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    ∀ (g : ℂ → ℂ) (s₁ : ℂ), AdmSq g s₁ → ∀ y r : ℝ, 0 < r →
      s₁ ∈ ball ((1/2 : ℂ) + (y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g s₁ (ball ((1/2 : ℂ) + (y : ℂ) * I) r) := by
  intro g s₁ hg y r hr hs₁
  have he : (1 + ((2 * y : ℝ) : ℂ) * I) / 2 = (1/2 : ℂ) + (y : ℂ) * I := by
    push_cast; ring
  have hball : ∀ v ∈ ball (1 + ((2 * y : ℝ) : ℂ) * I) (2 * r),
      v / 2 ∈ ball ((1/2 : ℂ) + (y : ℂ) * I) r := by
    intro v hv
    rw [mem_ball, ← he, Fill.dist_sq_half]
    have hd : dist v (1 + ((2 * y : ℝ) : ℂ) * I) < 2 * r := hv
    linarith
  have hsV : 2 * s₁ ∈ ball (1 + ((2 * y : ℝ) : ℂ) * I) (2 * r) := by
    have hd := Fill.dist_sq_half (2 * s₁) (1 + ((2 * y : ℝ) : ℂ) * I)
    rw [he, show 2 * s₁ / 2 = s₁ by ring] at hd
    have hs : dist s₁ ((1/2 : ℂ) + (y : ℂ) * I) < r := hs₁
    rw [mem_ball]
    linarith
  intro hExt
  obtain ⟨-, f, hfm, hfg⟩ := hExt
  obtain ⟨f', hf'm, hf'g, -⟩ := ThmA.exists_meromorphic_update hfm hfg
  apply Fill.boundary_SqV hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 (Fill.admSq_transfer hg)
    (2 * y) (2 * r) (by linarith) hsV
  refine ⟨hsV, fun v => f' (v / 2), fun v hv => ?_, ?_⟩
  · exact MeromorphicAt.comp_analyticAt (g := fun v : ℂ => v / 2)
      (hf'm (v / 2) (hball v hv)) (by fun_prop)
  · exact (Fill.eventuallyEq_comp_sq_half hf'g).filter_mono nhdsWithin_le_nhds

end GoldbachBoundaries.HInf
