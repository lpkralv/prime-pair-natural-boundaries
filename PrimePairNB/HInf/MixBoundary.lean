import PrimePairNB.HInf.MixNonvacuity
import PrimePairNB.HInf.MixArithmetic
import PrimePairNB.HInf.MixLocalAssembly
import PrimePairNB.HInf.MixBoundaryProof

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

/-- Natural boundary at `Re s = 1`, with seven explicit premises. -/
theorem boundary_mix (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    ∀ (g : ℂ → ℂ) (s₁ : ℂ), AdmMix g s₁ →
      ∀ y r : ℝ, 0 < r →
        s₁ ∈ ball (1 + (y : ℂ) * I) r →
        ¬ GermExtendsMeromorphically g s₁
          (ball (1 + (y : ℂ) * I) r) := by
  intro g s₁ hg y r hr hs₁
  exact MixProof.boundary_mix_aux hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 hg y r hr hs₁

end GoldbachBoundaries.HInf
