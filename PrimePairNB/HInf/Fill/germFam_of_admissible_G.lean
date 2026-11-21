import PrimePairNB.HInf.Fill.continuesAlong_G
import PrimePairNB.HInf.Fill.isPinchKernel_G
import PrimePairNB.HInf.Fill.uniformFamily_germFam

/-!
# `germFam_of_admissible_G`

The family is uniform and a property of germs, so `ThmA.continuationAlong_preserve` carries membership along the path.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **The description.** Every germ reached from `σ > 2` along a path in `{σ > 2B_∞} ∖ X` is
`D^θ + m`. -/
theorem germFam_of_admissible_G (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {g : ℂ → ℂ} {q : ℂ}
    (hg : IsAdmissibleGermOn G (VInf ⊤ \ Pinch) (halfPlane 2) g q) : GermFam kerG ⊤ 0 q g := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := hg
  have hstart : GermFam kerG ⊤ 0 (γ 0) (f 0) :=
    germFam_congr (germFam_G_start hZ1 hZ2 hZ3 hZ6 h0) hf0.symm
  exact germFam_congr (ThmA.continuationAlong_preserve
    (uniformFamily_germFam hZ1 hZ2 hZ3 (isPinchKernel_G hZ6) 0)
    (fun _ _ _ h hfg => germFam_congr h hfg) hγ hf hstart 1) hg1.symm

end GoldbachBoundaries.HInf.Fill
