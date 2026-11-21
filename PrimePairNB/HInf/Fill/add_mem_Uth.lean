import PrimePairNB.HInf.Defs

/-! Proof of `add_mem_Uth`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- Each point of `U_θ` flows east inside `U_θ`. -/
theorem add_mem_Uth {κ : ℝ} {z : ℂ} (hz : z ∈ Uth κ) {t : ℝ} (ht : 0 ≤ t) :
    z + (t : ℂ) * slantDir κ ∈ Uth κ := by
  refine ⟨?_, fun h => hz.2 ?_⟩
  · have h0 : 0 < z.re := hz.1
    show 0 < (z + (t : ℂ) * slantDir κ).re
    simp [slantDir]
    linarith
  · obtain ⟨a, ha, s, hs, he⟩ := mem_iUnion₂.mp h
    refine mem_iUnion₂.mpr ⟨a, ha, s + t, by linarith, ?_⟩
    push_cast
    linear_combination he

end GoldbachBoundaries.HInf.Fill
