import PrimePairNB.HInf.Fill.uniformFamily_germFam
import PrimePairNB.HInf.Fill.Dth_eq
import PrimePairNB.HInf.Fill.isPinchKernel_G
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-!
# `continuesAlong_G`

On `σ > 2` the germ of `G` is in the family (`Dth_eq_G`), and a uniform family continues along every path.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- On `σ > 2`, the germ of `G` is in `𝔊` with `C = 0`. -/
theorem germFam_G_start (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {q : ℂ} (h2 : 2 < q.re) :
    GermFam kerG ⊤ 0 q G := by
  refine ⟨0, mem_Om_of_two_lt hZ1 ⟨by linarith, EReal.coe_lt_top _⟩ h2, 0, zero_mem _, ?_⟩
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2] with v hv
  simp [Dth_eq_G hZ1 hZ2 hZ3 hZ6 0 hv]

/-- **Existence.** `G` continues along every path in `{σ > 2B_∞} ∖ X` from `σ > 2`. Unconditional up to the premises. -/
theorem continuesAlong_G (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {γ : C(unitInterval, ℂ)}
    (hγ : ∀ t, γ t ∈ VInf ⊤ \ Pinch) (h0 : 2 < (γ 0).re) : ContinuesAlong G γ := by
  obtain ⟨f, hf, hf0, -⟩ := ThmA.exists_continuationAlong_of_uniform
    (uniformFamily_germFam hZ1 hZ2 hZ3 (isPinchKernel_G hZ6) 0) hγ (germFam_G_start hZ1 hZ2 hZ3 hZ6 h0)
  exact ⟨f, hf, hf0⟩

end GoldbachBoundaries.HInf.Fill
