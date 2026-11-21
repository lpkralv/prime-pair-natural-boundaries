import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.isQCont_eventuallyEq

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- For a continuation `Qc` of `Q`, `I_c` is unchanged on the region (Z1): no point of the line, and no `s - w` for
`s` in the region, lies in `Σ_Q` (as in `Ic_differentiableOn`), and `Qc = Qcont` off `Σ_Q` (`isQCont_eventuallyEq`).
Uses: `isQCont_eventuallyEq`, `Fdelta_spec`, `poleSetQ_re_bounds`, `half_le_Binf`. -/
theorem IcQ_congr (hZ1 : Z1) {Qc : ℂ → ℂ} (hQc : IsQCont Qc) {δ c : ℝ} (h : AdmC δ c) {s : ℂ}
    (hs : s ∈ RegC δ c) : IcQ Qc c s = IcQ Qcont c s := by
  unfold IcQ VerticalIntegral' VerticalIntegral
  congr 2
  apply integral_congr_ae
  filter_upwards [] with y
  have hw : (((c : ℂ) + (y : ℂ) * I)).re = c := by simp
  obtain ⟨⟨hw0, hwp⟩, ⟨hsw0, hswp⟩⟩ := E2_line_regular hZ1 h hs hw
  rw [(isQCont_eventuallyEq hQc).1 _ ⟨hw0, hwp⟩,
    (isQCont_eventuallyEq hQc).1 _ ⟨hsw0, hswp⟩]

end GoldbachBoundaries.Paper2.M1
