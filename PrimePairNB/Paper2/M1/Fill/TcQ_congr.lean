import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.IcQ_congr
import PrimePairNB.Paper2.M1.Fill.isQCont_eventuallyEq

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- For a continuation `Qc` of `Q`, `𝒯_c` is unchanged on the region off `Π` (Z1): add `s - a ∉ Σ_Q` for `a ∈ F_δ`
(`s ∉ Π`, `Re(s - a) > 0`) to `IcQ_congr`. Uses: `IcQ_congr`, `isQCont_eventuallyEq`, `halfPlane_two_Binf_subset`. -/
theorem TcQ_congr (hZ1 : Z1) {Qc : ℂ → ℂ} (hQc : IsQCont Qc) {δ c : ℝ} (h : AdmC δ c) {s : ℂ}
    (hs : s ∈ RegC δ c) (hP : s ∉ Pinch) : TcQ Qc δ c s = TcQ Qcont δ c s := by
  classical
  unfold TcQ
  rw [IcQ_congr hZ1 hQc h hs]
  congr 1
  apply finsum_congr
  intro a
  apply finsum_congr
  intro ha
  obtain ⟨hsa, hpa⟩ := E2_sub_regular hZ1 (E2_reg_re h hs) ha.1 hP
  rw [(isQCont_eventuallyEq hQc).1 _ ⟨hsa, hpa⟩]

end GoldbachBoundaries.Paper2.M1
