import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.Ic_differentiableOn
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.isOpen_RegC

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `𝒯_c` is holomorphic at points of its region off `Π` (Z1, Z2, Z3): near such a point the indicators are constant,
`I_c` is holomorphic (`Ic_differentiableOn`), `K_s(a)` is holomorphic in `s` for `σ > Re a`, and `Q(s - a)` is analytic
because `s - a ∉ Σ_Q`. Uses: `Ic_differentiableOn`, `isOpen_RegC`, `poleSetQ_re_bounds`, `half_le_Binf`,
`analyticAt_Qcont_sub_sum`, `regular_of_not_mem_poleSetQ`. -/
theorem Tc_analyticAt (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c : ℝ} (h : AdmC δ c) {s₀ : ℂ} (hs₀ : s₀ ∈ RegC δ c)
    (hP : s₀ ∉ Pinch) : AnalyticAt ℂ (Tc δ c) s₀ := by
  classical
  have hF := (Fdelta_spec hZ1 δ h.1).1
  have hI : AnalyticAt ℂ (IcQ Qcont c) s₀ :=
    (Ic_differentiableOn hZ1 hZ2 hZ3 h).analyticAt ((isOpen_RegC hZ1 h).mem_nhds hs₀)
  have hs := E2_reg_re h hs₀
  have hsum : AnalyticAt ℂ (fun s => ∑ a ∈ hF.toFinset,
      nu c a s₀ * Rcoef a * KerS s a * Qcont (s - a)) s₀ := by
    apply Finset.analyticAt_fun_sum
    intro a ha
    have hap := (hF.mem_toFinset.mp ha).1
    obtain ⟨hsa, hpa⟩ := E2_sub_regular hZ1 hs hap hP
    have hka : a.re < s₀.re := halfPlane_two_Binf_subset hZ1 hap hs
    exact (analyticAt_const.fun_mul (E2_analytic_KerS hka)).fun_mul
      ((E2_analytic_Qcont hsa hpa).fun_comp (f := fun z : ℂ => z - a)
        (analyticAt_id.sub analyticAt_const))
  exact (hI.fun_add hsum).congr (E2_Tc_eventuallyEq hF hs₀).symm

end GoldbachBoundaries.Paper2.M1
