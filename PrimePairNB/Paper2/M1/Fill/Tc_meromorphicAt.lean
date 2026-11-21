import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.Ic_differentiableOn
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.isOpen_RegC
import PrimePairNB.Paper2.M1.Fill.meromorphicOrderAt_Qcont_ge

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `𝒯_c` is meromorphic with order `≥ -1` at every point of its region (Z1, Z2, Z3): as in `Tc_analyticAt`, each
`Q(s - a)` has order `≥ -1` (`meromorphicOrderAt_Qcont_ge`). Uses: `Ic_differentiableOn`, `isOpen_RegC`,
`meromorphicOrderAt_Qcont_ge`, `meromorphicAt_Qcont`. -/
theorem Tc_meromorphicAt (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c : ℝ} (h : AdmC δ c) {s₀ : ℂ}
    (hs₀ : s₀ ∈ RegC δ c) : MeromorphicAt (Tc δ c) s₀ ∧ -1 ≤ meromorphicOrderAt (Tc δ c) s₀ := by
  classical
  have hF := (Fdelta_spec hZ1 δ h.1).1
  have hI : AnalyticAt ℂ (IcQ Qcont c) s₀ :=
    (Ic_differentiableOn hZ1 hZ2 hZ3 h).analyticAt ((isOpen_RegC hZ1 h).mem_nhds hs₀)
  let f : ℂ → ℂ → ℂ := fun a s => nu c a s₀ * Rcoef a * KerS s a * Qcont (s - a)
  have hterms : ∀ a ∈ hF.toFinset, MeromorphicAt (f a) s₀ ∧
      -1 ≤ meromorphicOrderAt (f a) s₀ := by
    intro a ha
    have hap := (hF.mem_toFinset.mp ha).1
    have hka : a.re < s₀.re := halfPlane_two_Binf_subset hZ1 hap (E2_reg_re h hs₀)
    have hsa : 0 < (s₀ - a).re := by simp only [sub_re]; linarith
    have hA : AnalyticAt ℂ (fun s => nu c a s₀ * Rcoef a * KerS s a) s₀ :=
      analyticAt_const.fun_mul (E2_analytic_KerS hka)
    have hB : MeromorphicAt (fun s => Qcont (s - a)) s₀ :=
      (meromorphicAt_Qcont hsa).comp_analyticAt (g := fun z : ℂ => z - a) (analyticAt_id.sub analyticAt_const)
    have hbo : -1 ≤ meromorphicOrderAt (fun s => Qcont (s - a)) s₀ := by
      rw [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
      exact meromorphicOrderAt_Qcont_ge hsa
    exact ⟨hA.meromorphicAt.mul hB, E2_order_mul hA hB hbo⟩
  have hsum := E2_sum_simple hF.toFinset f s₀ (fun a ha => (hterms a ha).1)
    (fun a ha => (hterms a ha).2)
  have hmer := hI.meromorphicAt.fun_add hsum.1
  have hord : -1 ≤ meromorphicOrderAt (fun s => IcQ Qcont c s + ∑ a ∈ hF.toFinset, f a s) s₀ :=
    (le_min (le_trans (show (-1 : WithTop ℤ) ≤ 0 from by decide) hI.meromorphicOrderAt_nonneg) hsum.2).trans
      (meromorphicOrderAt_add hI.meromorphicAt hsum.1)
  have he : Tc δ c =ᶠ[𝓝[≠] s₀] (fun s => IcQ Qcont c s +
      ∑ a ∈ hF.toFinset, nu c a s₀ * Rcoef a * KerS s a * Qcont (s - a)) :=
    (E2_Tc_eventuallyEq hF hs₀).filter_mono nhdsWithin_le_nhds
  exact ⟨hmer.congr he.symm, by rw [meromorphicOrderAt_congr he]; exact hord⟩

end GoldbachBoundaries.Paper2.M1
