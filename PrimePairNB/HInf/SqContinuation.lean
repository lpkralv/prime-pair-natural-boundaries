import PrimePairNB.HInf.SqKernel
import PrimePairNB.HInf.SqNonvacuity
import PrimePairNB.HInf.Fill.boundary_G

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma Dth_eq_Sq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (κ : ℝ)
    {v : ℂ} (hv : 2 < v.re) : Dth kSq κ v = DSq v := by
  have hK := isPinchKernel_Sq_top hZ6
  have hD : AnalyticOnNhd ℂ (Dth kSq κ) (halfPlane 2) :=
    (Dth_analyticOn hZ1 hZ2 hZ3 hK κ).mono (fun z hz =>
      mem_Om_of_two_lt hZ1 ⟨by linarith [show 2 < z.re from hz], EReal.coe_lt_top _⟩ hz)
  have hS : AnalyticOnNhd ℂ DSq (halfPlane 2) := fun _ hz => DSq_analyticAt hz
  have he : Dth kSq κ =ᶠ[𝓝 (5 / 2 : ℂ)] DSq := by
    have hstrip : {z : ℂ | 2 < z.re ∧ z.re < 3} ∈ 𝓝 (5 / 2 : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by norm_num)
    filter_upwards [hstrip] with z hz
    exact Dth_eq hZ1 hZ2 hZ3 hK κ hz.1 hz.2
  exact hD.eqOn_of_preconnected_of_eventuallyEq hS
    (convex_halfSpace_re_gt (2 : ℝ)).isPreconnected (by norm_num [halfPlane]) he hv

/-- Admissibility in the pinch coordinate, with the unbounded continuation domain. -/
def AdmSqV (g : ℂ → ℂ) (v : ℂ) : Prop :=
  IsAdmissibleGermOn DSq (HH \ catG) (halfPlane 2) g v

lemma germFam_of_admissible_Sq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    {g : ℂ → ℂ} {q : ℂ}
    (hg : IsAdmissibleGermOn DSq (VInf ⊤ \ Pinch) (halfPlane 2) g q) :
    GermFam kSq ⊤ 0 q g := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := hg
  have hstart : GermFam kSq ⊤ 0 (γ 0) DSq := by
    have h2 : 2 < (γ 0).re := h0
    refine ⟨0, mem_Om_of_two_lt hZ1 ⟨by linarith, EReal.coe_lt_top _⟩ h2, 0, zero_mem _, ?_⟩
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2] with v hv
    simp [Dth_eq_Sq hZ1 hZ2 hZ3 hZ6 0 hv]
  exact germFam_congr (ThmA.continuationAlong_preserve
    (uniformFamily_germFam hZ1 hZ2 hZ3 (isPinchKernel_Sq_top hZ6) 0)
    (fun _ _ _ h hfg => germFam_congr h hfg) hγ hf
    (germFam_congr hstart hf0.symm) 1) hg1.symm

lemma eventuallyEq_comp_sq_half {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) :
    (fun v => f (v / 2)) =ᶠ[𝓝 (2 * s)] fun v => g (v / 2) := by
  have hc : ContinuousAt (fun v : ℂ => v / 2) (2 * s) := by fun_prop
  have ht : Tendsto (fun v : ℂ => v / 2) (𝓝 (2 * s)) (𝓝 s) := by
    simpa only [show 2 * s / 2 = s by ring] using hc.tendsto
  exact ht.eventually h

lemma analyticAt_comp_sq_half {f : ℂ → ℂ} {s : ℂ} (h : AnalyticAt ℂ f s) :
    AnalyticAt ℂ (fun v => f (v / 2)) (2 * s) := by
  have h' : AnalyticAt ℂ f (2 * s / 2) := by rwa [show 2 * s / 2 = s by ring]
  exact AnalyticAt.comp (g := f) (f := fun v : ℂ => v / 2) h' (by fun_prop)

lemma admSq_transfer {g : ℂ → ℂ} {s₁ : ℂ} (hg : AdmSq g s₁) :
    AdmSqV (fun v => g (v / 2)) (2 * s₁) := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := hg
  let γ' : C(unitInterval, ℂ) := ⟨fun t => 2 * γ t, by fun_prop⟩
  refine ⟨γ', fun t => ?_, ?_, rfl, fun t v => f t (v / 2),
    ⟨fun t => analyticAt_comp_sq_half (hf.analyticAt t), fun t => ?_⟩,
    eventuallyEq_comp_sq_half hf0, eventuallyEq_comp_sq_half hg1⟩
  · have ht := hγ t
    have ht0 : 1 / 2 < (γ t).re := by simpa only [twoL_HL, halfPlane, mem_ofPred_eq] using ht.1
    have h2 : 1 < (2 * γ t).re := by simp; linarith
    exact ⟨h2, fun hc => ht.2 (mem_catSq_iff.mpr ⟨ht0, (mem_catG_iff.mp hc).2⟩)⟩
  · have ht : 1 < (γ 0).re := by simpa only [twoL_RL, halfPlane, mem_ofPred_eq] using h0
    show 2 < (2 * γ 0).re
    simp; linarith
  · filter_upwards [hf.locallyEq t] with t' ht'
    exact eventuallyEq_comp_sq_half ht'

lemma dist_sq_half (v x : ℂ) : dist (v / 2) (x / 2) = dist v x / 2 := by
  rw [dist_eq_norm, dist_eq_norm, show v / 2 - x / 2 = (v - x) / 2 by ring, norm_div]
  norm_num

end GoldbachBoundaries.HInf.Fill
