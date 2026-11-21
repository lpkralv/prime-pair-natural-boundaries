import PrimePairNB.HInf.Fill.arc_model_pinch_derivative
import PrimePairNB.HInf.Fill.arc_model_residue
import PrimePairNB.HInf.Fill.exists_arc
import Mathlib.Analysis.Normed.Module.Convex

/-! Arc independence and the two-parameter pinch family. Horizontal connectors
have local primitives on convex neighborhoods; their endpoint values vanish. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

/-- A compact segment in a holomorphic domain has a convex neighborhood with a primitive. -/
lemma arc_model_segment_primitive {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {a b : ℂ} (hab : segment ℝ a b ⊆ U) :
    ∃ V : Set ℂ, IsOpen V ∧ Convex ℝ V ∧ segment ℝ a b ⊆ V ∧ V ⊆ U ∧
      ∃ Φ : ℂ → ℂ, ∀ z ∈ V, HasDerivAt Φ (F z) z := by
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_thickening_subset_open hU hab
  let V := thickening δ (segment ℝ a b)
  have hV : IsOpen V := isOpen_thickening
  have hcV : Convex ℝ V := (convex_segment a b).thickening δ
  have hsV : segment ℝ a b ⊆ V := self_subset_thickening hδ _
  refine ⟨V, hV, hcV, hsV, hδU, fun z => ThmA.segInt F a z, ?_⟩
  exact fun z hz => ThmA.GroupC.hasDerivAt_segInt hV hcV (hF.mono hδU)
    (hsV (left_mem_segment ℝ a b)) hz

/-- Integrals over two arcs agree whenever the horizontal segments between them stay holomorphic. -/
theorem arc_model_arc_independent {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℂ}
    {ξ₀ ξ₁ : ℝ → ℝ} (h₀ : IsArc r₀ ε ξ₀) (h₁ : IsArc r₀ ε ξ₁)
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hm : ∀ h ∈ Icc (-r₀) r₀, segment ℝ (arcPt ξ₀ h) (arcPt ξ₁ h) ⊆ U) :
    arcInt r₀ ξ₀ F = arcInt r₀ ξ₁ F := by
  let C : ℝ → ℂ := fun h => ThmA.segInt F (arcPt ξ₀ h) (arcPt ξ₁ h)
  have hc₀ := arcPt_continuousOn h₀
  have hc₁ := arcPt_continuousOn h₁
  have hlocal (h : ℝ) (hh : h ∈ Icc (-r₀) r₀) :
      ∃ Φ : ℂ → ℂ, (∀ᶠ x in 𝓝[Icc (-r₀) r₀] h,
        C x = Φ (arcPt ξ₁ x) - Φ (arcPt ξ₀ x)) ∧
        HasDerivAt Φ (F (arcPt ξ₀ h)) (arcPt ξ₀ h) ∧
        HasDerivAt Φ (F (arcPt ξ₁ h)) (arcPt ξ₁ h) := by
    obtain ⟨V, hV, hcV, hsV, hVU, Φ, hΦ⟩ := arc_model_segment_primitive hU hF (hm h hh)
    have ha := hsV (left_mem_segment ℝ (arcPt ξ₀ h) (arcPt ξ₁ h))
    have hb := hsV (right_mem_segment ℝ (arcPt ξ₀ h) (arcPt ξ₁ h))
    refine ⟨Φ, ?_, hΦ _ ha, hΦ _ hb⟩
    filter_upwards [(hc₀ h hh).eventually (hV.mem_nhds ha),
      (hc₁ h hh).eventually (hV.mem_nhds hb)] with x hx₀ hx₁
    exact segInt_eq_primitive (hF.continuousOn.mono hVU) hΦ (hcV.segment_subset hx₀ hx₁)
  have hc : ContinuousOn C (Icc (-r₀) r₀) := by
    intro h hh
    obtain ⟨Φ, he, hd₀, hd₁⟩ := hlocal h hh
    exact ((hd₁.continuousAt.comp_continuousWithinAt (hc₁ h hh)).sub
      (hd₀.continuousAt.comp_continuousWithinAt (hc₀ h hh))).congr_of_eventuallyEq he
        (he.self_of_nhdsWithin hh)
  obtain ⟨S₀, hS₀⟩ := h₀.brk
  obtain ⟨S₁, hS₁⟩ := h₁.brk
  have hd : ∀ h ∈ Ioo (-r₀) r₀, h ∉ S₀ ∪ S₁ →
      HasDerivAt C (F (arcPt ξ₁ h) * (((deriv ξ₁ h : ℝ) : ℂ) + I) -
        F (arcPt ξ₀ h) * (((deriv ξ₀ h : ℝ) : ℂ) + I)) h := by
    intro h hh hn
    have hn' : h ∉ S₀ ∧ h ∉ S₁ := by simpa using hn
    obtain ⟨Φ, he, hd₀, hd₁⟩ := hlocal h (Ioo_subset_Icc_self hh)
    have hp₀ : HasDerivAt (arcPt ξ₀) (((deriv ξ₀ h : ℝ) : ℂ) + I) h := by
      convert! ((hS₀ h hh hn'.1).hasDerivAt.ofReal_comp).fun_add
        ((hasDerivAt_id h).ofReal_comp.mul_const I) using 1 <;> simp [arcPt]
    have hp₁ : HasDerivAt (arcPt ξ₁) (((deriv ξ₁ h : ℝ) : ℂ) + I) h := by
      convert! ((hS₁ h hh hn'.2).hasDerivAt.ofReal_comp).fun_add
        ((hasDerivAt_id h).ofReal_comp.mul_const I) using 1 <;> simp [arcPt]
    apply ((hd₁.comp h hp₁).sub (hd₀.comp h hp₀)).congr_of_eventuallyEq
    rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hh.1 hh.2)] at he
    filter_upwards [he] with x hx
    exact hx
  have hi₀ := arc_integrable hr₀ h₀ (hF.continuousOn.comp hc₀
    (fun h hh => hm h hh (left_mem_segment ℝ _ _)))
  have hi₁ := arc_integrable hr₀ h₁ (hF.continuousOn.comp hc₁
    (fun h hh => hm h hh (right_mem_segment ℝ _ _)))
  have he := integral_eq_of_hasDerivAt_off_countable C _ (Finset.finite_toSet (S₀ ∪ S₁)).countable
    (by simpa [uIcc_of_le (show -r₀ ≤ r₀ by linarith)] using hc)
    (fun h hh => hd h (by
      have hab : -r₀ ≤ r₀ := by linarith
      simpa only [min_eq_left hab, max_eq_right hab] using hh.1) hh.2)
    (hi₁.sub hi₀)
  have hz : C r₀ - C (-r₀) = 0 := by simp [C, arcPt, h₀.ends.1, h₀.ends.2, h₁.ends.1, h₁.ends.2, ThmA.segInt]
  rw [intervalIntegral.integral_sub hi₁ hi₀, hz, sub_eq_zero] at he
  exact congrArg (fun z : ℂ => (1 / (2 * (Real.pi : ℂ) * I)) * z) he.symm

end GoldbachBoundaries.HInf.Fill
