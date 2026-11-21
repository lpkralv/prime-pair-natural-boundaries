import PrimePairNB.HInf.Fill.outer_contour_bounds
import PrimePairNB.HInf.Fill.outer_contour_holomorphy
import PrimePairNB.HInf.Fill.outer_contour_near
import PrimePairNB.HInf.Fill.hasDerivAt_Pth

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma outer_velocity_bound {κ : ℝ} (Γ : SlantGraph κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h, ‖slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I)‖ ≤ C := by
  classical
  obtain ⟨L, hL⟩ := Γ.lip
  let B := max L 0 + ∑ a ∈ Γ.brk, |deriv Γ.ξ a|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd : ∀ h, |deriv Γ.ξ h| ≤ B := by
    intro h
    by_cases hh : h ∈ Γ.brk
    · have hs := Finset.single_le_sum (f := fun a => |deriv Γ.ξ a|)
        (fun _ _ => abs_nonneg _) hh
      dsimp [B]; linarith [le_max_right L 0]
    · exact (hL h hh).trans (by dsimp [B]; exact le_add_of_le_of_nonneg (le_max_left _ _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  refine ⟨‖slantDir κ‖ * (B + 1), by positivity, fun h => ?_⟩
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_add_le _ _).trans (by simpa using add_le_add_right (hd h) 1)

/-- Holomorphy and domination on the closed exterior of the collision bands. -/
theorem outer_contour_integral (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D)
    {κ : ℝ} {x : ℂ} {q r e η : ℝ} (he : 0 < e) (hη : 0 < η)
    (Γ : SlantGraph κ) (hV : ball x r ⊆ Vt top)
    (hs : ∀ v ∈ ball x r, ∀ h, e ≤ (Γ.pt h).re ∧ (Γ.pt h).re ≤ v.re - e)
    (hc : ∀ v ∈ ball x r, Binf + 2 * η ≤ Γ.c ∧ Binf + 2 * η ≤ v.re - Γ.c)
    (hU : ∀ v ∈ ball x r, ∀ h ∈ outerHeights κ x q,
      Γ.pt h ∈ Uth κ ∧ v - Γ.pt h ∈ Uth κ) :
    DifferentiableOn ℂ (fun v => ∫ h in outerHeights κ x q,
      pairIntegrand k κ v (Γ.pt h) * (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))) (ball x r) := by
  let E := outerHeights κ x q
  have hE : IsClosed E := outer_heights_closed κ x q
  have hpt := outer_pt_continuous Γ
  have hcont : ∀ v ∈ ball x r, ContinuousOn (fun h => pairIntegrand k κ v (Γ.pt h)) E := by
    intro v hv
    unfold pairIntegrand
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · refine hK.holo.continuousOn.comp (hpt.prodMk continuous_const).continuousOn ?_
      intro h hh
      exact ⟨hV hv, by linarith [(hs v hv h).1], by linarith [(hs v hv h).2]⟩
    · exact (outer_Pth_continuousOn κ).comp hpt.continuousOn (fun h hh => (hU v hv h hh).1)
    · exact (outer_Pth_continuousOn κ).comp (continuous_const.sub hpt).continuousOn
        (fun h hh => (hU v hv h hh).2)
  apply outer_contour_holomorphy Γ
  · intro v hv
    exact ((hcont v hv).aestronglyMeasurable hE.measurableSet).mul
      (graph_velocity_measurable Γ).restrict
  · intro h hh
    unfold pairIntegrand
    refine DifferentiableOn.mul (DifferentiableOn.mul ?_ (differentiableOn_const _)) ?_
    · refine hK.holo.comp (f := fun v : ℂ => (Γ.pt h, v)) (by fun_prop) ?_
      intro v hv
      exact ⟨hV hv, by linarith [(hs v hv h).1], by linarith [(hs v hv h).2]⟩
    · refine (show DifferentiableOn ℂ (Pth κ) (Uth κ) from
        fun z hz => (Fill.hasDerivAt_Pth hz).differentiableAt.differentiableWithinAt).comp
        (f := fun v : ℂ => v - Γ.pt h) (by fun_prop) ?_
      intro v hv; exact (hU v hv h hh).2
  · intro K hKW hKc
    have hself : ∀ l h, interpPt Γ Γ l h = Γ.pt h := by
      intro l h; unfold interpPt SlantGraph.pt; congr 3; ring
    obtain ⟨M, hM⟩ := outer_contour_norm_uniform hZ1 hZ2 hZ3 hK hKc
      (fun v hv => hV (hKW hv)) hE (Γ₀ := Γ) (Γ₁ := Γ) he hη
      (by intro v hv l hl h hh; rw [hself]; exact hs v (hKW hv) h)
      (by intro v hv l hl h hh; rw [hself]; exact hU v (hKW hv) h hh)
      (by intro v hv; have h := hc v (hKW hv); exact ⟨h.1, h.1, h.2, h.2⟩)
    obtain ⟨C, hC, hb⟩ := outer_velocity_bound Γ
    refine ⟨fun h => (|M| * C) * (1 + |h|) ^ (-(3 / 2) : ℝ), ?_, ?_⟩
    · refine Integrable.const_mul ?_ _
      simpa only [Real.norm_eq_abs] using
        (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num))
    · intro v hv h hh
      have hm := hM v hv 0 (by simp) h hh
      rw [hself] at hm
      have hm' : ‖pairIntegrand k κ v (Γ.pt h)‖ ≤ |M| * (1 + |h|) ^ (-(3 / 2) : ℝ) :=
        hm.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      rw [norm_mul]
      calc
        _ ≤ (|M| * (1 + |h|) ^ (-(3 / 2) : ℝ)) * C :=
          mul_le_mul hm' (hb h) (norm_nonneg _) (by positivity)
        _ = _ := by ring
end GoldbachBoundaries.HInf.Fill
