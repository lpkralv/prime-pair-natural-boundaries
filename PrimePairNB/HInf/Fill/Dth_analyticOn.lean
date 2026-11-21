import PrimePairNB.HInf.Fill.graphInt_eq_of_separating
import PrimePairNB.HInf.Fill.differentiableOn_graphInt
import PrimePairNB.HInf.Fill.exists_separating_iff
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.interpPt_mem_of_separating
import PrimePairNB.HInf.Fill.isSeparating_eventually

/-!
# `Dth_analyticOn`

Near `v₁` a fixed graph separates, so `D^θ` is one integral over one contour; the integrand is holomorphic in `v` and
dominated by `sheet_norm_uniform`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

theorem sheet_interpPt_self {κ : ℝ} (Γ : SlantGraph κ) (l h : ℝ) : interpPt Γ Γ l h = Γ.pt h := by
  unfold interpPt SlantGraph.pt
  congr 3
  ring

theorem sheet_pt_continuous {κ : ℝ} (Γ : SlantGraph κ) : Continuous Γ.pt := by
  have h := (sheet_interp_continuous Γ Γ).comp (continuous_const.prodMk continuous_id : Continuous fun h : ℝ => ((0 : ℝ), h))
  refine h.congr fun h => ?_
  exact sheet_interpPt_self Γ 0 h

/-- `D^θ` is holomorphic on `Ω_θ`. -/
theorem Dth_analyticOn (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (κ : ℝ) : AnalyticOnNhd ℂ (Dth k κ) (Om κ top) := by
  have hOpen := isOpen_Om hZ1 κ top
  refine DifferentiableOn.analyticOnNhd (fun v₁ hv₁ => ?_) hOpen
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨Γ, hΓ⟩ := (exists_separating_iff hZ1 hv₁.1).mpr hv₁
  obtain ⟨ε₁, hε₁, hre₁⟩ := hΓ.re_mem
  have htail := hΓ.tail_c
  set δ : ℝ := min (Γ.c - Binf) (v₁.re - Binf - Γ.c) with hδdef
  have hδ : 0 < δ := lt_min (by linarith [htail.1]) (by linarith [htail.2])
  have hδ₁ : δ ≤ Γ.c - Binf := min_le_left _ _
  have hδ₂ : δ ≤ v₁.re - Binf - Γ.c := min_le_right _ _
  have hev : ∀ᶠ v in 𝓝 v₁, IsSeparating v Γ ∧ v ∈ Om κ top :=
    (isSeparating_eventually hZ1 hΓ).and (hOpen.mem_nhds hv₁)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set r : ℝ := min (r₀ / 2) (min (ε₁ / 2) (δ / 2)) with hrdef
  have hr : 0 < r := by
    refine lt_min (half_pos hr₀) (lt_min (half_pos hε₁) (half_pos hδ))
  have hrr₀ : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₀)
  have hrε : r ≤ ε₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set K₀ : Set ℂ := closedBall v₁ r with hK₀
  have hK₀sub : ∀ v ∈ K₀, IsSeparating v Γ ∧ v ∈ Om κ top := fun v hv =>
    hball v (closedBall_subset_ball hrr₀ hv)
  have hrenear : ∀ v ∈ K₀, v₁.re - r ≤ v.re := fun v hv => by
    have h1 : ‖v - v₁‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hv
    have h2 := (Complex.abs_re_le_norm (v - v₁)).trans h1
    have h3 := (abs_le.mp h2).1
    simp only [Complex.sub_re] at h3
    linarith
  have hmemK : ∀ v ∈ K₀, ∀ h : ℝ, Γ.pt h ∈ Uth κ ∧ v - Γ.pt h ∈ Uth κ := fun v hv h => by
    obtain ⟨_, _, hm⟩ := interpPt_mem_of_separating (hK₀sub v hv).1 (hK₀sub v hv).1
    have := hm 0 (by simp) h
    rw [sheet_interpPt_self] at this
    exact ⟨this.1, this.2.1⟩
  obtain ⟨M, hM⟩ := sheet_norm_uniform hZ1 hZ2 hZ3 hK (K := K₀) (isCompact_closedBall _ _)
    (fun v hv => (hK₀sub v hv).2.1.1) (Γ₀ := Γ) (Γ₁ := Γ) (half_pos hε₁) (half_pos (half_pos hδ))
    (by
      intro v hv l _ h
      rw [sheet_interpPt_self]
      have a := hre₁ h
      have b := hrenear v hv
      exact ⟨by linarith [a.1], by linarith [a.2]⟩)
    (by
      intro v hv l _ h
      rw [sheet_interpPt_self]
      exact hmemK v hv h)
    (by
      intro v hv
      have b := hrenear v hv
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
  have hWsub : ball v₁ r ⊆ K₀ := ball_subset_closedBall
  have hintg : Integrable (fun h : ℝ => M * (1 + |h|) ^ (-(3 / 2) : ℝ)) := by
    refine Integrable.const_mul ?_ M
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num))
  have hdiff : DifferentiableOn ℂ (fun v => graphInt Γ (pairIntegrand k κ v)) (ball v₁ r) := by
    refine differentiableOn_graphInt Γ isOpen_ball (F := fun v => pairIntegrand k κ v) ?_ ?_ ?_
    · unfold pairIntegrand
      have hptc : Continuous (fun p : ℂ × ℝ => Γ.pt p.2) := (sheet_pt_continuous Γ).comp continuous_snd
      refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
      · refine hK.holo.continuousOn.comp (f := fun p : ℂ × ℝ => (Γ.pt p.2, p.1))
          (hptc.prodMk continuous_fst).continuousOn ?_
        rintro ⟨v, h⟩ ⟨hv, -⟩
        have hvK := hWsub hv
        obtain ⟨ε, hε, hm⟩ := (hK₀sub v hvK).1.re_mem
        have hm' := hm h
        obtain ⟨hU₁, _⟩ := hmemK v hvK h
        refine ⟨(hK₀sub v hvK).2.1.1, hU₁.1, ?_⟩
        show (Γ.pt h).re < v.re
        linarith [hm'.2]
      · refine (sheet_Pth_continuousOn κ).comp hptc.continuousOn ?_
        rintro ⟨v, h⟩ ⟨hv, -⟩
        exact (hmemK v (hWsub hv) h).1
      · refine (sheet_Pth_continuousOn κ).comp (continuous_fst.sub hptc).continuousOn ?_
        rintro ⟨v, h⟩ ⟨hv, -⟩
        exact (hmemK v (hWsub hv) h).2
    · intro h
      unfold pairIntegrand
      refine DifferentiableOn.mul (DifferentiableOn.mul ?_ (differentiableOn_const _)) ?_
      · refine hK.holo.comp (f := fun v : ℂ => (Γ.pt h, v)) (by fun_prop) ?_
        intro v hv
        have hvK := hWsub hv
        obtain ⟨ε, hε, hm⟩ := (hK₀sub v hvK).1.re_mem
        have hm' := hm h
        refine ⟨(hK₀sub v hvK).2.1.1, (hmemK v hvK h).1.1, ?_⟩
        show (Γ.pt h).re < v.re
        linarith [hm'.2]
      · refine (sheet_Pth_differentiableOn κ).comp (f := fun v : ℂ => v - Γ.pt h) (by fun_prop) ?_
        intro v hv
        exact (hmemK v (hWsub hv) h).2
    · intro K hKW _
      refine ⟨fun h => M * (1 + |h|) ^ (-(3 / 2) : ℝ), hintg, ?_⟩
      intro v hv h
      have := hM v (hWsub (hKW hv)) 0 (by simp) h
      rwa [sheet_interpPt_self] at this
  refine ((hdiff v₁ (mem_ball_self hr)).differentiableAt (ball_mem_nhds v₁ hr)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds v₁ hr] with v hv
  have hs := hK₀sub v (hWsub hv)
  exact Dth_eq_graphInt hZ1 hZ2 hZ3 hK hs.2.1 hs.1

end GoldbachBoundaries.HInf.Fill

