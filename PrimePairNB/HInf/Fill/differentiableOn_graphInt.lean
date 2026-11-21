import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.graphInt_line

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- The measurable-height version of the vertical-integral argument: Cauchy's
estimate supplies an integrable bound for the parameter derivative. -/
private theorem differentiableOn_height_integral {U : Set ℂ} (hU : IsOpen U)
    {G : ℂ → ℝ → ℂ}
    (hmeas : ∀ x ∈ U, AEStronglyMeasurable (G x) volume)
    (hhol : ∀ y : ℝ, DifferentiableOn ℂ (fun s => G s y) U)
    (hdom : ∀ K ⊆ U, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ s ∈ K, ∀ y : ℝ, ‖G s y‖ ≤ g y) :
    DifferentiableOn ℂ (fun s => ∫ y : ℝ, G s y) U := by
  intro s₀ hs₀
  obtain ⟨R₀, hR₀, hR₀U⟩ := Metric.isOpen_iff.mp hU s₀ hs₀
  set R : ℝ := R₀ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hcbU : closedBall s₀ R ⊆ U :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hR₀U
  obtain ⟨g, hg, hgb⟩ := hdom (closedBall s₀ R) hcbU (isCompact_closedBall s₀ R)
  -- the derivative and its bound
  set F' : ℂ → ℝ → ℂ := fun x y => deriv (fun s => G s y) x with hF'def
  have hderiv : ∀ y : ℝ, ∀ x ∈ U, HasDerivAt (fun s => G s y) (F' x y) x := by
    intro y x hx
    exact ((hhol y).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hbound : ∀ y : ℝ, ∀ x ∈ ball s₀ (R / 2), ‖F' x y‖ ≤ g y / (R / 2) := by
    intro y x hx
    have hsub : closedBall x (R / 2) ⊆ closedBall s₀ R := by
      apply closedBall_subset_closedBall'
      have := mem_ball.mp hx
      linarith [dist_comm x s₀]
    have hdc : DiffContOnCl ℂ (fun s => G s y) (ball x (R / 2)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball x (by positivity)]
      exact (hhol y).mono (hsub.trans hcbU)
    apply norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdc
    intro z hz
    exact hgb z (hsub (sphere_subset_closedBall hz)) y
  -- measurability of `F' s₀` as a limit of difference quotients
  have hF'meas : AEStronglyMeasurable (F' s₀) volume := by
    set h : ℕ → ℂ := fun n => ((R / (n + 2) : ℝ) : ℂ) with hhdef
    have hhmem : ∀ n, s₀ + h n ∈ U := by
      intro n
      apply hcbU
      rw [mem_closedBall, dist_eq, add_sub_cancel_left, hhdef, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hh : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have : Tendsto (fun n : ℕ => R / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        have := (continuous_ofReal.tendsto 0).comp this
        simpa [hhdef, Function.comp_def] using this
      · simp only [hhdef, mem_compl_iff, mem_singleton_iff, ofReal_eq_zero]
        positivity
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n y => (h n)⁻¹ • (G (s₀ + h n) y - G s₀ y)) (fun n => ?_) ?_
    · exact ((hmeas _ (hhmem n)).sub (hmeas _ hs₀)).const_smul (h n)⁻¹
    · exact Eventually.of_forall fun y =>
        ((hderiv y s₀ hs₀).tendsto_slope_zero).comp hh
  have hball : ball s₀ (R / 2) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hcbU
  have hint : Integrable (G s₀) :=
    hg.mono' (hmeas s₀ hs₀) (Eventually.of_forall fun y =>
      hgb s₀ (mem_closedBall_self hR.le) y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := G) (F' := F') (x₀ := s₀) (bound := fun y => g y / (R / 2))
    (ball_mem_nhds s₀ (by positivity))
    (Filter.eventually_of_mem (hU.mem_nhds hs₀) fun x hx => hmeas x hx)
    hint hF'meas
    (Eventually.of_forall fun y x hx => hbound y x hx)
    (hg.div_const _)
    (Eventually.of_forall fun y x hx => hderiv y x (hball hx))
  exact key.2.differentiableAt.differentiableWithinAt

/-- The velocity is measurable even at corners, where `deriv` uses its default value. -/
theorem graph_velocity_measurable {κ : ℝ} (Γ : SlantGraph κ) :
    AEStronglyMeasurable (fun h => slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I)) volume := by
  exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable
    (aestronglyMeasurable_deriv Γ.ξ volume)).add_const I).const_mul _

/-- **Holomorphy under the integral**, on one fixed graph (the analogue of `Paper2.M1.differentiableOn_verticalIntegral'`). -/
theorem differentiableOn_graphInt {κ : ℝ} (Γ : SlantGraph κ) {W : Set ℂ} (hW : IsOpen W) {F : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => F p.1 (Γ.pt p.2)) (W ×ˢ univ))
    (hhol : ∀ h : ℝ, DifferentiableOn ℂ (fun v => F v (Γ.pt h)) W)
    (hdom : ∀ K ⊆ W, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧ ∀ v ∈ K, ∀ h : ℝ, ‖F v (Γ.pt h)‖ ≤ g h) :
    DifferentiableOn ℂ (fun v => graphInt Γ (F v)) W := by
  obtain ⟨L, hL⟩ := Γ.lip
  let C : ℝ := ‖slantDir κ‖ * (max L 0 + 1)
  have hC : 0 ≤ C := by positivity
  classical
  let V : ℝ → ℂ := fun h => if h ∈ Γ.brk then 0 else
    slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I)
  have hb (h : ℝ) : ‖V h‖ ≤ C := by
    dsimp [V]
    split_ifs with hh
    · simpa using hC
    · calc
        _ = ‖slantDir κ‖ * ‖((deriv Γ.ξ h : ℝ) : ℂ) + I‖ := norm_mul _ _
        _ ≤ ‖slantDir κ‖ * (|deriv Γ.ξ h| + 1) := by
          gcongr
          simpa using norm_add_le ((deriv Γ.ξ h : ℝ) : ℂ) I
        _ ≤ C := by
          dsimp [C]
          gcongr
          exact (hL h hh).trans (le_max_left _ _)
  have hvmeas : AEStronglyMeasurable V volume := by
    exact aestronglyMeasurable_const.piecewise Γ.brk.finite_toSet.measurableSet
      (graph_velocity_measurable Γ).restrict
  have hmain : DifferentiableOn ℂ
      (fun v => ∫ h : ℝ, F v (Γ.pt h) * V h) W := by
    apply differentiableOn_height_integral hW
    · intro v hv
      have hs : Continuous (fun h : ℝ => F v (Γ.pt h)) :=
        continuousOn_univ.mp (hcont.comp (Continuous.prodMk_right v).continuousOn
          (fun _ _ => ⟨hv, trivial⟩))
      exact hs.aestronglyMeasurable.mul hvmeas
    · intro h
      exact (hhol h).mul_const _
    · intro K hKW hK
      obtain ⟨g, hg, hgb⟩ := hdom K hKW hK
      refine ⟨fun h => C * |g h|, hg.abs.const_mul C, ?_⟩
      intro v hv h
      dsimp only
      rw [norm_mul, mul_comm C]
      exact mul_le_mul ((hgb v hv h).trans (le_abs_self _)) (hb h)
        (norm_nonneg _) (abs_nonneg _)
  have heq : (fun v => graphInt Γ (F v)) =
      fun v => (1 / (2 * (Real.pi : ℂ) * I)) * ∫ h : ℝ, F v (Γ.pt h) * V h := by
    funext v
    unfold graphInt
    congr 1
    apply integral_congr_ae
    filter_upwards [(show ∀ᵐ h : ℝ, h ∉ Γ.brk from ae_iff.mpr (by simpa using Γ.brk.finite_toSet.measure_zero volume))] with h hh
    simp [V, hh]
  rw [heq]
  exact hmain.const_mul _

end GoldbachBoundaries.HInf.Fill

