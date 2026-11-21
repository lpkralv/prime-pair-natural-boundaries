import PrimePairNB.Paper2.M1.Kernel

/-!
# `differentiableOn_verticalIntegral'`

Differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), following the interval
version `ThmA/Fill/differentiableOn_intervalIntegral_of_continuousOn.lean`. Fix `s₀ ∈ U` and a closed disc
`closedBall s₀ R ⊆ U`; on it `‖F s (c + iy)‖ ≤ g(y)` with `g` integrable (`hdom`). Cauchy's estimate on circles of
radius `R/2` bounds `‖∂ₛ F(s, c + iy)‖ ≤ g(y)/(R/2)` for `s ∈ ball s₀ (R/2)`; the derivative is ae-strongly
measurable in `y` as a pointwise limit of difference quotients, each continuous in `y`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Holomorphy of a vertical integral in a parameter.** If `U` is open, `F s w` is jointly continuous on
`U × {Re w = c}` and holomorphic in `s ∈ U` for each point of the line, and on every compact `K ⊆ U` it is dominated on
the line by an integrable function of `Im w`, then `s ↦ (2πi)⁻¹ ∫_{(c)} F s w dw` is holomorphic on `U` (dominated
convergence and Morera, or Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with Cauchy estimates for
the derivative). -/
theorem differentiableOn_verticalIntegral' {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ → ℂ} {c : ℝ}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => F p.1 (c + p.2 * I)) (U ×ˢ univ))
    (hhol : ∀ y : ℝ, DifferentiableOn ℂ (fun s => F s (c + y * I)) U)
    (hdom : ∀ K ⊆ U, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ s ∈ K, ∀ y : ℝ, ‖F s (c + y * I)‖ ≤ g y) :
    DifferentiableOn ℂ (fun s => VerticalIntegral' (F s) c) U := by
  set G : ℂ → ℝ → ℂ := fun s y => F s (c + y * I) with hGdef
  -- the integral as a function of `s`
  have hmain : DifferentiableOn ℂ (fun s => ∫ y : ℝ, G s y) U := by
    intro s₀ hs₀
    obtain ⟨R₀, hR₀, hR₀U⟩ := Metric.isOpen_iff.mp hU s₀ hs₀
    set R : ℝ := R₀ / 2 with hRdef
    have hR : 0 < R := by positivity
    have hcbU : closedBall s₀ R ⊆ U :=
      (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hR₀U
    obtain ⟨g, hg, hgb⟩ := hdom (closedBall s₀ R) hcbU (isCompact_closedBall s₀ R)
    -- continuity of each slice
    have hslice : ∀ x ∈ U, Continuous (G x) := by
      intro x hx
      have : ContinuousOn (fun y : ℝ => F (x, y).1 (c + (x, y).2 * I)) univ :=
        hcont.comp (Continuous.prodMk_right x).continuousOn (fun y _ => ⟨hx, trivial⟩)
      exact continuousOn_univ.mp (by simpa using this)
    have hmeas : ∀ x ∈ U, AEStronglyMeasurable (G x) volume := fun x hx =>
      (hslice x hx).aestronglyMeasurable
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
  have : (fun s => VerticalIntegral' (F s) c) =
      fun s => (1 / (2 * Real.pi * I) : ℂ) • (I • ∫ y : ℝ, G s y) := by
    funext s
    simp [VerticalIntegral', VerticalIntegral, hGdef]
  rw [this]
  exact (hmain.const_smul (c := I)).const_smul (c := (1 / (2 * Real.pi * I) : ℂ))

end GoldbachBoundaries.Paper2.M1
