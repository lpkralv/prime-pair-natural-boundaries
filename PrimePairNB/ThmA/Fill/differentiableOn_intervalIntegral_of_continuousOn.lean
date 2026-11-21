import PrimePairNB.ThmA.G15_Kernel

/-!
# Holomorphic dependence of an interval integral on a parameter

Proof: differentiation under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The derivative
`∂ₛ f(s,u)` is bounded uniformly near `s₀` by Cauchy's estimate
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) and a bound of `‖f‖` on the compact
`closedBall s₀ R ×ˢ [[a,b]]`; it is ae-strongly measurable in `u` as a pointwise limit of
difference quotients, each continuous in `u`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-- **Holomorphic dependence of an interval integral on a parameter** (general; Mathlib
does not seem to have it in this form).

Sketch. Fix `s₀ ∈ U` and a closed disc `D̄ = closedBall s₀ ρ ⊆ U`. `f` is uniformly continuous on
the compact `D̄ × [[a,b]]`; Cauchy's formula on `∂D` gives `∂ₛ f(s,u) = (2πi)⁻¹ ∮ f(w,u)/(w-s)² dw`,
bounded uniformly for `s ∈ ball s₀ (ρ/2)`, `u ∈ [[a,b]]`. Apply
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with that bound. (Alternatively:
Morera via `Complex.differentiableOn_of_...`/Fubini on triangles.) Upstream. -/
theorem differentiableOn_intervalIntegral_of_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {a b : ℝ}
    {f : ℂ → ℝ → ℂ} (hc : ContinuousOn (Function.uncurry f) (U ×ˢ [[a, b]]))
    (hd : ∀ u ∈ [[a, b]], DifferentiableOn ℂ (fun s => f s u) U) :
    DifferentiableOn ℂ (fun s => ∫ u in a..b, f s u) U := by
  intro s₀ hs₀
  -- a closed disc around `s₀` inside `U`
  obtain ⟨R₀, hR₀, hR₀U⟩ := Metric.isOpen_iff.mp hU s₀ hs₀
  set R : ℝ := R₀ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hcbU : closedBall s₀ R ⊆ U :=
    (closedBall_subset_ball (by rw [hRdef]; linarith)).trans hR₀U
  -- continuity of each slice
  have hslice : ∀ x ∈ U, ContinuousOn (f x) [[a, b]] := by
    intro x hx
    have : ContinuousOn (fun t : ℝ => Function.uncurry f (x, t)) [[a, b]] :=
      hc.comp (Continuous.prodMk_right x).continuousOn (fun t ht => ⟨hx, ht⟩)
    simpa using this
  have hmeas : ∀ x ∈ U, AEStronglyMeasurable (f x) (volume.restrict (Ι a b)) := fun x hx =>
    ((hslice x hx).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  -- a bound for `‖f‖` on the compact `closedBall s₀ R ×ˢ [[a,b]]`
  obtain ⟨M, hM⟩ := ((isCompact_closedBall s₀ R).prod isCompact_uIcc).exists_bound_of_continuousOn
    (hc.mono (prod_mono hcbU subset_rfl))
  -- the derivative and its bound
  set F' : ℂ → ℝ → ℂ := fun x t => deriv (fun s => f s t) x with hF'def
  have hderiv : ∀ t ∈ [[a, b]], ∀ x ∈ U, HasDerivAt (fun s => f s t) (F' x t) x := by
    intro t ht x hx
    exact ((hd t ht).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hbound : ∀ t ∈ [[a, b]], ∀ x ∈ ball s₀ (R / 2), ‖F' x t‖ ≤ M / (R / 2) := by
    intro t ht x hx
    have hsub : closedBall x (R / 2) ⊆ closedBall s₀ R := by
      apply closedBall_subset_closedBall'
      have := mem_ball.mp hx
      linarith [dist_comm x s₀]
    have hdc : DiffContOnCl ℂ (fun s => f s t) (ball x (R / 2)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball x (by positivity)]
      exact (hd t ht).mono (hsub.trans hcbU)
    apply norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hdc
    intro z hz
    exact hM (z, t) ⟨hsub (sphere_subset_closedBall hz), ht⟩
  -- measurability of `F' s₀` as a limit of difference quotients
  have hF'meas : AEStronglyMeasurable (F' s₀) (volume.restrict (Ι a b)) := by
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
      (f := fun n t => (h n)⁻¹ • (f (s₀ + h n) t - f s₀ t)) (fun n => ?_) ?_
    · exact ((hmeas _ (hhmem n)).sub (hmeas _ hs₀)).const_smul (h n)⁻¹
    · refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
      exact ((hderiv t (uIoc_subset_uIcc ht) s₀ hs₀).tendsto_slope_zero).comp hh
  have hball : ball s₀ (R / 2) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hcbU
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := f) (F' := F') (x₀ := s₀) (bound := fun _ => M / (R / 2))
    (ball_mem_nhds s₀ (by positivity))
    (Filter.eventually_of_mem (hU.mem_nhds hs₀) fun x hx => hmeas x hx)
    ((hslice s₀ hs₀).intervalIntegrable)
    hF'meas
    (Eventually.of_forall fun t ht x hx => hbound t (uIoc_subset_uIcc ht) x hx)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht x hx => hderiv t (uIoc_subset_uIcc ht) x (hball hx))
  exact key.2.differentiableAt.differentiableWithinAt

end GoldbachBoundaries.ThmA
