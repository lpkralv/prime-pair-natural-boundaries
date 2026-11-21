import PrimePairNB.HInf.Defs

/-! Holomorphy for the outer-height integral, isolated from its geometric and growth inputs. -/
noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

private theorem differentiableOn_dominated_height_integral {U : Set ℂ} (hU : IsOpen U)
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

/-- Holomorphy on the full parameter disc follows once the outer integrand is
measurable, pointwise holomorphic there, and uniformly dominated on compact sets.
The indicator handles the omitted bands without requiring continuity at their ends. -/
theorem outer_contour_holomorphy {κ : ℝ} {x : ℂ} {r₀ r : ℝ}
    {k : ℂ → ℂ → ℂ} (Γ₀ : SlantGraph κ)
    (hmeas : ∀ v ∈ ball x r, AEStronglyMeasurable
      (fun h => pairIntegrand k κ v (Γ₀.pt h) *
        (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I)))
      (volume.restrict (outerHeights κ x r₀)))
    (hhol : ∀ h ∈ outerHeights κ x r₀, DifferentiableOn ℂ
      (fun v => pairIntegrand k κ v (Γ₀.pt h)) (ball x r))
    (hdom : ∀ K ⊆ ball x r, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ v ∈ K, ∀ h ∈ outerHeights κ x r₀,
        ‖pairIntegrand k κ v (Γ₀.pt h) *
          (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I))‖ ≤ g h) :
    DifferentiableOn ℂ (fun v => ∫ h in outerHeights κ x r₀,
      pairIntegrand k κ v (Γ₀.pt h) *
        (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I))) (ball x r) := by
  classical
  let E := outerHeights κ x r₀
  have hE : MeasurableSet E := by
    have hc : IsClosed E := by
      dsimp [E, outerHeights]
      simp only [setOf_forall]
      exact isClosed_biInter fun a ha => isClosed_le continuous_const (by fun_prop)
    exact hc.measurableSet
  have heq : (fun v => ∫ h in outerHeights κ x r₀,
      pairIntegrand k κ v (Γ₀.pt h) * (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I))) =
      (fun v => ∫ h : ℝ, E.indicator (fun h => pairIntegrand k κ v (Γ₀.pt h) *
        (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I))) h) := by
    funext v
    exact (integral_indicator hE).symm
  rw [heq]
  apply differentiableOn_dominated_height_integral isOpen_ball
  · intro v hv
    exact (aestronglyMeasurable_indicator_iff hE).mpr (hmeas v hv)
  · intro h
    by_cases hh : h ∈ E
    · simpa only [Set.indicator_of_mem hh] using (hhol h hh).mul_const
        (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I))
    · simpa only [Set.indicator_of_notMem hh] using
        (differentiableOn_const (0 : ℂ) : DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) (ball x r))
  · intro K hK hKc
    obtain ⟨g, hg, hgb⟩ := hdom K hK hKc
    refine ⟨fun h => |g h|, hg.abs, ?_⟩
    intro v hv h
    by_cases hh : h ∈ E
    · rw [Set.indicator_of_mem hh]
      exact (hgb v hv h hh).trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hh, norm_zero]
      exact abs_nonneg _

end GoldbachBoundaries.HInf.Fill

