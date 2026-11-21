import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

/-!
# shared helpers for the log and Cauchy kernel lemmas

* `segFTC`: `g z - g z₀ = (z - z₀) ∫_0^1 g'(z₀ + τ(z - z₀)) dτ` on a convex open set.
* `hasDerivAt_segInt`: `z ↦ ∫_{[z₀,z]} g` is a primitive of `g` on a convex open set.
* `continuousOn_param_intervalIntegral`: continuity of a parametric interval integral, for a
  parameter set in which every point has a compact neighbourhood (within the set).
* `segR φ δ u = ∫_0^1 φ(δ, -δ + τ(u + δ)) dτ`, so that `segInt (φ δ) (-δ) u = (u + δ) segR φ δ u`,
  and its holomorphy in `δ`, also after integrating over `u`.
* `log_IBP`, `cauchy_split`: the two identities (integration by parts against `Log(δ+u)`,
  splitting off `f(-δ)/(δ+u)`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupC

/-- Points of a segment in a convex set. -/
theorem seg_mem {U : Set ℂ} (hUc : Convex ℝ U) {z₀ z : ℂ} (h₀ : z₀ ∈ U) (h : z ∈ U) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : z₀ + (τ : ℂ) * (z - z₀) ∈ U := by
  have := hUc.add_smul_sub_mem h₀ h hτ
  simpa [Complex.real_smul] using this

/-- Fundamental theorem of calculus along a segment. -/
theorem segFTC {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z₀ z : ℂ} (h₀ : z₀ ∈ U) (h : z ∈ U) :
    g z - g z₀ = (z - z₀) * ∫ τ in (0 : ℝ)..1, deriv g (z₀ + (τ : ℂ) * (z - z₀)) := by
  have hcont : ContinuousOn (deriv g) U := ((hg.analyticOnNhd hU).deriv).continuousOn
  have hderiv : ∀ τ ∈ [[(0 : ℝ), 1]], HasDerivAt (fun τ : ℝ => g (z₀ + (τ : ℂ) * (z - z₀)))
      ((z - z₀) * deriv g (z₀ + (τ : ℂ) * (z - z₀))) τ := by
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    have hw := seg_mem hUc h₀ h hτ
    have h1 : HasDerivAt (fun τ : ℝ => z₀ + (τ : ℂ) * (z - z₀)) (z - z₀) τ := by
      have := ((hasDerivAt_id (τ : ℂ)).mul_const (z - z₀)).const_add z₀
      simpa using this.comp_ofReal
    have h2 := ((hg.differentiableAt (hU.mem_nhds hw)).hasDerivAt).comp τ h1
    rw [mul_comm]; exact h2
  have hint : IntervalIntegrable (fun τ : ℝ => (z - z₀) * deriv g (z₀ + (τ : ℂ) * (z - z₀)))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    refine hcont.comp (by fun_prop) ?_
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    exact seg_mem hUc h₀ h hτ
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at this
  rw [this]
  simp

/-- `z ↦ ∫_{[z₀, z]} g` is a primitive of `g` on a convex open set. -/
theorem hasDerivAt_segInt {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z₀ z : ℂ} (h₀ : z₀ ∈ U) (h : z ∈ U) :
    HasDerivAt (fun z => segInt g z₀ z) (g z) z := by
  have hcont : ContinuousOn (deriv g) U := ((hg.analyticOnNhd hU).deriv).continuousOn
  have hgc : ContinuousOn g U := hg.continuousOn
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.mp hU z h
  set r : ℝ := r₀ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hcb : closedBall z r ⊆ U := (closedBall_subset_ball (by rw [hrdef]; linarith)).trans hr₀U
  -- the integrand and its derivative
  set w : ℂ → ℝ → ℂ := fun z' τ => z₀ + (τ : ℂ) * (z' - z₀) with hwdef
  have hwmem : ∀ z' ∈ closedBall z r, ∀ τ ∈ Icc (0 : ℝ) 1, w z' τ ∈ U := fun z' hz' τ hτ =>
    seg_mem hUc h₀ (hcb hz') hτ
  have hwcont : Continuous (Function.uncurry w) := by
    simp only [hwdef]; fun_prop
  obtain ⟨M, hM⟩ := ((isCompact_closedBall z r).prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun p : ℂ × ℝ => deriv g (w p.1 p.2))
    (hcont.comp hwcont.continuousOn fun p hp => hwmem p.1 hp.1 p.2 hp.2)
  have hIcc : ∀ τ ∈ Ι (0 : ℝ) 1, τ ∈ Icc (0 : ℝ) 1 := fun τ hτ => by
    rw [uIoc_of_le zero_le_one] at hτ; exact Ioc_subset_Icc_self hτ
  have hdw : ∀ z' ∈ closedBall z r, ∀ τ ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun z' => g (w z' τ)) ((τ : ℂ) * deriv g (w z' τ)) z' := by
    intro z' hz' τ hτ
    have h1 : HasDerivAt (fun z' => w z' τ) (τ : ℂ) z' := by
      have := ((hasDerivAt_id z').sub_const z₀).const_mul (τ : ℂ) |>.const_add z₀
      simpa [hwdef] using this
    have h2 := ((hg.differentiableAt (hU.mem_nhds (hwmem z' hz' τ hτ))).hasDerivAt).comp z' h1
    rw [mul_comm]; exact h2
  have hmeas : ∀ z' ∈ closedBall z r, AEStronglyMeasurable (fun τ => g (w z' τ))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    intro z' hz'
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact hgc.comp (by simp only [hwdef]; fun_prop) fun τ hτ => hwmem z' hz' τ (hIcc τ hτ)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := fun z' τ => g (w z' τ))
    (F' := fun z' τ => (τ : ℂ) * deriv g (w z' τ)) (x₀ := z) (bound := fun _ => M)
    (ball_mem_nhds z hr)
    (Filter.eventually_of_mem (closedBall_mem_nhds z hr) hmeas)
    (by
      apply ContinuousOn.intervalIntegrable
      refine hgc.comp (by simp only [hwdef]; fun_prop) fun τ hτ => ?_
      rw [uIcc_of_le zero_le_one] at hτ
      exact hwmem z (mem_closedBall_self hr.le) τ hτ)
    (by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      apply ContinuousOn.mul (by fun_prop)
      exact hcont.comp (by simp only [hwdef]; fun_prop) fun τ hτ =>
        hwmem z (mem_closedBall_self hr.le) τ (hIcc τ hτ))
    (Eventually.of_forall fun τ hτ z' hz' => by
      have hτ' := hIcc τ hτ
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hτ'.1]
      have := hM (z', τ) ⟨ball_subset_closedBall hz', hτ'⟩
      calc τ * ‖deriv g (w z' τ)‖ ≤ 1 * M := by
            apply mul_le_mul hτ'.2 this (norm_nonneg _) zero_le_one
        _ = M := one_mul M)
    intervalIntegrable_const
    (Eventually.of_forall fun τ hτ z' hz' => hdw z' (ball_subset_closedBall hz') τ (hIcc τ hτ))
  -- product rule
  have hprod := ((hasDerivAt_id z).sub_const z₀).mul key.2
  have hfun : (fun z => segInt g z₀ z) = fun z' => (id z' - z₀) * ∫ τ in (0 : ℝ)..1, g (w z' τ) := by
    funext z'; simp [segInt, hwdef]
  rw [hfun]
  convert hprod using 1
  -- `∫ g(w) + (z - z₀) ∫ τ g'(w) = g z` by the fundamental theorem of calculus
  have hFTC : ∀ τ ∈ [[(0 : ℝ), 1]], HasDerivAt (fun τ : ℝ => (τ : ℂ) * g (w z τ))
      (g (w z τ) + (τ : ℂ) * ((z - z₀) * deriv g (w z τ))) τ := by
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    have hwU := hwmem z (mem_closedBall_self hr.le) τ hτ
    have h1 : HasDerivAt (fun τ : ℝ => w z τ) (z - z₀) τ := by
      have := ((hasDerivAt_id (τ : ℂ)).mul_const (z - z₀)).const_add z₀
      simpa [hwdef] using this.comp_ofReal
    have h2 := ((hg.differentiableAt (hU.mem_nhds hwU)).hasDerivAt).comp τ h1
    have h3 : HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 τ := hasDerivAt_id (τ : ℂ) |>.comp_ofReal
    have := h3.mul h2
    convert this using 1
    · funext x; simp [Function.comp_def]
    · simp only [Function.comp_def]
      ring
  have hc1 : ContinuousOn (fun τ : ℝ => g (w z τ)) [[(0 : ℝ), 1]] := by
    refine hgc.comp (by simp only [hwdef]; fun_prop) fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    exact hwmem z (mem_closedBall_self hr.le) τ hτ
  have hc2 : ContinuousOn (fun τ : ℝ => deriv g (w z τ)) [[(0 : ℝ), 1]] := by
    refine hcont.comp (by simp only [hwdef]; fun_prop) fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    exact hwmem z (mem_closedBall_self hr.le) τ hτ
  have hint1 : IntervalIntegrable (fun τ : ℝ => g (w z τ)) volume 0 1 := hc1.intervalIntegrable
  have hint2 : IntervalIntegrable (fun τ : ℝ => (τ : ℂ) * ((z - z₀) * deriv g (w z τ)))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun τ : ℝ => (τ : ℂ)).continuousOn.mul
      (continuousOn_const.mul hc2)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hFTC (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at this
  have hw1 : w z 1 = z := by simp [hwdef]
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, sub_zero, hw1] at this
  rw [← this]
  have e : ∀ τ : ℝ, (τ : ℂ) * ((z - z₀) * deriv g (w z τ)) =
      (z - z₀) * ((τ : ℂ) * deriv g (w z τ)) := fun τ => by ring
  simp only [e, intervalIntegral.integral_const_mul, id]
  ring

/-- Continuity of a parametric interval integral, the parameter ranging over a set in which every
point has a compact neighbourhood (within the set). -/
theorem continuousOn_param_intervalIntegral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {S : Set X}
    {F : X → ℝ → ℂ} {a b : ℝ} (hF : ContinuousOn (Function.uncurry F) (S ×ˢ [[a, b]]))
    (hK : ∀ x ∈ S, ∃ K, IsCompact K ∧ K ⊆ S ∧ K ∈ 𝓝[S] x) :
    ContinuousOn (fun x => ∫ t in a..b, F x t) S := by
  intro x₀ hx₀
  obtain ⟨K, hKc, hKS, hKn⟩ := hK x₀ hx₀
  obtain ⟨M, hM⟩ := (hKc.prod isCompact_uIcc).exists_bound_of_continuousOn
    (hF.mono (prod_mono hKS subset_rfl))
  have hslice : ∀ x ∈ S, ContinuousOn (F x) [[a, b]] := by
    intro x hx
    have : ContinuousOn (fun t : ℝ => Function.uncurry F (x, t)) [[a, b]] :=
      hF.comp (Continuous.prodMk_right x).continuousOn (fun t ht => ⟨hx, ht⟩)
    simpa using this
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => M)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((hslice x hx).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hKn] with x hx
    exact ae_of_all _ fun t ht => hM (x, t) ⟨hx, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t ht => ?_
    have h1 := hF (x₀, t) ⟨hx₀, uIoc_subset_uIcc ht⟩
    have h2 : ContinuousWithinAt (fun x : X => (x, t)) S x₀ :=
      (Continuous.prodMk_left t).continuousWithinAt
    exact ContinuousWithinAt.comp (f := fun x : X => (x, t)) h1 h2
      (fun x hx => ⟨hx, uIoc_subset_uIcc ht⟩)

/-- `segR φ δ u = ∫_0^1 φ(δ, -δ + τ(u + δ)) dτ`. -/
def segR (φ : ℂ → ℂ → ℂ) (δ u : ℂ) : ℂ := ∫ τ in (0 : ℝ)..1, φ δ (-δ + (τ : ℂ) * (u + δ))

theorem segInt_eq_segR (φ : ℂ → ℂ → ℂ) (δ u : ℂ) :
    segInt (φ δ) (-δ) u = (u + δ) * segR φ δ u := by
  simp [segInt, segR, sub_neg_eq_add]

theorem neg_mem_ball_zero {ρ : ℝ} {δ : ℂ} (h : δ ∈ ball (0 : ℂ) ρ) : -δ ∈ ball (0 : ℂ) ρ := by
  simpa [mem_ball_zero_iff, norm_neg] using h

section segR

variable {φ : ℂ → ℂ → ℂ} {ρ : ℝ} {U : Set ℂ}

theorem segR_pt_mem (hUc : Convex ℝ U) (hball : ball (0 : ℂ) ρ ⊆ U) {δ u : ℂ}
    (hδ : δ ∈ ball (0 : ℂ) ρ) (hu : u ∈ U) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    -δ + (τ : ℂ) * (u + δ) ∈ U := by
  have := seg_mem hUc (hball (neg_mem_ball_zero hδ)) hu hτ
  simpa [sub_neg_eq_add] using this

theorem differentiableOn_segR (hU : IsOpen U) (hUc : Convex ℝ U) (hball : ball (0 : ℂ) ρ ⊆ U)
    (hφ : DifferentiableOn ℂ (Function.uncurry φ) (ball (0 : ℂ) ρ ×ˢ U)) {u : ℂ} (hu : u ∈ U) :
    DifferentiableOn ℂ (fun δ => segR φ δ u) (ball (0 : ℂ) ρ) := by
  apply differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
    (f := fun δ (τ : ℝ) => φ δ (-δ + (τ : ℂ) * (u + δ)))
  · have : ContinuousOn (fun p : ℂ × ℝ => Function.uncurry φ (p.1, -p.1 + (p.2 : ℂ) * (u + p.1)))
        (ball (0 : ℂ) ρ ×ˢ [[(0 : ℝ), 1]]) := by
      refine hφ.continuousOn.comp (by fun_prop) fun p hp => ⟨hp.1, ?_⟩
      have h2 := hp.2
      rw [uIcc_of_le zero_le_one] at h2
      exact segR_pt_mem hUc hball hp.1 hu h2
    exact this
  · intro τ hτ δ hδ
    rw [uIcc_of_le zero_le_one] at hτ
    have hw := segR_pt_mem hUc hball hδ hu hτ
    have h1 : DifferentiableAt ℂ (Function.uncurry φ) (δ, -δ + (τ : ℂ) * (u + δ)) :=
      hφ.differentiableAt ((isOpen_ball.prod hU).mem_nhds ⟨hδ, hw⟩)
    have h2 : DifferentiableAt ℂ (fun δ : ℂ => (δ, -δ + (τ : ℂ) * (u + δ))) δ := by fun_prop
    exact (h1.comp δ h2).differentiableWithinAt

theorem continuousOn_segR2 (hUc : Convex ℝ U) (hball : ball (0 : ℂ) ρ ⊆ U)
    (hφ : DifferentiableOn ℂ (Function.uncurry φ) (ball (0 : ℂ) ρ ×ˢ U)) {w₁ w₂ : ℝ}
    (hseg : ∀ u ∈ [[w₁, w₂]], (u : ℂ) ∈ U) :
    ContinuousOn (Function.uncurry fun δ (u : ℝ) => segR φ δ u) (ball (0 : ℂ) ρ ×ˢ [[w₁, w₂]]) := by
  have := continuousOn_param_intervalIntegral (X := ℂ × ℝ) (S := ball (0 : ℂ) ρ ×ˢ [[w₁, w₂]])
    (a := 0) (b := 1) (F := fun p (τ : ℝ) => φ p.1 (-p.1 + (τ : ℂ) * ((p.2 : ℂ) + p.1))) ?_ ?_
  · exact this
  · have : ContinuousOn (fun q : (ℂ × ℝ) × ℝ =>
        Function.uncurry φ (q.1.1, -q.1.1 + (q.2 : ℂ) * ((q.1.2 : ℂ) + q.1.1)))
        ((ball (0 : ℂ) ρ ×ˢ [[w₁, w₂]]) ×ˢ [[(0 : ℝ), 1]]) := by
      refine hφ.continuousOn.comp (by fun_prop) fun q hq => ⟨hq.1.1, ?_⟩
      have h2 := hq.2
      rw [uIcc_of_le zero_le_one] at h2
      exact segR_pt_mem hUc hball hq.1.1 (hseg _ hq.1.2) h2
    exact this
  · rintro ⟨δ₀, u₀⟩ ⟨hδ₀, hu₀⟩
    have hr : 0 < (ρ - ‖δ₀‖) / 2 := by
      have := mem_ball_zero_iff.mp hδ₀; linarith
    refine ⟨closedBall δ₀ ((ρ - ‖δ₀‖) / 2) ×ˢ [[w₁, w₂]],
      (isCompact_closedBall _ _).prod isCompact_uIcc, ?_, ?_⟩
    · refine prod_mono (fun z hz => ?_) subset_rfl
      rw [mem_closedBall] at hz
      rw [mem_ball_zero_iff]
      have := mem_ball_zero_iff.mp hδ₀
      calc ‖z‖ ≤ ‖z - δ₀‖ + ‖δ₀‖ := norm_le_norm_sub_add z δ₀
        _ = dist z δ₀ + ‖δ₀‖ := by rw [dist_eq_norm]
        _ < ρ := by linarith
    · refine mem_nhdsWithin.mpr ⟨ball δ₀ ((ρ - ‖δ₀‖) / 2) ×ˢ univ,
        isOpen_ball.prod isOpen_univ, ⟨mem_ball_self hr, trivial⟩, fun p hp => ?_⟩
      exact ⟨ball_subset_closedBall hp.1.1, hp.2.2⟩

theorem differentiableOn_int_segR (hU : IsOpen U) (hUc : Convex ℝ U)
    (hball : ball (0 : ℂ) ρ ⊆ U)
    (hφ : DifferentiableOn ℂ (Function.uncurry φ) (ball (0 : ℂ) ρ ×ˢ U)) {w₁ w₂ : ℝ}
    (hseg : ∀ u ∈ [[w₁, w₂]], (u : ℂ) ∈ U) :
    DifferentiableOn ℂ (fun δ => ∫ u in w₁..w₂, segR φ δ u) (ball (0 : ℂ) ρ) :=
  differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
    (continuousOn_segR2 hUc hball hφ hseg)
    (fun u hu => differentiableOn_segR hU hUc hball hφ (hseg u hu))

end segR

/-- Integration by parts against `Log(δ + u)`. -/
theorem log_IBP {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {δ : ℂ} (hδ : -δ ∈ U) {w₁ w₂ : ℝ}
    (hseg : ∀ u ∈ [[w₁, w₂]], (u : ℂ) ∈ U) (hslit : ∀ u ∈ [[w₁, w₂]], δ + u ∈ slitPlane) :
    ∫ u in w₁..w₂, g u * Complex.log (δ + u) =
      segInt g (-δ) w₂ * Complex.log (δ + w₂) - segInt g (-δ) w₁ * Complex.log (δ + w₁) -
        ∫ u in w₁..w₂, segR (fun _ => g) δ u := by
  have hS : ∀ u ∈ [[w₁, w₂]], HasDerivAt (fun u : ℝ => segInt g (-δ) u) (g u) u := fun u hu =>
    (hasDerivAt_segInt hU hUc hg hδ (hseg u hu)).comp_ofReal
  have hL : ∀ u ∈ [[w₁, w₂]], HasDerivAt (fun u : ℝ => Complex.log (δ + u)) (1 / (δ + u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => δ + (u : ℂ)) 1 u := by
      simpa using ((hasDerivAt_id (u : ℂ)).const_add δ).comp_ofReal
    exact h1.clog_real (hslit u hu)
  have hderiv : ∀ u ∈ [[w₁, w₂]], HasDerivAt
      (fun u : ℝ => segInt g (-δ) u * Complex.log (δ + u))
      (g u * Complex.log (δ + u) + segInt g (-δ) u * (1 / (δ + u))) u := by
    intro u hu
    exact (hS u hu).mul (hL u hu)
  have hgc : ∀ u ∈ [[w₁, w₂]], ContinuousAt (fun u : ℝ => g u) u := fun u hu =>
    (hg.differentiableAt (hU.mem_nhds (hseg u hu))).continuousAt.comp continuous_ofReal.continuousAt
  have hA : ContinuousOn (fun u : ℝ => g u * Complex.log (δ + u)) [[w₁, w₂]] := fun u hu =>
    ((hgc u hu).mul ((hL u hu).continuousAt)).continuousWithinAt
  have hB : ContinuousOn (fun u : ℝ => segInt g (-δ) u * (1 / (δ + u))) [[w₁, w₂]] := by
    intro u hu
    have hne : δ + (u : ℂ) ≠ 0 := slitPlane_ne_zero (hslit u hu)
    refine ((hS u hu).continuousAt.mul ?_).continuousWithinAt
    exact continuousAt_const.div (by fun_prop) hne
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hA.intervalIntegrable.add hB.intervalIntegrable)
  rw [intervalIntegral.integral_add hA.intervalIntegrable hB.intervalIntegrable] at hFTC
  have hBR : ∫ u in w₁..w₂, segInt g (-δ) u * (1 / (δ + u)) =
      ∫ u in w₁..w₂, segR (fun _ => g) δ u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hne : δ + (u : ℂ) ≠ 0 := slitPlane_ne_zero (hslit u hu)
    rw [segInt_eq_segR (fun _ => g) δ u]
    field_simp
    ring
  rw [hBR] at hFTC
  linear_combination hFTC

/-- Splitting off `f(-δ)/(δ + u)` from a Cauchy-kernel integral. -/
theorem cauchy_split {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {δ : ℂ} (hδ : -δ ∈ U) {w₁ w₂ : ℝ}
    (hseg : ∀ u ∈ [[w₁, w₂]], (u : ℂ) ∈ U) (hslit : ∀ u ∈ [[w₁, w₂]], δ + u ∈ slitPlane) :
    ∫ u in w₁..w₂, f u / (δ + u) =
      (∫ u in w₁..w₂, segR (fun _ => deriv f) δ u) +
        f (-δ) * (Complex.log (δ + w₂) - Complex.log (δ + w₁)) := by
  have hL : ∀ u ∈ [[w₁, w₂]], HasDerivAt (fun u : ℝ => Complex.log (δ + u)) (1 / (δ + u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => δ + (u : ℂ)) 1 u := by
      simpa using ((hasDerivAt_id (u : ℂ)).const_add δ).comp_ofReal
    exact h1.clog_real (hslit u hu)
  have hinv : ContinuousOn (fun u : ℝ => 1 / (δ + u)) [[w₁, w₂]] := by
    intro u hu
    have hne : δ + (u : ℂ) ≠ 0 := slitPlane_ne_zero (hslit u hu)
    have : ContinuousAt (fun u : ℝ => 1 / (δ + (u : ℂ))) u :=
      ContinuousAt.div continuousAt_const (by fun_prop) hne
    exact this.continuousWithinAt
  have hlogint : ∫ u in w₁..w₂, 1 / (δ + u) = Complex.log (δ + w₂) - Complex.log (δ + w₁) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hL hinv.intervalIntegrable
  have hfc : ContinuousOn (fun u : ℝ => f u) [[w₁, w₂]] := fun u hu =>
    ((hf.differentiableAt (hU.mem_nhds (hseg u hu))).continuousAt.comp
      continuous_ofReal.continuousAt).continuousWithinAt
  have hA : ContinuousOn (fun u : ℝ => f u / (δ + u)) [[w₁, w₂]] := by
    intro u hu
    have hne : δ + (u : ℂ) ≠ 0 := slitPlane_ne_zero (hslit u hu)
    exact ((hfc u hu).div (by fun_prop) hne)
  have hB : ContinuousOn (fun u : ℝ => f (-δ) * (1 / (δ + u))) [[w₁, w₂]] :=
    continuousOn_const.mul hinv
  have hsplit : ∫ u in w₁..w₂, f u / (δ + u) - f (-δ) * (1 / (δ + u)) =
      ∫ u in w₁..w₂, segR (fun _ => deriv f) δ u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hne : δ + (u : ℂ) ≠ 0 := slitPlane_ne_zero (hslit u hu)
    have h := segFTC hU hUc hf hδ (hseg u hu)
    simp only [sub_neg_eq_add] at h
    simp only [segR]
    have : f u = f (-δ) + (u + δ) * ∫ τ in (0 : ℝ)..1, deriv f (-δ + (τ : ℂ) * (u + δ)) := by
      rw [← h]; ring
    rw [this]
    field_simp
    ring
  rw [intervalIntegral.integral_sub hA.intervalIntegrable hB.intervalIntegrable,
    intervalIntegral.integral_const_mul, hlogint] at hsplit
  rw [← hsplit]
  ring

/-! ### Small facts used by the four kernel lemmas -/

theorem slice_differentiableOn {φ : ℂ → ℂ → ℂ} {ρ : ℝ} {U : Set ℂ}
    (hφ : DifferentiableOn ℂ (Function.uncurry φ) (ball (0 : ℂ) ρ ×ˢ U)) {δ : ℂ}
    (hδ : δ ∈ ball (0 : ℂ) ρ) : DifferentiableOn ℂ (φ δ) U := by
  have := hφ.comp ((differentiableOn_const δ).prodMk differentiableOn_id)
    (fun w hw => ⟨hδ, hw⟩)
  exact this

theorem log_eq_log_neg_add {z : ℂ} (h : 0 < z.im) :
    Complex.log z = Complex.log (-z) + (Real.pi : ℂ) * I := by
  simp only [Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos h]
  push_cast
  ring

theorem re_add_pos {ρ w : ℝ} {δ : ℂ} (hδ : δ ∈ ball (0 : ℂ) ρ) (hw : ρ < w) :
    0 < (δ + w).re := by
  have h1 := mem_ball_zero_iff.mp hδ
  have h2 := Complex.abs_re_le_norm δ
  simp only [add_re, ofReal_re]
  linarith [neg_abs_le δ.re]

theorem re_neg_sub_pos {ρ w : ℝ} {δ : ℂ} (hδ : δ ∈ ball (0 : ℂ) ρ) (hw : w < -ρ) :
    0 < (-δ - w).re := by
  have h1 := mem_ball_zero_iff.mp hδ
  have h2 := Complex.abs_re_le_norm δ
  simp only [sub_re, neg_re, ofReal_re]
  linarith [le_abs_self δ.re]

theorem add_mem_slitPlane_of_nonneg {ε : ℂ} (hε : ε ∈ slitPlane) {u : ℝ} (hu : 0 ≤ u) :
    ε + u ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hε ⊢
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  rcases hε with h | h
  · left; linarith
  · right; exact h

theorem add_mem_slitPlane_of_im_pos {δ : ℂ} (hδ : 0 < δ.im) (u : ℝ) : δ + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simp only [add_im, ofReal_im, add_zero]
  exact hδ.ne'

end GroupC

end GoldbachBoundaries.ThmA
