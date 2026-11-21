import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.Qcont_pole_split

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

-- Segment primitive helper (from `Fill/CCommon.lean`).
namespace GroupDPrimitive

/-- Points of a segment in a convex set. -/
theorem seg_mem {U : Set ℂ} (hUc : Convex ℝ U) {z₀ z : ℂ} (h₀ : z₀ ∈ U) (h : z ∈ U) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : z₀ + (τ : ℂ) * (z - z₀) ∈ U := by
  have := hUc.add_smul_sub_mem h₀ h hτ
  simpa [Complex.real_smul] using this

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

end GroupDPrimitive

/-- **The holomorphic part `E` of `P` on `H_{1/2}`** (under RH).

Sketch (avoids `log ζ`). Under RH, `-Qcont + 1/(z-1)` is holomorphic on the convex `H_{1/2}`
(the pole-set lemma for `Q`(iv): the only pole of `Qcont` there is `1`, residue `1`; `analyticAt_Qcont_of_RH`
and `Qcont_pole_split`-style removal at `1`), so it has a primitive `E₀` there (integral along
segments from `2`, Cauchy–Goursat for triangles; Mathlib `Complex.IsExactOn`/
`DifferentiableOn.isExactOn_ball`-type results, or by hand). On `ℍ`, `P + Log(z-1)` has the same
derivative (`hasDerivAt_P`, `Series.lean`), and `ℍ` is connected, so they differ by a constant;
adjust `E₀` by it. -/
theorem exists_Eaux (hRH : RiemannHypothesis) :
    ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (halfPlane (1 / 2)) ∧
      ∀ z ∈ HH, E z = P z + Complex.log (z - 1) := by
  obtain ⟨q, hq, hQ⟩ := Qcont_pole_split hRH (a := 1) (by simp [PoleSetQ])
  have hqh : AnalyticOnNhd ℂ q (halfPlane (1 / 2)) := by
    intro z hz
    apply hq z
    refine ⟨show 0 < z.re by have : 1 / 2 < z.re := hz; linarith, ?_⟩
    rintro ⟨hzS, hz1⟩
    have hmem : z ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨hzS, hz⟩
    rw [(lem_Sigma_iv_proof hRH).1] at hmem
    exact hz1 hmem
  have hconv : Convex ℝ (halfPlane (1 / 2)) := convex_halfSpace_re_gt _
  have h2 : (2 : ℂ) ∈ halfPlane (1 / 2) := by norm_num [halfPlane]
  let E : ℂ → ℂ := fun z => segInt (fun w => -q w) 2 z + (P 2 + Complex.log (2 - 1))
  have hEd : ∀ z ∈ halfPlane (1 / 2), HasDerivAt E (-q z) z := by
    intro z hz
    exact (GroupDPrimitive.hasDerivAt_segInt (isOpen_halfPlane _) hconv
      hqh.neg.differentiableOn h2 hz).add_const _
  have hEdo : DifferentiableOn ℂ E (halfPlane (1 / 2)) :=
    fun z hz => (hEd z hz).differentiableAt.differentiableWithinAt
  have hEa : AnalyticOnNhd ℂ E (halfPlane (1 / 2)) :=
    hEdo.analyticOnNhd (isOpen_halfPlane _)
  have hQeq : ∀ z ∈ HH, Qcont z = Q z := by
    intro z hz
    rw [← (hasSum_Q_moebius_zeta hz).tsum_eq, Qcont]
    apply tsum_congr
    intro n
    simp [sigmaTerm, negLogDerivZeta, neg_div]
  have hpd : ∀ z ∈ HH, HasDerivAt (fun z => P z + Complex.log (z - 1)) (-q z) z := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hz0 : 0 < z.re := by linarith
    have hzhalf : z ∈ halfPlane (1 / 2) := by change 1 / 2 < z.re; linarith
    have hz1 : z ≠ 1 := by intro he; simp [he] at hz'
    have hzS : z ∉ PoleSetQ := by
      intro he
      have hm : z ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨he, hzhalf⟩
      rw [(lem_Sigma_iv_proof hRH).1] at hm
      exact hz1 hm
    have hsplit := hQ z hz0 hzS
    rw [sigmaRes_eq hasResidue_Qcont_one, hQeq z hz] at hsplit
    have hlog : z - 1 ∈ slitPlane := by
      apply mem_slitPlane_iff.mpr
      left
      simp only [sub_re, one_re]
      linarith
    convert (hasDerivAt_P hz).add (((hasDerivAt_id z).sub_const 1).clog hlog) using 1
    · rfl
    · dsimp
      linear_combination hsplit
  have hsub : HH ⊆ halfPlane (1 / 2) := by intro z hz; change 1 / 2 < z.re; have : 1 < z.re := hz; linarith
  have heq := (isOpen_halfPlane 1).eqOn_of_deriv_eq
    (convex_halfSpace_re_gt (1 : ℝ)).isPreconnected
    (hEa.differentiableOn.mono hsub)
    (fun z hz => (hpd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hEd z (hsub hz)).deriv.trans (hpd z hz).deriv.symm)
    (show (2 : ℂ) ∈ HH by norm_num [halfPlane])
    (show E 2 = P 2 + Complex.log (2 - 1) by simp [E, segInt])
  exact ⟨E, hEa, heq⟩

/-! ### Lemmas that use `exists_Eaux` -/

section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

theorem Eaux_spec (hRH : RiemannHypothesis) :
    AnalyticOnNhd ℂ Eaux (halfPlane (1 / 2)) ∧ ∀ z ∈ HH, Eaux z = P z + Complex.log (z - 1) := by
  have h := exists_Eaux hRH
  have : Eaux = h.choose := by
    unfold Eaux
    split_ifs with h'
    · rfl
    · exact absurd h h'
  rw [this]
  exact h.choose_spec

end

end GoldbachBoundaries.ThmA
