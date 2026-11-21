import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

set_option maxHeartbeats 1000000
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

-- Joint continuity helper (from `Fill/CCommon.lean`).
/-- Continuity of a parametric interval integral, the parameter ranging over a set in which every
point has a compact neighbourhood (within the set). -/
private theorem D_continuousOn_param_intervalIntegral {X : Type*} [TopologicalSpace X]
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

/-- **Holomorphy of `N₁` where the segment misses `Σ`** (the principal-sheet proposition, "Holomorphy";
also the `𝒮₁` parts in the local model and the access lemma). No RH.

Sketch. For `u ∈ [0, 1-b]`: `Re(1 - uv) = 1 - u ≥ b > 0` and `Re(s - 1 + uv) > 0` near `s₀`, so
both `Γ` factors are holomorphic. The compact segment `{s₀ - 1 + uv}` lies in `{Re > 0} ∖ Σ`, which
is open (`Σ` locally finite in `Re > 0`; unconditionally the points `ρ/n` with `Re ≥ x` are finite
in bounded sets), so a uniform neighbourhood of it avoids `Σ`, and `Qcont` is holomorphic there
(`analyticAt_Qcont_sub_sum`, `regular_of_not_mem_poleSetQ`, `SigmaMeromorphic.lean`). Then
`(s,u) ↦ ∫_u^{1-b} Qcont(s-1+u'v) du'` is jointly continuous and holomorphic in `s`, and so is
the full integrand; `differentiableOn_intervalIntegral_of_continuousOn` again. `A(s - w_b)` is holomorphic near `s₀` by `hA`. -/
theorem analyticAt_N1A {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {A : ℂ → ℂ} {s₀ : ℂ}
    (h1 : 1 < s₀.re) (hA : AnalyticAt ℂ A (s₀ - wb κ b))
    (hseg : ∀ u ∈ Icc (0 : ℝ) (1 - b), s₀ - 1 + (u : ℂ) * slantDir κ ∉ PoleSetQ) :
    AnalyticAt ℂ (N1A κ b A) s₀ := by
  let c : ℝ := 1 - b
  have hc0 : 0 ≤ c := by dsimp [c]; linarith [hb.2]
  have hI : [[(0 : ℝ), c]] = Icc (0 : ℝ) c := uIcc_of_le hc0
  let z : ℂ → ℝ → ℂ := fun s u => s - 1 + (u : ℂ) * slantDir κ
  have hzre : ∀ s : ℂ, ∀ u : ℝ, (z s u).re = s.re - 1 + u := by
    intro s u
    simp [z, slantDir]
  have hQnear : ∀ᶠ s in 𝓝 s₀, ∀ u ∈ Icc (0 : ℝ) c, AnalyticAt ℂ Qcont (z s u) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hz0 : 0 < (z s₀ u).re := by rw [hzre]; linarith [hu.1]
    have hQ : AnalyticAt ℂ Qcont (z s₀ u) := by
      simpa using analyticAt_Qcont_sub_sum hz0 ∅
        (fun n _ hmu => regular_of_not_mem_poleSetQ hz0 (hseg u hu) hmu)
    have hzc : ContinuousAt (fun p : ℂ × ℝ => z p.1 p.2) (s₀, u) := by dsimp [z]; fun_prop
    exact Filter.Tendsto.eventually hzc hQ.eventually_analyticAt
  have hAnear : ∀ᶠ s in 𝓝 s₀, AnalyticAt ℂ A (s - wb κ b) := by
    have hzc : ContinuousAt (fun s : ℂ => s - wb κ b) s₀ := by fun_prop
    exact Filter.Tendsto.eventually hzc hA.eventually_analyticAt
  have hHnear : ∀ᶠ s in 𝓝 s₀, 1 < s.re := (isOpen_halfPlane 1).mem_nhds h1
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hQnear.and (hAnear.and hHnear))
  let U := ball s₀ r
  have hQall : ∀ s ∈ U, ∀ u ∈ Icc (0 : ℝ) c, AnalyticAt ℂ Qcont (z s u) :=
    fun s hs => (hball s hs).1
  have hAall : ∀ s ∈ U, AnalyticAt ℂ A (s - wb κ b) :=
    fun s hs => (hball s hs).2.1
  have hHall : ∀ s ∈ U, 1 < s.re := fun s hs => (hball s hs).2.2
  have hQc : ContinuousOn (fun p : ℂ × ℝ => Qcont (z p.1 p.2)) (U ×ˢ Icc (0 : ℝ) c) := by
    rintro ⟨s,u⟩ ⟨hs,hu⟩
    exact ((hQall s hs u hu).continuousAt.comp
      (f := fun p : ℂ × ℝ => z p.1 p.2) (x := (s,u)) (by dsimp [z]; fun_prop)).continuousWithinAt
  have hmove : ∀ u ∈ Icc (0 : ℝ) c, ∀ t ∈ [[(0 : ℝ), 1]], u + (c - u) * t ∈ Icc (0 : ℝ) c := by
    intro u hu t ht
    rw [uIcc_of_le zero_le_one] at ht
    constructor <;> nlinarith [hu.1, hu.2, mul_nonneg (sub_nonneg.mpr hu.2) ht.1,
      mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr ht.2)]
  have hK : ∀ p ∈ U ×ˢ Icc (0 : ℝ) c, ∃ K : Set (ℂ × ℝ), IsCompact K ∧
      K ⊆ U ×ˢ Icc (0 : ℝ) c ∧ K ∈ 𝓝[U ×ˢ Icc (0 : ℝ) c] p := by
    rintro ⟨s,u⟩ ⟨hs,hu⟩
    obtain ⟨d, hd, hdU⟩ := Metric.isOpen_iff.mp (show IsOpen U from isOpen_ball) s hs
    refine ⟨closedBall s (d / 2) ×ˢ Icc (0 : ℝ) c,
      (isCompact_closedBall _ _).prod isCompact_Icc, ?_, ?_⟩
    · exact prod_mono ((closedBall_subset_ball (by linarith)).trans hdU) subset_rfl
    · refine mem_nhdsWithin.mpr ⟨ball s (d / 2) ×ˢ univ, isOpen_ball.prod isOpen_univ,
        ⟨mem_ball_self (by linarith), trivial⟩, ?_⟩
      intro p hp
      exact ⟨ball_subset_closedBall hp.1.1, hp.2.2⟩
  have hIc : ContinuousOn (fun p : ℂ × ℝ => ∫ t in (0 : ℝ)..1,
      Qcont (z p.1 (p.2 + (c - p.2) * t))) (U ×ˢ Icc (0 : ℝ) c) := by
    have hmap : Continuous (fun p : (ℂ × ℝ) × ℝ =>
        (p.1.1, p.1.2 + (c - p.1.2) * p.2)) := by fun_prop
    have hT : ContinuousOn (fun p : (ℂ × ℝ) × ℝ =>
        Qcont (z p.1.1 (p.1.2 + (c - p.1.2) * p.2)))
        ((U ×ˢ Icc (0 : ℝ) c) ×ˢ [[(0 : ℝ), 1]]) :=
      hQc.comp (f := fun p : (ℂ × ℝ) × ℝ => (p.1.1, p.1.2 + (c - p.1.2) * p.2))
        hmap.continuousOn (fun p hp => ⟨hp.1.1, hmove _ hp.1.2 _ hp.2⟩)
    exact D_continuousOn_param_intervalIntegral hT hK
  have hchange : ∀ s : ℂ, ∀ u : ℝ, (∫ t in u..c, Qcont (z s t)) =
      ((c - u : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, Qcont (z s (u + (c - u) * t)) := by
    intro s u
    have h := intervalIntegral.smul_integral_comp_add_mul (fun t => Qcont (z s t))
      (a := 0) (b := 1) (c - u) u
    simpa [Complex.real_smul] using h.symm
  have hPc : ContinuousOn (fun p : ℂ × ℝ => PsegA κ b A p.1 p.2) (U ×ˢ Icc (0 : ℝ) c) := by
    have hAc : ContinuousOn (fun p : ℂ × ℝ => A (p.1 - wb κ b)) (U ×ˢ Icc (0 : ℝ) c) := by
      rintro ⟨s,u⟩ ⟨hs,hu⟩
      exact ((hAall s hs).continuousAt.comp
        (f := fun p : ℂ × ℝ => p.1 - wb κ b) (x := (s,u)) (by fun_prop)).continuousWithinAt
    have h : ContinuousOn (fun p : ℂ × ℝ => A (p.1 - wb κ b) +
        slantDir κ * (((c - p.2 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
          Qcont (z p.1 (p.2 + (c - p.2) * t)))) (U ×ˢ Icc (0 : ℝ) c) :=
      hAc.add (continuousOn_const.mul ((by fun_prop :
      ContinuousOn (fun p : ℂ × ℝ => ((c - p.2 : ℝ) : ℂ)) (U ×ˢ Icc (0 : ℝ) c)).mul hIc))
    apply h.congr
    intro p hp
    simp only [PsegA, hchange, z, c]
  have hPd : ∀ u ∈ Icc (0 : ℝ) c, DifferentiableOn ℂ (fun s => PsegA κ b A s u) U := by
    intro u hu
    have hi : DifferentiableOn ℂ (fun s => ∫ t in u..c, Qcont (z s t)) U := by
      apply differentiableOn_intervalIntegral_of_continuousOn isOpen_ball
      · apply hQc.mono
        rw [uIcc_of_le hu.2]
        exact prod_mono subset_rfl (Icc_subset_Icc hu.1 le_rfl)
      · intro t ht s hs
        rw [uIcc_of_le hu.2] at ht
        have hzt : DifferentiableAt ℂ (fun s : ℂ => z s t) s := by dsimp [z]; fun_prop
        exact ((hQall s hs t ⟨hu.1.trans ht.1, ht.2⟩).differentiableAt.comp s hzt).differentiableWithinAt
    have hAd : DifferentiableOn ℂ (fun s => A (s - wb κ b)) U :=
      fun s hs => ((hAall s hs).differentiableAt.comp s (by fun_prop)).differentiableWithinAt
    exact hAd.add (hi.const_mul (slantDir κ))
  have hγ : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Gamma w := by
    intro w hw
    apply differentiableAt_Gamma
    intro n he
    have := congrArg Complex.re he
    simp only [neg_re, natCast_re] at this
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hγ1 : ∀ u ∈ Icc (0 : ℝ) c, 0 < (1 - (u : ℂ) * slantDir κ).re := by
    intro u hu
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have hv : (slantDir κ).re = 1 := by simp [slantDir]
    rw [hv, mul_one]
    dsimp [c] at hu
    linarith [hb.1, hu.2]
  have hγ2 : ∀ s ∈ U, ∀ u ∈ Icc (0 : ℝ) c, 0 < (z s u).re := by
    intro s hs u hu
    rw [hzre]
    linarith [hHall s hs, hu.1]
  have hc : ContinuousOn (Function.uncurry (fun (s : ℂ) (u : ℝ) =>
      Gamma (1 - (u : ℂ) * slantDir κ) * Gamma (z s u) * PsegA κ b A s u))
      (U ×ˢ [[(0 : ℝ), c]]) := by
    rw [hI]
    apply ContinuousOn.mul _ hPc
    apply ContinuousOn.mul
    · rintro ⟨s,u⟩ ⟨hs,hu⟩
      exact ((hγ _ (hγ1 u hu)).continuousAt.comp
        (f := fun p : ℂ × ℝ => 1 - (p.2 : ℂ) * slantDir κ) (x := (s,u)) (by fun_prop)).continuousWithinAt
    · rintro ⟨s,u⟩ ⟨hs,hu⟩
      exact ((hγ _ (hγ2 s hs u hu)).continuousAt.comp
        (f := fun p : ℂ × ℝ => z p.1 p.2) (x := (s,u)) (by dsimp [z]; fun_prop)).continuousWithinAt
  have hd : DifferentiableOn ℂ (fun s => ∫ u in (0 : ℝ)..c,
      Gamma (1 - (u : ℂ) * slantDir κ) * Gamma (z s u) * PsegA κ b A s u) U := by
    apply differentiableOn_intervalIntegral_of_continuousOn isOpen_ball hc
    intro u hu s hs
    rw [hI] at hu
    have hzt : DifferentiableAt ℂ (fun s : ℂ => z s u) s := by dsimp [z]; fun_prop
    exact (((hγ _ (hγ2 s hs u hu)).comp s hzt).const_mul
      (Gamma (1 - (u : ℂ) * slantDir κ))).differentiableWithinAt.mul (hPd u hu s hs)
  exact (hd.const_mul (slantDir κ)).analyticAt (ball_mem_nhds s₀ hr)

end GoldbachBoundaries.ThmA
