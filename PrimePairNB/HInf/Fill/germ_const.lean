import PrimePairNB.HInf.Fill.Dth_eq
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.local_model_sheet
import PrimePairNB.HInf.Fill.exists_separating_iff
import PrimePairNB.HInf.Fill.isSeparating_eventually
import PrimePairNB.HInf.Fill.differentiableOn_graphInt
import PrimePairNB.HInf.Fill.isSeparating_line
import PrimePairNB.HInf.Fill.graphInt_line
import PrimePairNB.HInf.Fill.hasDerivAt_Pth
import PrimePairNB.HInf.Fill.interpPt_mem_of_separating
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-! The common eastward segment lies in both endpoint domains: a cut crossing
it would give a cut through the initial point at an intermediate slope. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/- Two facts about the sheet, stated here with their inputs resolved to the proved lemmas of this
folder. `LocalModel` supplies the corresponding contour estimates. -/
namespace RotationSheet

private theorem sheet_Pth_continuousOn (κ : ℝ) : ContinuousOn (Pth κ) (Uth κ) :=
  fun _ hz => (GoldbachBoundaries.HInf.Fill.hasDerivAt_Pth hz).continuousAt.continuousWithinAt

private theorem sheet_Pth_differentiableOn (κ : ℝ) : DifferentiableOn ℂ (Pth κ) (Uth κ) :=
  fun _ hz => (GoldbachBoundaries.HInf.Fill.hasDerivAt_Pth hz).differentiableAt.differentiableWithinAt

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
  obtain ⟨M, hM⟩ := LocalModel.sheet_norm_uniform hZ1 hZ2 hZ3 hK (K := K₀) (isCompact_closedBall _ _)
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
  exact LocalModel.Dth_eq_graphInt hZ1 hZ2 hZ3 hK hs.2.1 hs.1

/-- `D^θ = D` on `2 < Re v < 3`. -/
theorem Dth_eq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) (κ : ℝ) {v : ℂ} (h2 : 2 < v.re) (h3 : v.re < 3) : Dth k κ v = D v := by
  have hVt : v ∈ Vt top := by
    refine ⟨by linarith, lt_of_lt_of_le ?_ hK.three_le⟩
    have : ((v.re : ℝ) : EReal) < ((3 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr h3
    exact this.trans_eq (by norm_cast)
  have hv : v ∈ VInf top := (mem_Om_of_two_lt hZ1 (κ := κ) hVt h2).1
  set c : ℝ := v.re / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hc2 : c < v.re - 1 := by rw [hc]; linarith
  rw [LocalModel.Dth_eq_graphInt hZ1 hZ2 hZ3 hK hv (isSeparating_line hZ1 κ hc1 hc2), graphInt_line,
    hK.mb v h2 h3 c hc1 hc2]
  have hpt : ∀ y : ℝ, pairIntegrand k κ v ((c : ℂ) + (y : ℂ) * I) =
      k ((c : ℂ) + (y : ℂ) * I) v * P ((c : ℂ) + (y : ℂ) * I) * P (v - ((c : ℂ) + (y : ℂ) * I)) := by
    intro y
    have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
    unfold pairIntegrand
    rw [Pth_eq_P κ (by rw [hre]; exact hc1), Pth_eq_P κ (by rw [sub_re, hre]; linarith)]
  simp only [VerticalIntegral', VerticalIntegral, hpt]

end RotationSheet

private theorem east_mem_common {top : EReal} {v : ℂ} {κ₁ κ₂ : ℝ}
    (h : κ₁ ≤ κ₂) (hmem : ∀ κ ∈ Icc κ₁ κ₂, v ∈ Om κ top)
    {t : ℝ} (ht : 0 ≤ t) (hV : v + (t : ℂ) * slantDir κ₁ ∈ Vt top)
    {σ : ℝ} (hσ : σ ∈ Icc κ₁ κ₂) :
    v + (t : ℂ) * slantDir κ₁ ∈ Om σ top := by
  have hv := hmem κ₁ ⟨le_rfl, h⟩
  by_cases ht0 : t = 0
  · simpa [ht0] using hmem σ hσ
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  refine ⟨⟨hV, ?_⟩, ?_⟩
  · have hre : (v + (t : ℂ) * slantDir κ₁).re = v.re + t := by simp [slantDir]
    rw [hre]
    linarith [hv.1.2]
  · simp only [mem_iUnion, not_exists]
    rintro x hx ⟨s, hs, heq⟩
    let q : ℝ := (t * κ₁ + s * σ) / (t + s)
    have hts : 0 < t + s := by linarith
    have hq : q ∈ Icc κ₁ κ₂ := by
      constructor
      · apply (le_div_iff₀ hts).mpr
        nlinarith [hσ.1]
      · apply (div_le_iff₀ hts).mpr
        nlinarith [hσ.2]
    have hmul : q * (t + s) = t * κ₁ + s * σ := div_mul_cancel₀ _ (ne_of_gt hts)
    apply (hmem q hq).2
    refine mem_iUnion₂.mpr ⟨x, hx, t + s, le_of_lt hts, ?_⟩
    have hr := congrArg Complex.re heq
    have hi := congrArg Complex.im heq
    simp [slantDir] at hr hi
    apply Complex.ext <;> simp [slantDir] <;> nlinarith

/-- If `v₁ ∈ Ω_κ` for every `κ` in an interval, the germ of `D^κ` at `v₁` is constant on it. -/
theorem germ_const (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {v₁ : ℂ} {κ₁ κ₂ : ℝ} (h : κ₁ ≤ κ₂) (hmem : ∀ κ ∈ Icc κ₁ κ₂, v₁ ∈ Om κ top) :
    Dth k κ₂ =ᶠ[𝓝 v₁] Dth k κ₁ := by
  have hv₁ := hmem κ₁ ⟨le_rfl, h⟩
  have hv₂ := hmem κ₂ ⟨h, le_rfl⟩
  have heq {z : ℂ} (hz2 : 2 < z.re) (hz3 : z.re < 3) : Dth k κ₂ z = Dth k κ₁ z :=
    (RotationSheet.Dth_eq hZ1 hZ2 hZ3 hK κ₂ hz2 hz3).trans (RotationSheet.Dth_eq hZ1 hZ2 hZ3 hK κ₁ hz2 hz3).symm
  have hstrip {z : ℂ} (hz2 : 2 < z.re) (hz3 : z.re < 3) : Dth k κ₂ =ᶠ[𝓝 z] Dth k κ₁ := by
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (show 2 < z.re ∧ z.re < 3 from ⟨hz2, hz3⟩)] with w hw
    exact heq hw.1 hw.2
  by_cases hv2 : 2 < v₁.re
  · by_cases hv3 : v₁.re < 3
    · exact hstrip hv2 hv3
    -- For a base point further east, every intervening point is in every sheet.
    let U : Set ℂ := {z | 2 < z.re ∧ (z.re : EReal) < top}
    have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_coe_real_ereal.comp Complex.continuous_re) continuous_const)
    have hsub (σ : ℝ) : U ⊆ Om σ top := fun z hz => mem_Om_of_two_lt hZ1 ⟨by linarith [hz.1], hz.2⟩ hz.1
    have hUc : IsPreconnected U := by
      have hconv : Convex ℝ U := by
        intro a ha b hb s t hs ht hst
        have hmin : min a.re b.re ≤ s * a.re + t * b.re := by
          have h1 := mul_le_mul_of_nonneg_left (min_le_left a.re b.re) hs
          have h2 := mul_le_mul_of_nonneg_left (min_le_right a.re b.re) ht
          have h3 : s * min a.re b.re + t * min a.re b.re = min a.re b.re := by rw [← add_mul, hst, one_mul]
          linarith
        have hmax : s * a.re + t * b.re ≤ max a.re b.re := by
          have h1 := mul_le_mul_of_nonneg_left (le_max_left a.re b.re) hs
          have h2 := mul_le_mul_of_nonneg_left (le_max_right a.re b.re) ht
          have h3 : s * max a.re b.re + t * max a.re b.re = max a.re b.re := by rw [← add_mul, hst, one_mul]
          linarith
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
          exact lt_of_lt_of_le (lt_min ha.1 hb.1) hmin
        · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
          apply lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hmax)
          rcases le_total a.re b.re with hab | hab
          · simpa [max_eq_right hab] using hb.2
          · simpa [max_eq_left hab] using ha.2
      exact hconv.isPreconnected
    have h52 : (((5 / 2 : ℝ)) : EReal) < top := lt_of_lt_of_le (by
      have hh : (((5 / 2 : ℝ)) : EReal) < ((3 : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (by norm_num)
      exact hh.trans_eq (by norm_cast)) hK.three_le
    have hzU : (((5 / 2 : ℝ)) : ℂ) ∈ U := ⟨by norm_num, by simpa using h52⟩
    have hf := (RotationSheet.Dth_analyticOn hZ1 hZ2 hZ3 hK κ₂).mono (hsub κ₂)
    have hg := (RotationSheet.Dth_analyticOn hZ1 hZ2 hZ3 hK κ₁).mono (hsub κ₁)
    have hE := hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hzU (hstrip (by norm_num) (by norm_num))
    exact Filter.eventuallyEq_of_mem (hUo.mem_nhds ⟨hv2, hv₁.1.1.2⟩) hE
  · have hvle : v₁.re ≤ 2 := le_of_not_gt hv2
    let T : ℝ := 5 / 2 - v₁.re
    have hT : 0 ≤ T := by dsimp [T]; linarith
    let p : ℝ → ℂ := fun t => v₁ + (t : ℂ) * slantDir κ₁
    let U : Set ℂ := Om κ₁ top ∩ Om κ₂ top
    let C : Set ℂ := connectedComponentIn U v₁
    have hUo : IsOpen U := (isOpen_Om hZ1 κ₁ top).inter (isOpen_Om hZ1 κ₂ top)
    have h52 : (((5 / 2 : ℝ)) : EReal) < top := lt_of_lt_of_le (by
      have hh : (((5 / 2 : ℝ)) : EReal) < ((3 : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (by norm_num)
      exact hh.trans_eq (by norm_cast)) hK.three_le
    have hp : p '' Icc 0 T ⊆ U := by
      rintro _ ⟨t, ht, rfl⟩
      have hV : p t ∈ Vt top := by
        have hre : (p t).re = v₁.re + t := by simp [p, slantDir]
        refine ⟨?_, ?_⟩
        · rw [hre]; linarith [hv₁.1.1.1, ht.1]
        · rw [hre]
          have htT : t ≤ 5 / 2 - v₁.re := ht.2
          apply lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (show v₁.re + t ≤ 5 / 2 from by linarith)) h52
      exact ⟨east_mem_common h hmem ht.1 hV ⟨le_rfl, h⟩,
        east_mem_common h hmem ht.1 hV ⟨h, le_rfl⟩⟩
    have hpc : IsPreconnected (p '' Icc 0 T) := isPreconnected_Icc.image p (by fun_prop)
    have hvp : v₁ ∈ p '' Icc 0 T := ⟨0, ⟨le_rfl, hT⟩, by simp [p]⟩
    have hC : p '' Icc 0 T ⊆ C := hpc.subset_connectedComponentIn hvp hp
    have hpT : p T ∈ C := hC ⟨T, ⟨hT, le_rfl⟩, rfl⟩
    have hCre : (p T).re = 5 / 2 := by simp [p, T, slantDir]
    have hCsub : C ⊆ U := connectedComponentIn_subset U v₁
    have hf := (RotationSheet.Dth_analyticOn hZ1 hZ2 hZ3 hK κ₂).mono (fun z hz => (hCsub hz).2)
    have hg := (RotationSheet.Dth_analyticOn hZ1 hZ2 hZ3 hK κ₁).mono (fun z hz => (hCsub hz).1)
    have hE := hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_connectedComponentIn hpT
      (hstrip (by rw [hCre]; norm_num) (by rw [hCre]; norm_num))
    exact Filter.eventuallyEq_of_mem (hUo.connectedComponentIn.mem_nhds (mem_connectedComponentIn ⟨hv₁, hv₂⟩)) hE

end GoldbachBoundaries.HInf.Fill

