import PrimePairNB.HInf.Fill.local_model_sheet
import PrimePairNB.HInf.Fill.arc_model
import PrimePairNB.HInf.Fill.Pth_local
import PrimePairNB.HInf.Fill.exists_outer_contour
import PrimePairNB.HInf.Fill.exists_glued_graph
import PrimePairNB.HInf.Fill.graphInt_eq_outer_add_arcs
import PrimePairNB.HInf.Fill.Dth_analyticOn
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.exists_arc
import PrimePairNB.HInf.Fill.interpPt_mem_of_separating

/-! Assembly of the local model, in the coordinate `t = (z-a)/slantDir κ`.
All local and contour inputs are imported from the files of this folder. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

private lemma scaled_Pth {κ : ℝ} (hκ : IsGenericSlope κ) {a : ℂ} (ha : a ∈ PoleSetQ) :
    ∃ q : ℝ, 0 < q ∧ ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (ball 0 (2 * q)) ∧
      ∀ t ∈ ball (0 : ℂ) (2 * q), t ∈ slitPlane →
        Pth κ (a + t * slantDir κ) = cP a * Complex.log t + E t := by
  obtain ⟨R, hR, -, -, E, hE, he⟩ := Pth_local ha (fun b hb hba => hκ.1 b hb a ha hba)
  have hw := ThmA.slantDir_ne_zero κ
  have hn : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hw
  let q := R / (4 * ‖slantDir κ‖)
  have hq : 0 < q := by dsimp [q]; positivity
  have hm (t : ℂ) (ht : t ∈ ball (0 : ℂ) (2 * q)) : a + t * slantDir κ ∈ ball a R := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul]
    have ht' := mem_ball_zero_iff.mp ht
    have heq : 2 * q * ‖slantDir κ‖ = R / 2 := by dsimp [q]; field_simp; ring
    have := mul_lt_mul_of_pos_right ht' hn
    rw [heq] at this
    linarith
  refine ⟨q, hq, fun t => cP a * Complex.log (slantDir κ) + E (a + t * slantDir κ), ?_, ?_⟩
  · intro t ht
    exact analyticAt_const.add (AnalyticAt.comp (f := fun t : ℂ => a + t * slantDir κ)
      (hE _ (hm t ht)) (by fun_prop))
  · intro t ht hs
    have hr : a + t * slantDir κ ∉ rayW κ a := by
      rw [not_mem_rayW_iff]
      simpa [hw] using hs
    rw [he _ ⟨hm t ht, hr⟩]
    simp only [logK, add_sub_cancel_left, mul_div_cancel_right₀ _ hw]
    ring

private lemma scaled_kernel {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {x a : ℂ} (hxV : x ∈ Vt top)
    (ha : a ∈ collide x) :
    ∃ q : ℝ, 0 < q ∧ DifferentiableOn ℂ
      (fun p : ℂ × ℂ => slantDir κ * k (a + p.1 * slantDir κ) (x + p.2 * slantDir κ))
      (ball (0 : ℂ) (2 * q) ×ˢ ball (0 : ℂ) (2 * q)) := by
  let g : ℂ × ℂ → ℂ × ℂ := fun p => (a + p.1 * slantDir κ, x + p.2 * slantDir κ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hmem : g (0, 0) ∈ domK top := by
    have hb := (M1.poleSetQ_re_bounds ha.2).1
    refine ⟨by simpa [g] using hxV, ?_, ?_⟩
    · simpa [g] using (M1.poleSetQ_re_bounds ha.1).1
    · simpa [g, sub_re] using hb
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp ((isOpen_domK top).preimage hg) (0, 0) hmem
  refine ⟨R / 4, by positivity, ?_⟩
  refine DifferentiableOn.const_mul (hK.holo.comp (f := g) (by dsimp [g]; fun_prop) ?_) _
  rintro ⟨t, ε⟩ ⟨ht, hε⟩
  apply hball
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨(mem_ball.mp ht).trans (by linarith), (mem_ball.mp hε).trans (by linarith)⟩

private lemma local_arc_data {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ}
    (hxV : x ∈ Vt top) (a : collide x) :
    ∃ q : ℝ, 0 < q ∧ ∃ E₁ E₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ E₁ (ball 0 (2 * q)) ∧ AnalyticOnNhd ℂ E₂ (ball 0 (2 * q)) ∧
      DifferentiableOn ℂ
        (fun p : ℂ × ℂ => slantDir κ * k (a + p.1 * slantDir κ) (x + p.2 * slantDir κ))
        (ball (0 : ℂ) (2 * q) ×ˢ ball (0 : ℂ) (2 * q)) ∧
      (∀ t ∈ ball (0 : ℂ) (2 * q), t ∈ slitPlane →
        Pth κ (a + t * slantDir κ) = cP a * Complex.log t + E₁ t) ∧
      (∀ t ∈ ball (0 : ℂ) (2 * q), t ∈ slitPlane →
        Pth κ (x - a + t * slantDir κ) = cP (x - a) * Complex.log t + E₂ t) := by
  obtain ⟨q₁, hq₁, E₁, hE₁, he₁⟩ := scaled_Pth hκ a.property.1
  obtain ⟨q₂, hq₂, E₂, hE₂, he₂⟩ := scaled_Pth hκ a.property.2
  obtain ⟨q₃, hq₃, hf⟩ := scaled_kernel hK hxV a.property
  let q := min q₁ (min q₂ q₃)
  have hq1 : q ≤ q₁ := min_le_left _ _
  have hq2 : q ≤ q₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hq3 : q ≤ q₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hm1 : ball (0 : ℂ) (2 * q) ⊆ ball 0 (2 * q₁) := ball_subset_ball (by linarith)
  have hm2 : ball (0 : ℂ) (2 * q) ⊆ ball 0 (2 * q₂) := ball_subset_ball (by linarith)
  have hm3 : ball (0 : ℂ) (2 * q) ⊆ ball 0 (2 * q₃) := ball_subset_ball (by linarith)
  exact ⟨q, lt_min hq₁ (lt_min hq₂ hq₃), E₁, E₂, hE₁.mono hm1, hE₂.mono hm2,
    hf.mono (Set.prod_mono hm3 hm3), (fun t ht => he₁ t (hm1 ht)), (fun t ht => he₂ t (hm2 ht))⟩

private lemma local_Xc_sum (hZ1 : Z1) {x : ℂ} (hx : x ∈ Xcat)
    (k : ℂ → ℂ → ℂ) (v : ℂ) [Fintype (collide x)] :
    Xc k x v = ∑ a : collide x, cP a * cP (x - a) * Jv k a (x - a) v := by
  classical
  letI := finite_pairs hZ1 hx
  letI := Fintype.ofFinite (pinchPairs x)
  let e : collide x ≃ pinchPairs x :=
    { toFun := fun a => ⟨(a, x - a), a.property.1, a.property.2, by simp⟩
      invFun := fun p => ⟨p.1.1, p.2.1, by
        have heq : x - p.1.1 = p.1.2 := by linear_combination -p.2.2.2
        simpa only [heq] using p.2.2.1⟩
      left_inv := fun a => rfl
      right_inv := fun p => by apply Subtype.ext; apply Prod.ext; rfl; dsimp; linear_combination -p.2.2.2 }
  rw [Xc, tsum_fintype]
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

private lemma local_graph_integrable (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D)
    {κ : ℝ} {v : ℂ} (hv : v ∈ VInf top) {Γ : SlantGraph κ} (hΓ : IsSeparating v Γ) :
    Integrable (fun h : ℝ => pairIntegrand k κ v (Γ.pt h) *
      (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))) := by
  obtain ⟨e, he, hm⟩ := interpPt_mem_of_separating hΓ hΓ
  have hmem (h : ℝ) := hm 0 (by simp) h
  simp only [sheet_interpPt_self] at hmem
  have hc : Continuous (fun h => pairIntegrand k κ v (Γ.pt h)) :=
    (LocalModel.sheet_pairIntegrand_differentiableOn hK κ hv.1).continuousOn.comp_continuous
      (sheet_pt_continuous Γ) (fun h => ⟨(hmem h).1, (hmem h).2.1, by
        change (Γ.pt h).re < v.re
        linarith only [he, (hmem h).2.2.2]⟩)
  obtain ⟨M, hM⟩ := LocalModel.norm_pairIntegrand_le hZ1 hZ2 hZ3 hK hv hΓ hΓ
  have hdec (h : ℝ) : ‖pairIntegrand k κ v (Γ.pt h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
    simpa only [sheet_interpPt_self] using hM 0 (by simp) h
  obtain ⟨L, hL⟩ := Γ.lip
  have hi : Integrable (fun h : ℝ => (1 + |h|) ^ (-(3 / 2) : ℝ)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num))
  have hmeas : AEStronglyMeasurable (fun h : ℝ => pairIntegrand k κ v (Γ.pt h) *
      (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))) volume :=
    hc.aestronglyMeasurable.mul
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (aestronglyMeasurable_deriv Γ.ξ volume)).add_const I).const_mul (slantDir κ))
  apply (hi.const_mul (M * (‖slantDir κ‖ * (max L 0 + 1)))).mono' hmeas
  filter_upwards [(show ∀ᵐ h : ℝ, h ∉ Γ.brk from
    ae_iff.mpr (by simpa using Γ.brk.finite_toSet.measure_zero volume))] with h hh
  have hb : ‖slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I)‖ ≤ ‖slantDir κ‖ * (max L 0 + 1) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_add_le _ _).trans
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_I]
    exact add_le_add ((hL h hh).trans (le_max_left L 0)) le_rfl
  rw [norm_mul]
  calc
    _ ≤ (M * (1 + |h|) ^ (-(3 / 2) : ℝ)) * (‖slantDir κ‖ * (max L 0 + 1)) :=
      mul_le_mul (hdec h) hb (norm_nonneg _) ((norm_nonneg _).trans (hdec h))
    _ = _ := by ring

private lemma local_outer_eq {κ : ℝ} {Γ Γ₀ : SlantGraph κ} {x : ℂ}
    (hfin : (collide x).Finite) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (he : ∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h) (f : ℂ → ℂ) :
    (∫ h in outerHeights κ x r₀, f (Γ.pt h) *
      (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))) =
    ∫ h in outerHeights κ x r₀, f (Γ₀.pt h) *
      (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I)) := by
  classical
  letI := hfin.fintype
  let B := ((fun a => hgt κ a - r₀) '' collide x) ∪ ((fun a => hgt κ a + r₀) '' collide x)
  have hB : B.Finite := (hfin.image _).union (hfin.image _)
  have hae : ∀ᵐ h : ℝ, h ∉ B := ae_iff.mpr (by simpa using hB.measure_zero volume)
  have hmeas : MeasurableSet (outerHeights κ x r₀) := by
    have : IsClosed (outerHeights κ x r₀) := by
      simp only [outerHeights, Set.ofPred_forall]
      exact isClosed_biInter (fun a _ => isClosed_le continuous_const (by fun_prop))
    exact this.measurableSet
  apply integral_congr_ae
  apply (ae_restrict_iff' hmeas).mpr
  filter_upwards [hae] with h hh hhout
  have hs (a : collide x) : r₀ < |h - hgt κ a| := by
    have hn1 : h ≠ hgt κ a - r₀ := fun hn => hh (Or.inl ⟨a, a.property, hn.symm⟩)
    have hn2 : h ≠ hgt κ a + r₀ := fun hn => hh (Or.inr ⟨a, a.property, hn.symm⟩)
    have := hhout a a.property
    rcases le_abs.mp this with hpos | hneg
    · rw [abs_of_nonneg (by linarith : 0 ≤ h - hgt κ a)]
      exact lt_of_le_of_ne hpos (by intro hn; apply hn2; linarith)
    · rw [abs_of_nonpos (by linarith : h - hgt κ a ≤ 0)]
      exact lt_of_le_of_ne (by linarith) (by intro hn; apply hn1; linarith)
  have hev : ∀ᶠ t in 𝓝 h, ∀ a : collide x, r₀ < |t - hgt κ a| :=
    eventually_all.mpr fun a => (isOpen_lt continuous_const (by fun_prop)).mem_nhds (hs a)
  have hξ : Γ.ξ =ᶠ[𝓝 h] Γ₀.ξ := by
    filter_upwards [hev] with t ht
    exact he t (fun a ha => (ht ⟨a, ha⟩).le)
  have hpt : Γ.pt h = Γ₀.pt h := by simp only [SlantGraph.pt, he h hhout]
  rw [hpt, hξ.deriv_eq]

/-- Assemble the outer contour and every ordered collision pair. -/
theorem local_model (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ VInf top ∧ ball x r \ rayW κ x ⊆ Om κ top ∧
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball x r) ∧
        ∀ v ∈ ball x r \ rayW κ x, Dth k κ v = logK κ (v - x) * Xc k x v + H v := by
  classical
  have hfin := collide_finite hZ1 hx
  letI := hfin.fintype
  have hw := ThmA.slantDir_ne_zero κ
  have hwn : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr hw
  have hw1 : 1 ≤ ‖slantDir κ‖ := by
    simpa [slantDir] using Complex.abs_re_le_norm (slantDir κ)
  choose q hq E₁ E₂ hE₁ hE₂ hf he₁ he₂ using (local_arc_data hK hκ hxV)
  obtain ⟨R, hR, hRq⟩ := finite_positive_lower_bound (Set.toFinite (Set.univ : Set (collide x)))
    q (fun a _ => hq a)
  obtain ⟨r₀, ρ, hr₀, hrR, hρ, hρr, hdisj, hV, hOm, Γ₀, hflat, hsep, hout⟩ :=
    exists_outer_contour hZ1 hZ2 hZ3 hK hκ hx hxV hR
  have hsmall (a : collide x) : ball (0 : ℂ) (2 * r₀) ⊆ ball 0 (2 * q a) :=
    ball_subset_ball (by have := hrR.trans (hRq a (mem_univ a)).le; linarith)
  have ham (a : collide x) := arc_model hr₀
    (f := fun t ε => slantDir κ * k (a + t * slantDir κ) (x + ε * slantDir κ))
    ((hf a).mono (Set.prod_mono (hsmall a) (hsmall a)))
    ((hE₁ a).mono (hsmall a)) ((hE₂ a).mono (hsmall a)) (cP a) (cP (x - a))
  choose s hs hsr H hH hmodel using ham
  obtain ⟨d, hd, hds⟩ := finite_positive_lower_bound (Set.toFinite (Set.univ : Set (collide x)))
    (fun a => s a * ‖slantDir κ‖) (fun a _ => mul_pos (hs a) hwn)
  let r := min ρ d
  have hr : 0 < r := lt_min hρ hd
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrd : r ≤ d := min_le_right _ _
  let ε : ℂ → ℂ := fun v => (v - x) / slantDir κ
  have hε (v : ℂ) (hv : v ∈ ball x r) (a : collide x) : ε v ∈ ball (0 : ℂ) (s a) := by
    rw [mem_ball_zero_iff]
    change ‖(v - x) / slantDir κ‖ < s a
    rw [norm_div, div_lt_iff₀ hwn]
    have hvn : ‖v - x‖ < r := by simpa [dist_eq_norm] using hv
    exact hvn.trans (hrd.trans_lt (hds a (mem_univ a)))
  have hε₀ (v : ℂ) (hv : v ∈ ball x r) : ‖ε v‖ < r₀ / 4 := by
    change ‖(v - x) / slantDir κ‖ < r₀ / 4
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hw1).trans_lt
    have hvn : ‖v - x‖ < r := by simpa [dist_eq_norm] using hv
    exact hvn.trans (hrρ.trans_lt hρr)
  let O : ℂ → ℂ := fun v => (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ h in outerHeights κ x r₀, pairIntegrand k κ v (Γ₀.pt h) *
      (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I))
  let Hloc : ℂ → ℂ := fun v => O v + ∑ a : collide x, H a (ε v) - Complex.log (slantDir κ) * Xc k x v
  have hsub : ball x r ⊆ ball x ρ := ball_subset_ball hrρ
  have hHloc : AnalyticOnNhd ℂ Hloc (ball x r) := by
    have hO : DifferentiableOn ℂ O (ball x r) := (hout.mono hsub).const_mul _
    have hsum : DifferentiableOn ℂ (fun v => ∑ a : collide x, H a (ε v)) (ball x r) := by
      apply DifferentiableOn.fun_sum
      intro a _
      exact (hH a).differentiableOn.comp (f := ε) (by dsimp [ε]; fun_prop) (fun v hv => hε v hv a)
    exact (hO.add hsum |>.sub ((Xc_analyticOn hZ1 hK hx).differentiableOn.mono
      (fun v hv => (hV (hsub hv)).1) |>.const_mul _)).analyticOnNhd isOpen_ball
  refine ⟨r, hr, hsub.trans hV, (sdiff_subset_sdiff_left hsub).trans hOm, Hloc, hHloc, ?_⟩
  intro v hv
  have hev : ε v ∈ slitPlane := (not_mem_rayW_iff κ x v).mp hv.2
  obtain ⟨ξ, hξ⟩ := exists_arc hr₀ (hε₀ v hv.1) hev
  obtain ⟨Γ, -, hext, hbands⟩ := exists_glued_graph Γ₀ hfin hr₀ hdisj hflat
    (hε₀ v hv.1) (fun _ => ξ) (fun _ _ => hξ)
  have hΓ : IsSeparating v Γ := hsep v ⟨hsub hv.1, hv.2⟩ Γ hext (fun a ha => (hbands a ha).1)
  have hsplit := graphInt_eq_outer_add_arcs Γ hfin hr₀ hdisj
    (local_graph_integrable hZ1 hZ2 hZ3 hK (hV (hsub hv.1)) hΓ)
  have hew : ε v * slantDir κ = v - x := div_mul_cancel₀ _ hw
  have hvw : x + ε v * slantDir κ = v := by rw [hew]; ring
  have harc (a : collide x) :
      arcInt r₀ (fun h => Γ.ξ (h + hgt κ a) - absc κ a)
        (fun t => slantDir κ * pairIntegrand k κ v (a + t * slantDir κ)) =
      Complex.log (ε v) * (cP a * cP (x - a) * Jv k a (x - a) v) + H a (ε v) := by
    let η : ℝ → ℝ := fun h => Γ.ξ (h + hgt κ a) - absc κ a
    have hη : IsArc r₀ (ε v) η := (hbands a a.property).1
    have hm := hmodel a (ε v) (hε v hv.1 a) hev η hη
    have hI : ε v * (∫ τ in (0 : ℝ)..1, slantDir κ *
        k (a + ((τ : ℂ) * ε v) * slantDir κ) (x + ε v * slantDir κ)) =
        Jv k a (x - a) v := by
      simp_rw [hvw]
      rw [intervalIntegral.integral_const_mul, ← mul_assoc, hew]
      have hab : v - (a : ℂ) - (x - a) = v - x := by ring
      simp only [Jv, hab]
      congr 2
      funext τ
      rw [mul_assoc, hew]
    rw [hI] at hm
    have heq : arcInt r₀ η (fun t => slantDir κ * pairIntegrand k κ v (a + t * slantDir κ)) =
        arcInt r₀ η (fun t => (slantDir κ * k (a + t * slantDir κ) (x + ε v * slantDir κ)) *
          (cP a * Complex.log t + E₁ a t) *
          (cP (x - a) * Complex.log (ε v - t) + E₂ a (ε v - t))) := by
      unfold arcInt
      congr 1
      apply intervalIntegral.integral_congr
      intro h hh
      have hh' : h ∈ Icc (-r₀) r₀ := by simpa [uIcc_of_le (by linarith : -r₀ ≤ r₀)] using hh
      let t := arcPt η h
      have ht : t ∈ ball (0 : ℂ) (2 * r₀) :=
        mem_ball_zero_iff.mpr ((hη.small h hh').trans (by linarith))
      have hu : ε v - t ∈ ball (0 : ℂ) (2 * r₀) := by
        rw [mem_ball_zero_iff]
        have htn : ‖t‖ < 3 * r₀ / 2 := hη.small h hh'
        exact (norm_sub_le _ _).trans_lt (by linarith only [htn, hε₀ v hv.1, hr₀])
      have hsl := arcPt_slit hη h
      have hu_eq : v - (a + t * slantDir κ) = x - a + (ε v - t) * slantDir κ := by
        linear_combination -hew
      change slantDir κ * pairIntegrand k κ v (a + t * slantDir κ) * _ = _
      unfold pairIntegrand
      rw [he₁ a t (hsmall a ht) hsl.1, hu_eq, he₂ a _ (hsmall a hu) hsl.2, hvw]
      dsimp only [t, arcPt]
      ring
    rw [heq, hm]
    ring
  rw [LocalModel.Dth_eq_graphInt hZ1 hZ2 hZ3 hK (hV (hsub hv.1)) hΓ, hsplit,
    local_outer_eq hfin hr₀ hext]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hfs : (∑ a ∈ hfin.toFinset, arcInt r₀ (fun h => Γ.ξ (h + hgt κ a) - absc κ a)
      (fun t => slantDir κ * pairIntegrand k κ v (a + t * slantDir κ))) =
      ∑ a : collide x, arcInt r₀ (fun h => Γ.ξ (h + hgt κ a) - absc κ a)
        (fun t => slantDir κ * pairIntegrand k κ v (a + t * slantDir κ)) := by
    exact Finset.sum_subtype _ (fun a => hfin.mem_toFinset) _
  rw [hfs]
  simp_rw [harc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← local_Xc_sum hZ1 hx k v]
  dsimp [Hloc, O, logK, ε]
  ring

end GoldbachBoundaries.HInf.Fill
