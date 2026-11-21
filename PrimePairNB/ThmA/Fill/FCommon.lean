import PrimePairNB.ThmA.G18_LocalAccess
import Mathlib.MeasureTheory.Group.Prod
import PrimePairNB.TIdentity.Basic
import PrimePairNB.ThmA.Fill.Pv_spec
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

lemma F_two_mem_catalogue : (2 : ℂ) ∈ catalogue := by
  exact Or.inl (Or.inl rfl)

lemma F_re_slant (κ : ℝ) : (slantDir κ).re = 1 := by simp [slantDir]

lemma F_re_wb (κ b : ℝ) : (wb κ b).re = b := by simp [wb, slantDir]

lemma F_re_segment (κ : ℝ) (s : ℂ) (u : ℝ) :
    (s - 1 + (u : ℂ) * slantDir κ).re = s.re - 1 + u := by simp [slantDir]

lemma F_of_not_slit {z : ℂ} (hz : z ∉ slitPlane) :
    z.re ≤ 0 ∧ z = (z.re : ℂ) := by
  simp only [mem_slitPlane_iff, not_or, not_lt, not_not] at hz
  refine ⟨hz.1, ?_⟩
  apply Complex.ext <;> simp [hz.2]

lemma F_Omega_no_pole {κ : ℝ} {s : ℂ} (hs : s ∈ Omega κ) {u : ℝ} (hu : 0 ≤ u) :
    s - 1 + (u : ℂ) * slantDir κ ∉ PoleSetQ := by
  intro hp
  have hC := one_add_mem_catalogue_of_mem_poleSetQ hp
  apply hs.2 (mem_biUnion hC ?_)
  refine ⟨u, hu, ?_, ?_⟩
  · rw [add_re, one_re, F_re_segment]
    have : 1 < s.re := hs.1
    linarith
  · ring

lemma F_Omega_not_segSS {κ b : ℝ} {s : ℂ} (hs : s ∈ Omega κ) : s ∉ segSS κ b := by
  rintro ⟨u, hu, he⟩
  apply hs.2 (mem_biUnion F_two_mem_catalogue ?_)
  refine ⟨u, hu.1, ?_, he⟩
  have hs1 : 1 < s.re := hs.1
  rw [he] at hs1
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, F_re_slant] at hs1
  norm_num at hs1 ⊢
  linarith

lemma F_Omega_anchor_slit {κ b : ℝ} (hb : b < 1) {s : ℂ} (hs : s ∈ Omega κ) :
    (s - wb κ b - 1) / slantDir κ ∈ slitPlane := by
  by_contra h
  obtain ⟨hq, he⟩ := F_of_not_slit h
  set q := ((s - wb κ b - 1) / slantDir κ).re
  have he' : s = 2 - ((1 - b - q : ℝ) : ℂ) * slantDir κ := by
    have h := (div_eq_iff (slantDir_ne_zero κ)).mp he
    simp only [wb] at h
    push_cast at h ⊢
    linear_combination h
  apply hs.2 (mem_biUnion F_two_mem_catalogue ?_)
  refine ⟨1 - b - q, by dsimp [q]; linarith, ?_, he'⟩
  have hs1 : 1 < s.re := hs.1
  rw [he'] at hs1
  simp [slantDir] at hs1
  norm_num
  linarith

lemma F_goodSlant_segment {κ : ℝ} (hκ : IsGoodSlant κ) {α : ℂ} (hα : α ∈ catalogue)
    {u : ℝ} (hu : 0 < u) : α - 1 + (u : ℂ) * slantDir κ ∉ PoleSetQ := by
  intro hp
  have hC := one_add_mem_catalogue_of_mem_poleSetQ hp
  have hne : α ≠ 1 + (α - 1 + (u : ℂ) * slantDir κ) := by
    intro he
    have := congrArg Complex.re he
    simp [slantDir] at this
    linarith
  exact hκ.2.2 α hα _ hC hne (-u) (by push_cast; ring)

lemma F_goodSlant_off_two_line {κ : ℝ} (hκ : IsGoodSlant κ) {α : ℂ}
    (hα : α ∈ catalogue) (hne : α ≠ 2) (t : ℝ) :
    α ≠ 2 - (t : ℂ) * slantDir κ := by
  intro he
  exact hκ.2.2 α hα 2 F_two_mem_catalogue hne (-t) (by rw [he]; push_cast; ring)

lemma F_PsegA_eq_P (hRH : RiemannHypothesis) {κ b : ℝ} {s : ℂ}
    (hs : 2 < s.re) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (1 - b)) :
    PsegA κ b (Pv κ) s u = P (s - 1 + (u : ℂ) * slantDir κ) := by
  have hre : ∀ t ∈ Icc u (1 - b), 1 < (s - 1 + (t : ℂ) * slantDir κ).re := by
    intro t ht
    rw [F_re_segment]
    linarith [ht.1, hu.1]
  have hc : ContinuousOn (fun t : ℝ => Q (s - 1 + (t : ℂ) * slantDir κ)) (Icc u (1 - b)) :=
    Q_differentiableOn.continuousOn.comp (by fun_prop) hre
  have hd : ∀ t ∈ [[u, 1 - b]], HasDerivAt
      (fun t : ℝ => P (s - 1 + (t : ℂ) * slantDir κ))
      (-(slantDir κ) * Q (s - 1 + (t : ℂ) * slantDir κ)) t := by
    intro t ht
    rw [uIcc_of_le hu.2] at ht
    have h := ((hasDerivAt_P (hre t ht)).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const (slantDir κ)).const_add (s - 1))).comp_ofReal
    convert h using 1 <;> first | rfl | ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hc.const_mul (-(slantDir κ))).intervalIntegrable_of_Icc hu.2)
  rw [intervalIntegral.integral_const_mul] at hFTC
  have he : s - wb κ b = s - 1 + ((1 - b : ℝ) : ℂ) * slantDir κ := by
    simp only [wb]; ring
  have hpv := (Pv_spec hRH κ).1 _ (he.symm ▸ hre (1 - b) ⟨hu.2, le_rfl⟩)
  have hi : (∫ t in u..(1 - b), Qcont (s - 1 + (t : ℂ) * slantDir κ)) =
      ∫ t in u..(1 - b), Q (s - 1 + (t : ℂ) * slantDir κ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu.2] at ht
    exact TIdentity.Qcont_eq_Q_of_one_lt (hre t ht)
  rw [PsegA, hpv, he, hi]
  linear_combination -hFTC

lemma F_square_diagonal {c : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 c ×ˢ Icc 0 c)) :
    (∫ u in (0 : ℝ)..c, ∫ t in (0 : ℝ)..c, f (u,t)) =
      ∫ w in (0 : ℝ)..(2*c), ∫ u in (max 0 (w-c))..(min w c), f (u,w-u) := by
  let S := Icc (0 : ℝ) c ×ˢ Icc (0 : ℝ) c
  let F : ℝ × ℝ → ℂ := S.indicator f
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2-p.1)
  have hfi : IntegrableOn f S (volume.prod volume) :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hF : Integrable F (volume.prod volume) := (integrable_indicator_iff hS).mpr hfi
  have hmp : MeasurePreserving T (volume.prod volume) (volume.prod volume) :=
    measurePreserving_prod_sub volume volume
  have hG := hmp.integrable_comp_of_integrable hF
  have hemb : MeasurableEmbedding T := by
    exact (MeasurableEquiv.shearSubRight ℝ).measurableEmbedding
  have hleft : (∫ u in (0 : ℝ)..c, ∫ t in (0 : ℝ)..c, f (u,t)) =
      ∫ p, F p ∂volume.prod volume := by
    rw [integral_indicator hS, setIntegral_prod f hfi]
    simp only [intervalIntegral.integral_of_le hc.le, integral_Icc_eq_integral_Ioc]
  rw [hleft, ← hmp.integral_comp hemb F]
  change (∫ p, (F ∘ T) p ∂volume.prod volume) = _
  rw [integral_prod_symm _ hG]
  have hslice : ∀ w : ℝ, (∫ u : ℝ, F (T (u,w))) =
      (Icc (0 : ℝ) (2*c)).indicator
        (fun w => ∫ u in (max 0 (w-c))..(min w c), f (u,w-u)) w := by
    intro w
    by_cases hw : w ∈ Icc (0 : ℝ) (2*c)
    · rw [indicator_of_mem hw]
      have hb : max 0 (w-c) ≤ min w c := by
        rw [max_le_iff, le_min_iff, le_min_iff]
        constructor <;> constructor <;> linarith [hw.1, hw.2]
      have hp : ∀ u : ℝ, (u,w-u) ∈ S ↔ u ∈ Icc (max 0 (w-c)) (min w c) := by
        intro u
        dsimp [S]
        simp only [mem_prod, mem_Icc, max_le_iff, le_min_iff]
        constructor
        · rintro ⟨⟨h1,h2⟩,h3,h4⟩
          exact ⟨⟨h1, by linarith⟩, by linarith, h2⟩
        · rintro ⟨⟨h1,h2⟩,h3,h4⟩
          exact ⟨⟨h1,h4⟩, by linarith, by linarith⟩
      have he : (fun u : ℝ => F (T (u,w))) =
          (Icc (max 0 (w-c)) (min w c)).indicator (fun u => f (u,w-u)) := by
        funext u
        dsimp [F,T]
        simp only [indicator, hp u]
      rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hb]
    · rw [indicator_of_notMem hw]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun u => by
        apply indicator_of_notMem
        intro hu
        apply hw
        dsimp [T,S] at hu
        exact ⟨by linarith [hu.1.1,hu.2.1], by linarith [hu.1.2,hu.2.2]⟩
  change (∫ w : ℝ, ∫ u : ℝ, F (T (u,w))) = _
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith : 0 ≤ 2*c)]

namespace FEndpoint

/-- Clamp of a real number to `[lo, hi]`. -/
def n1aClampR (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem continuous_n1aClampR (lo hi : ℝ) : Continuous (n1aClampR lo hi) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem n1aClampR_mem {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : n1aClampR lo hi x ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem n1aClampR_of_mem {lo hi x : ℝ} (hx : x ∈ Icc lo hi) : n1aClampR lo hi x = x := by
  unfold n1aClampR
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Clamp of a complex number to the closed box of half-width `β` about `c`. -/
def n1aClamp (c : ℂ) (β : ℝ) (s : ℂ) : ℂ :=
  (n1aClampR (c.re - β) (c.re + β) s.re : ℂ) + (n1aClampR (c.im - β) (c.im + β) s.im : ℂ) * I

theorem continuous_n1aClamp (c : ℂ) (β : ℝ) : Continuous (n1aClamp c β) := by
  unfold n1aClamp
  exact (continuous_ofReal.comp ((continuous_n1aClampR _ _).comp continuous_re)).add
    ((continuous_ofReal.comp ((continuous_n1aClampR _ _).comp continuous_im)).mul continuous_const)

theorem n1aClamp_norm (c : ℂ) {β : ℝ} (hβ : 0 ≤ β) (s : ℂ) : ‖n1aClamp c β s - c‖ ≤ 2 * β := by
  have hre : (n1aClamp c β s - c).re = n1aClampR (c.re - β) (c.re + β) s.re - c.re := by
    simp [n1aClamp]
  have him : (n1aClamp c β s - c).im = n1aClampR (c.im - β) (c.im + β) s.im - c.im := by
    simp [n1aClamp]
  have h1 := n1aClampR_mem (show c.re - β ≤ c.re + β by linarith) s.re
  have h2 := n1aClampR_mem (show c.im - β ≤ c.im + β by linarith) s.im
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him]
  have e1 : |n1aClampR (c.re - β) (c.re + β) s.re - c.re| ≤ β :=
    abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have e2 : |n1aClampR (c.im - β) (c.im + β) s.im - c.im| ≤ β :=
    abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
  linarith

theorem n1a_abs_re_le (s c : ℂ) : |s.re - c.re| ≤ ‖s - c‖ := by
  have := abs_re_le_norm (s - c); rwa [sub_re] at this

theorem n1a_abs_im_le (s c : ℂ) : |s.im - c.im| ≤ ‖s - c‖ := by
  have := abs_im_le_norm (s - c); rwa [sub_im] at this

theorem n1aClamp_of_mem_ball {c : ℂ} {β : ℝ} {s : ℂ} (hs : s ∈ ball c β) : n1aClamp c β s = s := by
  have hn : ‖s - c‖ < β := by rw [← dist_eq_norm]; exact hs
  have h1 := abs_lt.mp (lt_of_le_of_lt (n1a_abs_re_le s c) hn)
  have h2 := abs_lt.mp (lt_of_le_of_lt (n1a_abs_im_le s c) hn)
  unfold n1aClamp
  rw [n1aClampR_of_mem ⟨by linarith [h1.1], by linarith [h1.2]⟩,
    n1aClampR_of_mem ⟨by linarith [h2.1], by linarith [h2.2]⟩]
  exact re_add_im s

theorem n1a_gamma_diff {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Gamma z := by
  refine Complex.differentiableAt_Gamma z fun m hm => ?_
  have h := congrArg Complex.re hm
  simp only [neg_re, natCast_re] at h
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  linarith

theorem n1a_gamma_cont {X : Type*} [TopologicalSpace X] {f : X → ℂ} {x : X} (hf : ContinuousAt f x)
    (h : 0 < (f x).re) : ContinuousAt (fun y => Gamma (f y)) x :=
  (n1a_gamma_diff h).continuousAt.comp hf

theorem n1a_gamma_dcomp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℂ f x) (h : 0 < (f x).re) : DifferentiableAt ℂ (fun y => Gamma (f y)) x :=
  (n1a_gamma_diff h).comp x hf

theorem n1a_ccomp {X : Type*} [TopologicalSpace X] {g : ℂ → ℂ} {f : X → ℂ} {x : X} {y : ℂ}
    (hg : ContinuousAt g y) (hf : ContinuousAt f x) (h : f x = y) :
    ContinuousAt (fun z => g (f z)) x := by
  subst h; exact hg.comp hf

theorem n1a_dcomp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℂ → ℂ} {f : E → ℂ}
    {x : E} {y : ℂ} (hg : DifferentiableAt ℂ g y) (hf : DifferentiableAt ℂ f x) (h : f x = y) :
    DifferentiableAt ℂ (fun z => g (f z)) x := by
  subst h; exact hg.comp x hf

/-- Under RH, `{Re > 0} ∖ (Σ ∖ {a})` is open (`Σ` is locally finite in `Re > 0`). -/
theorem n1a_isOpen_W (hRH : RiemannHypothesis) (a : ℂ) :
    IsOpen (halfPlane 0 \ (PoleSetQ \ {a})) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hfin⟩ := (lem_Sigma_iv_proof hRH).2 z hz.1
  have hcl : IsClosed ((U ∩ PoleSetQ) \ {z}) := (hfin.subset sdiff_subset).isClosed
  have hzn : z ∉ (U ∩ PoleSetQ) \ {z} := fun h => h.2 rfl
  filter_upwards [hU, (isOpen_halfPlane 0).mem_nhds hz.1, hcl.isOpen_compl.mem_nhds hzn] with
    w hwU hwH hwc
  refine ⟨hwH, fun hw => ?_⟩
  by_cases hwz : w = z
  · subst hwz; exact hz.2 hw
  · exact hwc ⟨⟨hwU, hw.1⟩, hwz⟩

lemma slit_add_nonneg {z : ℂ} (hz : z ∈ slitPlane) {u : ℝ} (hu : 0 ≤ u) :
    z + (u : ℂ) ∈ slitPlane := by
  rcases hz with hz | hz
  · left; simp only [add_re, ofReal_re]; linarith
  · right; simpa using hz

end FEndpoint

namespace FCauchy

theorem gamma_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gamma s := by
  refine Complex.differentiableAt_Gamma s fun m hm => ?_
  have := congrArg Complex.re hm
  simp at this
  linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

theorem conv_lt_one {X Y τ : ℝ} (hX : X < 1) (hY : Y < 1) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (1 - τ) * X + τ * Y < 1 := by
  nlinarith [mul_le_mul_of_nonneg_left (le_max_left X Y) (sub_nonneg.mpr h1),
    mul_le_mul_of_nonneg_left (le_max_right X Y) h0, max_lt hX hY]

theorem re_conv (A B : ℂ) (τ : ℝ) :
    ((1 - (τ : ℂ)) * A + (τ : ℂ) * B).re = (1 - τ) * A.re + τ * B.re := by
  simp [Complex.add_re, Complex.mul_re]

/-- The integrand of `phiD` with a complex parameter. -/
def kG (v z u : ℂ) : ℂ := Gamma (1 - u * v) * Gamma (1 - (z - u) * v)

/-- Holomorphy of `z ↦ segInt (kG v z) (p z) (q z)` where all Gamma arguments have positive real
part. -/
theorem segGamma_differentiableOn {v : ℂ} {p q : ℂ → ℂ} (hp : Differentiable ℂ p)
    (hq : Differentiable ℂ q) {W : Set ℂ} (hW : IsOpen W)
    (h1 : ∀ z ∈ W, (p z * v).re < 1) (h2 : ∀ z ∈ W, (q z * v).re < 1)
    (h3 : ∀ z ∈ W, ((z - p z) * v).re < 1) (h4 : ∀ z ∈ W, ((z - q z) * v).re < 1) :
    DifferentiableOn ℂ (fun z => segInt (kG v z) (p z) (q z)) W := by
  have hpos : ∀ z ∈ W, ∀ τ ∈ [[(0 : ℝ), 1]],
      0 < (1 - (p z + (τ : ℂ) * (q z - p z)) * v).re ∧
      0 < (1 - (z - (p z + (τ : ℂ) * (q z - p z))) * v).re := by
    intro z hz τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    have e1 : (1 - (p z + (τ : ℂ) * (q z - p z)) * v) =
        1 - ((1 - (τ : ℂ)) * (p z * v) + (τ : ℂ) * (q z * v)) := by ring
    have e2 : (1 - (z - (p z + (τ : ℂ) * (q z - p z))) * v) =
        1 - ((1 - (τ : ℂ)) * ((z - p z) * v) + (τ : ℂ) * ((z - q z) * v)) := by ring
    rw [e1, e2, sub_re, sub_re, one_re, re_conv, re_conv]
    exact ⟨by linarith [conv_lt_one (h1 z hz) (h2 z hz) hτ.1 hτ.2],
      by linarith [conv_lt_one (h3 z hz) (h4 z hz) hτ.1 hτ.2]⟩
  have hpc := hp.continuous
  have hqc := hq.continuous
  simp only [segInt, kG]
  refine (hq.sub hp).differentiableOn.mul
    (differentiableOn_intervalIntegral_of_continuousOn hW ?_ ?_)
  · rintro ⟨z, τ⟩ ⟨hz, hτ⟩
    obtain ⟨hA, hB⟩ := hpos z hz τ hτ
    refine ContinuousAt.continuousWithinAt ?_
    show ContinuousAt (fun x : ℂ × ℝ => Gamma (1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1)) * v) *
      Gamma (1 - (x.1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1))) * v)) (z, τ)
    refine ContinuousAt.mul ?_ ?_
    · exact (gamma_differentiableAt hA).continuousAt.comp
        (f := fun x : ℂ × ℝ => 1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1)) * v)
        (by fun_prop)
    · exact (gamma_differentiableAt hB).continuousAt.comp
        (f := fun x : ℂ × ℝ => 1 - (x.1 - (p x.1 + (x.2 : ℂ) * (q x.1 - p x.1))) * v)
        (by fun_prop)
  · intro τ hτ z hz
    obtain ⟨hA, hB⟩ := hpos z hz τ hτ
    have hpz := hp z
    have hqz := hq z
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ?_ ?_
    · exact (gamma_differentiableAt hA).comp z
        (f := fun z => 1 - (p z + (τ : ℂ) * (q z - p z)) * v) (by fun_prop)
    · exact (gamma_differentiableAt hB).comp z
        (f := fun z => 1 - (z - (p z + (τ : ℂ) * (q z - p z))) * v) (by fun_prop)

/-- `segInt` between real endpoints is the real interval integral. -/
theorem segInt_ofReal (g : ℂ → ℂ) (x y : ℝ) :
    segInt g x y = ∫ u in x..y, g u := by
  unfold segInt
  have := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (fun u : ℝ => g u) (y - x) x
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at this
  rw [← this, Complex.real_smul]
  push_cast
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  ring_nf

theorem phiD_eq_left (κ : ℝ) {b w : ℝ} (hw : w ∈ Icc (0 : ℝ) (1 - b)) :
    phiD κ b w = segInt (kG (slantDir κ) w) 0 w := by
  unfold phiD
  rw [max_eq_left (by linarith [hw.2]), min_eq_left hw.2,
    show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, segInt_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [kG]
  push_cast
  ring_nf

theorem phiD_eq_right (κ : ℝ) {b w : ℝ} (hw : w ∈ Icc (1 - b) (2 * (1 - b))) :
    phiD κ b w = segInt (kG (slantDir κ) w) (w - ((1 - b : ℝ) : ℂ)) ((1 - b : ℝ) : ℂ) := by
  unfold phiD
  rw [max_eq_right (by linarith [hw.1]), min_eq_right hw.1,
    show (w : ℂ) - ((1 - b : ℝ) : ℂ) = ((w - (1 - b) : ℝ) : ℂ) by push_cast; ring, segInt_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [kG]
  push_cast
  ring_nf

/-- An integral `∫_x^y h(w)/(δ - t₀ + w) dw` over an interval at distance `≥ η` from `t₀` is
holomorphic in `δ` for `|δ| < η/2`. -/
theorem piece_analytic {h : ℝ → ℂ} {x y t₀ η : ℝ} (hxy : x ≤ y)
    (hh : ContinuousOn h (Icc x y)) (hfar : ∀ w ∈ Icc x y, η ≤ |w - t₀|) :
    AnalyticOnNhd ℂ (fun δ : ℂ => ∫ w in x..y, h w / (δ - t₀ + w)) (ball 0 (η / 2)) := by
  have hden : ∀ δ ∈ ball (0 : ℂ) (η / 2), ∀ w ∈ Icc x y, δ - t₀ + w ≠ 0 := by
    intro δ hδ w hw h0
    have : δ = ((t₀ - w : ℝ) : ℂ) := by push_cast; linear_combination h0
    rw [mem_ball_zero_iff, this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hδ
    have := hfar w hw
    have : 0 ≤ |w - t₀| := abs_nonneg _
    linarith
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ball
  refine differentiableOn_intervalIntegral_of_continuousOn isOpen_ball ?_ ?_
  · rw [uIcc_of_le hxy]
    show ContinuousOn (fun p : ℂ × ℝ => h p.2 / (p.1 - t₀ + p.2)) _
    refine ContinuousOn.div (hh.comp continuousOn_snd fun p hp => hp.2) (by fun_prop) ?_
    rintro ⟨δ, w⟩ ⟨hδ, hw⟩
    exact hden δ hδ w hw
  · intro w hw
    rw [uIcc_of_le hxy] at hw
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) ?_
    intro δ hδ
    exact hden δ hδ w hw

theorem phiD_continuousOn (κ : ℝ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun w : ℝ => phiD κ b w) (Icc 0 (2 * (1 - b))) := by
  set v := slantDir κ with hv
  have hvre : v.re = 1 := by simp [hv, slantDir]
  have hcre : ∀ x : ℝ, ((x : ℂ) * v).re = x := by intro x; simp [hvre]
  have hb1 : 1 - b < 1 := by linarith [hb.1]
  have hf₁ : DifferentiableOn ℂ (fun z => segInt (kG v z) ((fun _ => (0 : ℂ)) z) ((fun z => z) z))
      {z : ℂ | (z * v).re < 1} :=
    segGamma_differentiableOn (p := fun _ => (0 : ℂ)) (q := fun z => z) (differentiable_const _)
      differentiable_id (isOpen_lt (by fun_prop) continuous_const) (fun z _ => by simp)
      (fun z hz => hz) (fun z hz => by show ((z - 0) * v).re < 1; rw [sub_zero]; exact hz)
      (fun z _ => by simp)
  have hf₂ : DifferentiableOn ℂ
      (fun z => segInt (kG v z) ((fun z => z - ((1 - b : ℝ) : ℂ)) z) ((fun _ => ((1 - b : ℝ) : ℂ)) z))
      {z : ℂ | ((z - ((1 - b : ℝ) : ℂ)) * v).re < 1} :=
    segGamma_differentiableOn (p := fun z => z - ((1 - b : ℝ) : ℂ)) (q := fun _ => ((1 - b : ℝ) : ℂ))
      (differentiable_id.sub_const _) (differentiable_const _)
      (isOpen_lt (by fun_prop) continuous_const) (fun z hz => hz)
      (fun z _ => by show (((1 - b : ℝ) : ℂ) * v).re < 1; rw [hcre]; exact hb1)
      (fun z _ => by
        show ((z - (z - ((1 - b : ℝ) : ℂ))) * v).re < 1
        rw [sub_sub_cancel, hcre]; exact hb1)
      (fun z hz => hz)
  have hL : ContinuousOn (fun w : ℝ => phiD κ b w) (Icc 0 (1 - b)) := by
    refine ContinuousOn.congr (f := fun w : ℝ => segInt (kG v w) 0 w) ?_
      (fun w hw => phiD_eq_left κ hw)
    refine hf₁.continuousOn.comp Complex.continuous_ofReal.continuousOn fun w hw => ?_
    show ((w : ℂ) * v).re < 1
    rw [hcre]; linarith [hw.2]
  have hR : ContinuousOn (fun w : ℝ => phiD κ b w) (Icc (1 - b) (2 * (1 - b))) := by
    refine ContinuousOn.congr
      (f := fun w : ℝ => segInt (kG v w) ((w : ℂ) - ((1 - b : ℝ) : ℂ)) ((1 - b : ℝ) : ℂ)) ?_
      (fun w hw => phiD_eq_right κ hw)
    refine hf₂.continuousOn.comp Complex.continuous_ofReal.continuousOn fun w hw => ?_
    show (((w : ℂ) - ((1 - b : ℝ) : ℂ)) * v).re < 1
    rw [show (w : ℂ) - ((1 - b : ℝ) : ℂ) = ((w - (1 - b) : ℝ) : ℂ) by push_cast; ring, hcre]
    linarith [hw.2]
  have := hL.union_of_isClosed hR isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc (by linarith [hb.2]) (by linarith [hb.2])] at this

end FCauchy

end GoldbachBoundaries.ThmA
