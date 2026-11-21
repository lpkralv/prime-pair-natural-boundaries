import PrimePairNB.HInf.Fill.outer_contour_tents
import PrimePairNB.HInf.Fill.norm_Pth_le
import PrimePairNB.HInf.Fill.isOpen_Uth

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma outer_pt_div {κ : ℝ} (Γ : SlantGraph κ) (h : ℝ) :
    Γ.pt h / slantDir κ = (Γ.ξ h : ℂ) + (h : ℂ) * I := by
  rw [SlantGraph.pt, mul_div_cancel_left₀ _ (slantDir_ne_zero' κ)]
lemma outer_hgt_pt {κ : ℝ} (Γ : SlantGraph κ) (h : ℝ) : hgt κ (Γ.pt h) = h := by
  simp [hgt, outer_pt_div]
lemma outer_absc_pt {κ : ℝ} (Γ : SlantGraph κ) (h : ℝ) : absc κ (Γ.pt h) = Γ.ξ h := by
  simp [absc, outer_pt_div]
lemma outer_pt_continuous {κ : ℝ} (Γ : SlantGraph κ) : Continuous Γ.pt := by
  unfold SlantGraph.pt
  exact continuous_const.mul ((Complex.continuous_ofReal.comp Γ.cont).add
    ((Complex.continuous_ofReal).mul_const I))
lemma outer_heights_closed (κ : ℝ) (x : ℂ) (q : ℝ) : IsClosed (outerHeights κ x q) := by
  dsimp [outerHeights]
  simp only [setOf_forall]
  exact isClosed_biInter fun a ha => isClosed_le continuous_const (by fun_prop)

lemma outer_sides_mem {κ : ℝ} {x : ℂ} {q e : ℝ} (hq : 0 < q) (he : 0 < e)
    (Γ : SlantGraph κ)
    (hs : ∀ h, e ≤ (Γ.pt h).re ∧ (Γ.pt h).re ≤ x.re - e)
    (hl : ∀ a ∈ PoleSetQ, a ∉ collide x → absc κ a < Γ.ξ (hgt κ a))
    (hr : ∀ b ∈ PoleSetQ, b ∉ collide x → Γ.ξ (hgt κ (x - b)) < absc κ (x - b)) :
    ∀ h ∈ outerHeights κ x q, Γ.pt h ∈ Uth κ ∧ x - Γ.pt h ∈ Uth κ := by
  intro h hh
  refine ⟨⟨by have := (hs h).1; change 0 < (Γ.pt h).re; linarith, ?_⟩,
    ⟨by have := (hs h).2; change 0 < (x - Γ.pt h).re; simp only [sub_re]; linarith, ?_⟩⟩
  · intro hm
    obtain ⟨a, ha, t, ht, hpt⟩ := mem_iUnion₂.mp hm
    have hah : hgt κ a = h := by rw [← outer_hgt_pt Γ h, hpt, hgt_sub_mul]
    have hnc : a ∉ collide x := fun hac => by
      have := hh a hac; rw [hah, sub_self, abs_zero] at this; linarith
    have ha' := hl a ha hnc
    have hab : absc κ (Γ.pt h) = absc κ a - t := by rw [hpt, absc_sub_mul]
    rw [outer_absc_pt] at hab
    rw [hah] at ha'
    linarith
  · intro hm
    obtain ⟨b, hb, t, ht, hpt⟩ := mem_iUnion₂.mp hm
    have hbh : hgt κ (x - b) = h := by
      have hi := congrArg (hgt κ) hpt
      rw [hgt_sub, outer_hgt_pt, hgt_sub_mul] at hi
      rw [hgt_sub]; linarith
    have hnc : b ∉ collide x := fun hbc => by
      have := hh (x - b) (collide_sub hbc)
      rw [hbh, sub_self, abs_zero] at this; linarith
    have hb' := hr b hb hnc
    have hab : absc κ (x - b) = Γ.ξ h - t := by
      have hi := congrArg (absc κ) hpt
      rw [absc_sub, outer_absc_pt, absc_sub_mul] at hi
      rw [absc_sub]; linarith
    rw [hbh, hab] at hb'
    linarith

lemma outer_sides_of_mem {κ : ℝ} {v : ℂ} {E : Set ℝ} (Γ : SlantGraph κ)
    (hU : ∀ h ∈ E, Γ.pt h ∈ Uth κ ∧ v - Γ.pt h ∈ Uth κ) :
    (∀ a ∈ PoleSetQ, hgt κ a ∈ E → absc κ a < Γ.ξ (hgt κ a)) ∧
    (∀ b ∈ PoleSetQ, hgt κ (v - b) ∈ E → Γ.ξ (hgt κ (v - b)) < absc κ (v - b)) := by
  constructor
  · intro a ha hh
    by_contra hn
    have hc := (hU _ hh).1.2
    apply hc
    refine mem_iUnion₂.mpr ⟨a, ha, a.re - (Γ.pt (hgt κ a)).re, ?_, ?_⟩
    · rw [pt_re, re_eq_absc κ a]
      linarith [not_lt.mp hn]
    · exact eq_sub_of_hgt_eq (by rw [outer_hgt_pt])
  · intro b hb hh
    by_contra hn
    have hc := (hU _ hh).2.2
    apply hc
    refine mem_iUnion₂.mpr ⟨b, hb, b.re - (v - Γ.pt (hgt κ (v - b))).re, ?_, ?_⟩
    · have hb_re := re_eq_absc κ (v - b)
      simp only [sub_re] at hb_re
      rw [sub_re, pt_re]
      linarith [not_lt.mp hn]
    · apply eq_sub_of_hgt_eq
      rw [hgt_sub, outer_hgt_pt, hgt_sub]
      ring

/-- Compact exterior pieces stay in the branch domain; the tails use the proved growth lemma. -/
theorem outer_contour_near (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {κ : ℝ} {x : ℂ}
    {E : Set ℝ} (hE : IsClosed E) (Γ : SlantGraph κ) {e : ℝ} (he : 0 < e)
    (hs : ∀ h, e ≤ (Γ.pt h).re ∧ (Γ.pt h).re ≤ x.re - e)
    (hc : Binf < Γ.c ∧ Γ.c < x.re - Binf)
    (hU : ∀ h ∈ E, Γ.pt h ∈ Uth κ ∧ x - Γ.pt h ∈ Uth κ) :
    ∃ r : ℝ, 0 < r ∧ ∀ v ∈ ball x r,
      (∀ h, e / 2 ≤ (Γ.pt h).re ∧ (Γ.pt h).re ≤ v.re - e / 2) ∧
      (Binf + min (Γ.c - Binf) (x.re - Binf - Γ.c) / 2 ≤ Γ.c ∧
        Binf + min (Γ.c - Binf) (x.re - Binf - Γ.c) / 2 ≤ v.re - Γ.c) ∧
      ∀ h ∈ E, Γ.pt h ∈ Uth κ ∧ v - Γ.pt h ∈ Uth κ := by
  let η := min (Γ.c - Binf) (x.re - Binf - Γ.c) / 4
  have hη : 0 < η := by dsimp [η]; exact div_pos (lt_min (by linarith [hc.1]) (by linarith [hc.2])) (by norm_num)
  obtain ⟨T, C, hP⟩ := Fill.norm_Pth_le hZ1 hZ2 hZ3 κ hη
  let H := max Γ.T 0 + |T| + |κ * Γ.c| + |x.im| + 2
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hcompact : IsCompact (Icc (-H) H ∩ E) := isCompact_Icc.inter_right hE
  have hev : ∀ᶠ v in 𝓝 x, ∀ h ∈ Icc (-H) H ∩ E, v - Γ.pt h ∈ Uth κ := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro h hh
    exact ((isOpen_Uth κ).preimage
      (continuous_fst.sub ((outer_pt_continuous Γ).comp continuous_snd))).mem_nhds (hU h hh.2).2
  have hre : ∀ᶠ v : ℂ in 𝓝 x, x.re - min (e / 2) (2 * η) < v.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      show x.re - min (e / 2) (2 * η) < x.re
      have : 0 < min (e / 2) (2 * η) := lt_min (by positivity) (by positivity)
      linarith)
  have him : ∀ᶠ v : ℂ in 𝓝 x, |v.im| < |x.im| + 1 :=
    (isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds (by show |x.im| < |x.im| + 1; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hev.and (hre.and him))
  refine ⟨r, hr, fun v hv => ?_⟩
  obtain ⟨hvE, hvr, hvi⟩ := hball v hv
  have hm1 : min (e / 2) (2 * η) ≤ e / 2 := min_le_left _ _
  have hm2 : min (e / 2) (2 * η) ≤ 2 * η := min_le_right _ _
  have hη1 : 4 * η ≤ Γ.c - Binf := by
    dsimp [η]; linarith [min_le_left (Γ.c - Binf) (x.re - Binf - Γ.c)]
  have hη2 : 4 * η ≤ x.re - Binf - Γ.c := by
    dsimp [η]; linarith [min_le_right (Γ.c - Binf) (x.re - Binf - Γ.c)]
  refine ⟨fun h => ⟨by linarith [(hs h).1], by linarith [(hs h).2]⟩, ?_, fun h hh => ⟨(hU h hh).1, ?_⟩⟩
  · constructor
    · dsimp [η] at hη1 ⊢; linarith
    · dsimp [η] at hη2 hm2 ⊢; linarith
  · by_cases hsmall : |h| ≤ H
    · exact hvE h ⟨abs_le.mp hsmall, hh⟩
    · have hbig : H < |h| := lt_of_not_ge hsmall
      have hT : Γ.T ≤ |h| := by dsimp [H] at hbig; linarith [le_max_left Γ.T 0, le_max_right Γ.T 0, abs_nonneg T, abs_nonneg (κ * Γ.c), abs_nonneg x.im]
      have hzre : (Γ.pt h).re = Γ.c := by rw [pt_re, Γ.tail h hT]; ring
      have hzim : (Γ.pt h).im = κ * Γ.c + (1 + κ ^ 2) * h := by
        simp [SlantGraph.pt, slantDir, Γ.tail h hT]
        ring
      have hab : |h| ≤ |(Γ.pt h).im| + |κ * Γ.c| := by
        have h1 : |(1 + κ ^ 2) * h| ≤ |(Γ.pt h).im| + |κ * Γ.c| := by
          rw [show (1 + κ ^ 2) * h = (Γ.pt h).im - κ * Γ.c by rw [hzim]; ring]
          exact abs_sub _ _
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + κ ^ 2)] at h1
        nlinarith [sq_nonneg κ, abs_nonneg h]
      have hvab : |(Γ.pt h).im| ≤ |v.im| + |(v - Γ.pt h).im| := by
        rw [show (Γ.pt h).im = v.im - (v - Γ.pt h).im by simp]
        exact abs_sub _ _
      apply (hP (v - Γ.pt h) ?_ ?_).1
      · simp only [sub_re, hzre]; linarith
      · dsimp [H] at hbig
        linarith [le_max_right Γ.T 0, le_abs_self T]
end GoldbachBoundaries.HInf.Fill

