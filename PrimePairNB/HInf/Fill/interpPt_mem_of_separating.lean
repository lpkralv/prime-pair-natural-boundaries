import PrimePairNB.HInf.Fill.absc_lt_iff_re_lt

/-! Proof of `interpPt_mem_of_separating`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma interpPt_div {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (l h : ℝ) :
    interpPt Γ₀ Γ₁ l h / slantDir κ = (((1 - l) * Γ₀.ξ h + l * Γ₁.ξ h : ℝ) : ℂ) + (h : ℂ) * I := by
  rw [interpPt, mul_div_cancel_left₀ _ (slantDir_ne_zero' κ)]

lemma hgt_interpPt {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (l h : ℝ) : hgt κ (interpPt Γ₀ Γ₁ l h) = h := by
  rw [hgt, interpPt_div]
  simp

lemma absc_interpPt {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (l h : ℝ) :
    absc κ (interpPt Γ₀ Γ₁ l h) = (1 - l) * Γ₀.ξ h + l * Γ₁.ξ h := by
  rw [absc, interpPt_div]
  simp

/-- For a whole interpolation of two separating graphs (the conditions are convex in `ξ`): every interpolated point `z` has `z ∈ U_θ`, `v - z ∈ U_θ`, and real part in a
fixed compact subset of `(0, Re v)`. With `Γ₀ = Γ₁` this says that a separating graph itself stays in that set. -/
theorem interpPt_mem_of_separating {κ : ℝ} {v : ℂ} {Γ₀ Γ₁ : SlantGraph κ} (h₀ : IsSeparating v Γ₀)
    (h₁ : IsSeparating v Γ₁) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      interpPt Γ₀ Γ₁ l h ∈ Uth κ ∧ v - interpPt Γ₀ Γ₁ l h ∈ Uth κ ∧
        ε₁ ≤ (interpPt Γ₀ Γ₁ l h).re ∧ (interpPt Γ₀ Γ₁ l h).re ≤ v.re - ε₁ := by
  obtain ⟨e₀, he₀, hr₀⟩ := h₀.re_mem
  obtain ⟨e₁, he₁, hr₁⟩ := h₁.re_mem
  refine ⟨min e₀ e₁, lt_min he₀ he₁, fun l hl h => ?_⟩
  set z := interpPt Γ₀ Γ₁ l h with hz
  have hl0 : 0 ≤ l := hl.1
  have hl1 : 0 ≤ 1 - l := by linarith [hl.2]
  have hzh : hgt κ z = h := hgt_interpPt Γ₀ Γ₁ l h
  have hza : absc κ z = (1 - l) * Γ₀.ξ h + l * Γ₁.ξ h := absc_interpPt Γ₀ Γ₁ l h
  have hzr : z.re = (1 - l) * (Γ₀.pt h).re + l * (Γ₁.pt h).re := by
    rw [re_eq_absc κ z, hzh, hza, pt_re, pt_re]
    ring
  have hm0 : min e₀ e₁ ≤ e₀ := min_le_left _ _
  have hm1 : min e₀ e₁ ≤ e₁ := min_le_right _ _
  obtain ⟨a0, a1⟩ := hr₀ h
  obtain ⟨b0, b1⟩ := hr₁ h
  have lo : min e₀ e₁ ≤ z.re := by
    rw [hzr]
    nlinarith [mul_nonneg hl1 (sub_nonneg.mpr (hm0.trans a0)), mul_nonneg hl0 (sub_nonneg.mpr (hm1.trans b0))]
  have hi : z.re ≤ v.re - min e₀ e₁ := by
    rw [hzr]
    nlinarith [mul_nonneg hl1 (sub_nonneg.mpr (a1.trans (by linarith : v.re - e₀ ≤ v.re - min e₀ e₁))),
      mul_nonneg hl0 (sub_nonneg.mpr (b1.trans (by linarith : v.re - e₁ ≤ v.re - min e₀ e₁)))]
  have hpos : 0 < min e₀ e₁ := lt_min he₀ he₁
  -- a convex combination of two numbers above `A` is above `A`
  have conv_gt : ∀ A : ℝ, A < Γ₀.ξ h → A < Γ₁.ξ h → A < (1 - l) * Γ₀.ξ h + l * Γ₁.ξ h := by
    intro A hA0 hA1
    rcases hl0.eq_or_lt with rfl | hlp
    · simpa using hA0
    · have := mul_pos hlp (sub_pos.mpr hA1)
      nlinarith [mul_nonneg hl1 (sub_pos.mpr hA0).le]
  have conv_lt : ∀ A : ℝ, Γ₀.ξ h < A → Γ₁.ξ h < A → (1 - l) * Γ₀.ξ h + l * Γ₁.ξ h < A := by
    intro A hA0 hA1
    rcases hl0.eq_or_lt with rfl | hlp
    · simpa using hA0
    · have := mul_pos hlp (sub_pos.mpr hA1)
      nlinarith [mul_nonneg hl1 (sub_pos.mpr hA0).le]
  refine ⟨⟨?_, fun hm => ?_⟩, ⟨?_, fun hm => ?_⟩, lo, hi⟩
  · show 0 < z.re
    linarith
  · obtain ⟨a, ha, t, ht, he⟩ := mem_iUnion₂.mp hm
    have e1 : hgt κ a = h := by rw [← hzh, he, hgt_sub_mul]
    have e2 : absc κ z = absc κ a - t := by rw [he, absc_sub_mul]
    have c0 := h₀.left a ha
    have c1 := h₁.left a ha
    rw [e1] at c0 c1
    have := conv_gt _ c0 c1
    rw [← hza, e2] at this
    linarith
  · show 0 < (v - z).re
    rw [sub_re]
    linarith
  · obtain ⟨b, hb, t, ht, he⟩ := mem_iUnion₂.mp hm
    have e1 : hgt κ (v - b) = h := by
      have := congrArg (hgt κ) he
      rw [hgt_sub, hgt_sub_mul, hzh] at this
      rw [hgt_sub]
      linarith
    have e2 : absc κ (v - b) = absc κ z - t := by
      have := congrArg (absc κ) he
      rw [absc_sub, absc_sub_mul] at this
      rw [absc_sub]
      linarith
    have c0 := h₀.right b hb
    have c1 := h₁.right b hb
    rw [e1] at c0 c1
    have := conv_lt _ c0 c1
    rw [← hza, e2] at this
    linarith

end GoldbachBoundaries.HInf.Fill

