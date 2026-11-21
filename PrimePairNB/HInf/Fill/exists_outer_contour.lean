import PrimePairNB.HInf.Fill.outer_contour_integral

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

/-- The outer contour, with flat collision tops, uniform exterior margins, and a holomorphic outer integral. -/
theorem exists_outer_contour (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top) {R : ℝ} (hR : 0 < R) :
    ∃ r₀ r : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧ 0 < r ∧ r < r₀ / 4 ∧
      (∀ a ∈ collide x, ∀ a' ∈ collide x, a ≠ a' → 2 * r₀ < |hgt κ a - hgt κ a'|) ∧ ball x r ⊆ VInf top ∧ ball x r \ rayW κ x ⊆ Om κ top ∧
      ∃ Γ₀ : SlantGraph κ,
        (∀ a ∈ collide x, ∀ h : ℝ, |h - hgt κ a| ≤ r₀ → Γ₀.ξ h = absc κ a) ∧
        (∀ v ∈ ball x r \ rayW κ x, ∀ Γ : SlantGraph κ,
          (∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h) →
          (∀ a ∈ collide x, IsArc r₀ ((v - x) / slantDir κ) (fun h => Γ.ξ (h + hgt κ a) - absc κ a)) →
          IsSeparating v Γ) ∧
        DifferentiableOn ℂ (fun v => ∫ h in outerHeights κ x r₀,
          pairIntegrand k κ v (Γ₀.pt h) * (slantDir κ * (((deriv Γ₀.ξ h : ℝ) : ℂ) + I))) (ball x r) := by
  obtain ⟨q, e, hq, hqR, he, hdisj, Γ₀, hc, hs, hflat, hleft, hright⟩ :=
    outer_contour_tents hZ1 hκ hx hxV.1 hR
  have hw : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr (slantDir_ne_zero' κ)
  have hw1 : 1 ≤ ‖slantDir κ‖ := by
    have := Complex.abs_re_le_norm (slantDir κ)
    simpa [slantDir] using this
  obtain ⟨u, hu, hbands⟩ := outer_contour_relevant_heights hZ1 hκ hx (show 0 < e / 4 by positivity)
  let r₀ := min q (min u (e / (16 * ‖slantDir κ‖)))
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hrq : r₀ ≤ q := min_le_left _ _
  have hru : r₀ ≤ u := (min_le_right _ _).trans (min_le_left _ _)
  have hre : r₀ ≤ e / (16 * ‖slantDir κ‖) := (min_le_right _ _).trans (min_le_right _ _)
  have hrw : 2 * r₀ * ‖slantDir κ‖ ≤ e / 8 := by
    have := (le_div_iff₀ (by positivity : 0 < 16 * ‖slantDir κ‖)).mp hre
    nlinarith
  have hbase := outer_sides_mem hr₀ he Γ₀ hs hleft hright
  have htail : Binf < Γ₀.c ∧ Γ₀.c < x.re - Binf := by rw [hc]; constructor <;> linarith [hx.2]
  obtain ⟨ρ, hρ, hnear⟩ := outer_contour_near hZ1 hZ2 hZ3
    (outer_heights_closed κ x r₀) Γ₀ he hs htail hbase
  obtain ⟨s, hspos, hsV, hsOm⟩ := exists_pinch_slit_disc hZ1 hκ hx hxV
  let r := min (ρ / 2) (min (s / 2) (min (r₀ / 8) (e / 8)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r < ρ := (min_le_left _ _).trans_lt (by linarith)
  have hrs : r < s := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hrr : r ≤ r₀ / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hre' : r ≤ e / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hVr : ball x r ⊆ VInf top := (ball_subset_ball hrs.le).trans hsV
  have hn : ∀ v ∈ ball x r, v ∈ ball x ρ := fun v hv => ball_subset_ball hrρ.le hv
  have hη : 0 < min (Γ₀.c - Binf) (x.re - Binf - Γ₀.c) / 4 :=
    div_pos (lt_min (by linarith [htail.1]) (by linarith [htail.2])) (by norm_num)
  have hnorm : ∀ v ∈ ball x r, ‖(v - x) / slantDir κ‖ < r₀ / 4 := by
    intro v hv
    have hvn : ‖v - x‖ < r := by simpa [dist_eq_norm] using hv
    rw [norm_div]
    apply (div_le_self (norm_nonneg _) hw1).trans_lt
    linarith
  refine ⟨r₀, r, hr₀, hrq.trans hqR, hr, by linarith, ?_, hVr,
    (sdiff_subset_sdiff_left (ball_subset_ball hrs.le)).trans hsOm, Γ₀, ?_, ?_, ?_⟩
  · intro a ha b hb hab; exact (by linarith : 2 * r₀ ≤ 2 * q).trans_lt (hdisj a ha b hb hab)
  · intro a ha h hh; exact hflat a ha h (hh.trans hrq)
  · intro v hv Γ heq harc
    have hnv := hnear v (hn v hv.1)
    obtain ⟨hL, hR'⟩ := outer_sides_of_mem Γ₀ hnv.2.2
    have hbs := hbands r₀ hr₀ hru v (hnorm v hv.1)
    have hvr : x.re - e / 8 < v.re := by
      have hn : ‖v - x‖ < r := by simpa [dist_eq_norm] using hv.1
      have hi := (Complex.abs_re_le_norm (v - x)).trans_lt hn
      simp only [sub_re] at hi
      linarith [(abs_lt.mp hi).1]
    have hmargin : ∀ a ∈ collide x,
        e / 4 + 2 * r₀ * ‖slantDir κ‖ ≤ a.re ∧
        a.re ≤ v.re - e / 4 - 2 * r₀ * ‖slantDir κ‖ := by
      intro a ha
      have hapt : (Γ₀.pt (hgt κ a)).re = a.re := by
        rw [pt_re, hflat a ha _ (by simp; exact hq.le), re_eq_absc κ a]
      have hsa := hs (hgt κ a)
      rw [hapt] at hsa
      constructor <;> linarith
    apply outer_contour_separating hr₀ (show 0 < e / 4 by positivity) Γ₀ Γ
      (collide_finite hZ1 hx) ?_ heq ?_ hmargin hbs.1 hbs.2 hL hR' harc
    · have hm := hnv.2.1
      have hp : 0 < min (Γ₀.c - Binf) (x.re - Binf - Γ₀.c) / 2 := by linarith [hη]
      exact ⟨htail.1, by linarith [hm.2]⟩
    · intro h hh
      have hsh := hnv.1 h
      exact ⟨by linarith [hsh.1], by linarith [hsh.2]⟩
  · apply outer_contour_integral hZ1 hZ2 hZ3 hK (show 0 < e / 2 by positivity) hη Γ₀
      (fun v hv => (hVr hv).1) (fun v hv => (hnear v (hn v hv)).1) ?_
      (fun v hv => (hnear v (hn v hv)).2.2)
    intro v hv
    have hm := (hnear v (hn v hv)).2.1
    constructor <;> linarith [hm.1, hm.2]
end GoldbachBoundaries.HInf.Fill
