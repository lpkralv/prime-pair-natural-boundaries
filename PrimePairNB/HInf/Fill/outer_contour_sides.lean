import PrimePairNB.HInf.Fill.outer_contour_radii
import PrimePairNB.HInf.Fill.graphInt_eq_outer_add_arcs

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma re_eq_absc_sub_mul_hgt (κ : ℝ) (z : ℂ) : z.re = absc κ z - κ * hgt κ z := by
  have he : ((absc κ z : ℂ) + (hgt κ z : ℂ) * I) * slantDir κ = z := by
    rw [absc, hgt, Complex.re_add_im, div_mul_cancel₀ _ (ThmA.slantDir_ne_zero κ)]
  have := congrArg Complex.re he
  simpa [slantDir, mul_comm] using this.symm

lemma graph_re_eq {κ : ℝ} (Γ : SlantGraph κ) (h : ℝ) : (Γ.pt h).re = Γ.ξ h - κ * h := by
  simp [SlantGraph.pt, slantDir]

lemma collide_sub {x a : ℂ} (ha : a ∈ collide x) : x - a ∈ collide x := by
  exact ⟨ha.2, by simpa using ha.1⟩

/-- Only finitely many poles with real part bounded below occur in a bounded
interval of slant heights. -/
lemma finite_poles_in_height_strip (κ : ℝ) {d : ℝ} (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A) :
    {b ∈ PoleSetQ | d ≤ b.re ∧ |hgt κ b| ≤ A}.Finite := by
  let K : Set ℂ := closedBall 0 (1 + |κ| + (κ ^ 2 + 1) * A) ∩ {b | d ≤ b.re}
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hK0 : K ⊆ halfPlane 0 := fun b hb => lt_of_lt_of_le hd hb.2
  apply (M6.finite_inter_poleSetQ_A hKc hK0).subset
  rintro b ⟨hb, hbd, hbh⟩
  refine ⟨⟨?_, hbd⟩, hb⟩
  rw [mem_closedBall, dist_zero_right]
  have he : ((absc κ b : ℂ) + (hgt κ b : ℂ) * I) * slantDir κ = b := by
    rw [absc, hgt, Complex.re_add_im, div_mul_cancel₀ _ (ThmA.slantDir_ne_zero κ)]
  have hi : b.im = κ * b.re + (κ ^ 2 + 1) * hgt κ b := by
    have hi := congrArg Complex.im he
    simp only [slantDir, Complex.mul_im, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.one_im, Complex.I_im] at hi
    rw [re_eq_absc_sub_mul_hgt κ b]
    nlinarith
  have hb01 := M1.poleSetQ_re_bounds hb
  have hre : |b.re| ≤ 1 := by rw [abs_of_pos hb01.1]; exact hb01.2.1
  have him : |b.im| ≤ |κ| + (κ ^ 2 + 1) * A := by
    rw [hi]
    calc |κ * b.re + (κ ^ 2 + 1) * hgt κ b|
        ≤ |κ * b.re| + |(κ ^ 2 + 1) * hgt κ b| := abs_add_le _ _
      _ ≤ |κ| + (κ ^ 2 + 1) * A := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ κ ^ 2 + 1)]
        gcongr
        nlinarith [abs_nonneg κ]
  exact (Complex.norm_le_abs_re_add_abs_im b).trans (by linarith)

/-- Around each collision height, all poles with `Re b ≥ d` except the collision
itself are excluded by one common positive band width. -/
theorem exists_collision_band_isolation (hZ1 : Z1) {κ : ℝ} (hκ : IsGenericSlope κ)
    {x : ℂ} (hx : x ∈ Xcat) {d : ℝ} (hd : 0 < d) :
    ∃ u : ℝ, 0 < u ∧ ∀ a ∈ collide x, ∀ b ∈ PoleSetQ, d ≤ b.re →
      |hgt κ b - hgt κ a| ≤ 2 * u → b = a := by
  classical
  have hfin := collide_finite hZ1 hx
  let A := 1 + ∑ a ∈ hfin.toFinset, |hgt κ a|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA' : ∀ a ∈ collide x, |hgt κ a| + 1 ≤ A := by
    intro a ha
    have := Finset.single_le_sum (f := fun a => |hgt κ a|)
      (fun a ha => abs_nonneg _) (hfin.mem_toFinset.mpr ha)
    dsimp [A]
    linarith
  let F : Set ℂ := {b ∈ PoleSetQ | d ≤ b.re ∧ |hgt κ b| ≤ A}
  have hF : F.Finite := finite_poles_in_height_strip κ hd hA
  let S : Set (ℂ × ℂ) := {p ∈ collide x ×ˢ F | p.1 ≠ p.2}
  have hS : S.Finite := (hfin.prod hF).subset (by intro p hp; exact hp.1)
  obtain ⟨δ, hδ, hδS⟩ := finite_positive_lower_bound hS
    (fun p => |hgt κ p.2 - hgt κ p.1|) (by
      rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hn⟩
      exact abs_pos.mpr (sub_ne_zero.mpr (fun he => hn
        (hgt_injOn_poles hκ ha.1 hb.1 he.symm))))
  refine ⟨min (1 / 2) (δ / 4), lt_min (by norm_num) (by positivity), ?_⟩
  intro a ha b hb hbd hba
  by_contra hn
  have hsmall : |hgt κ b - hgt κ a| ≤ 1 := by
    have := min_le_left (1 / 2 : ℝ) (δ / 4)
    linarith
  have hbF : b ∈ F := by
    refine ⟨hb, hbd, ?_⟩
    have ht := abs_add_le (hgt κ b - hgt κ a) (hgt κ a)
    simp only [sub_add_cancel] at ht
    linarith [hA' a ha]
  have hs := hδS (a, b) ⟨⟨ha, hbF⟩, Ne.symm hn⟩
  have := min_le_right (1 / 2 : ℝ) (δ / 4)
  dsimp at hs
  linarith

/-- All noncolliding poles relevant to the strip lie outside the bands, for both
the fixed left points and the moving right points. -/
theorem outer_contour_relevant_heights (hZ1 : Z1) {κ : ℝ} (hκ : IsGenericSlope κ)
    {x : ℂ} (hx : x ∈ Xcat) {d : ℝ} (hd : 0 < d) :
    ∃ u : ℝ, 0 < u ∧ ∀ r₀ : ℝ, 0 < r₀ → r₀ ≤ u → ∀ v : ℂ,
      ‖(v - x) / slantDir κ‖ < r₀ / 4 →
      (∀ a ∈ PoleSetQ, d ≤ a.re → a ∉ collide x → hgt κ a ∈ outerHeights κ x r₀) ∧
      (∀ b ∈ PoleSetQ, d ≤ b.re → b ∉ collide x → hgt κ (v - b) ∈ outerHeights κ x r₀) := by
  obtain ⟨u, hu, hiso⟩ := exists_collision_band_isolation hZ1 hκ hx hd
  refine ⟨u, hu, fun r₀ hr₀ hru v hv => ⟨?_, ?_⟩⟩
  · intro b hb hbd hbc a ha
    by_contra hh
    have hh' : |hgt κ b - hgt κ a| ≤ 2 * u := by
      have : |hgt κ b - hgt κ a| < r₀ := lt_of_not_ge hh
      linarith
    exact hbc ((hiso a ha b hb hbd hh') ▸ ha)
  · intro b hb hbd hbc a ha
    by_contra hh
    have hh' : |hgt κ (v - b) - hgt κ a| < r₀ := lt_of_not_ge hh
    have hi := (Complex.abs_im_le_norm ((v - x) / slantDir κ)).trans_lt hv
    have he : hgt κ b - hgt κ (x - a) =
        ((v - x) / slantDir κ).im - (hgt κ (v - b) - hgt κ a) := by
      simp only [hgt, sub_div, Complex.sub_im]
      ring
    have hs : |hgt κ b - hgt κ (x - a)| ≤ 2 * u := by
      rw [he]
      have := abs_sub ((v - x) / slantDir κ).im (hgt κ (v - b) - hgt κ a)
      linarith
    have heq := hiso (x - a) (collide_sub ha) b hb hbd hs
    exact hbc (heq ▸ collide_sub ha)

/-- Left-side constraints transfer from the outer graph; poles with small real part
are handled by the strip margin, and collision points by `IsArc.west_of`. -/
theorem outer_contour_left {κ : ℝ} {x : ℂ} {r₀ : ℝ} {ε : ℂ}
    (Γ₀ Γ : SlantGraph κ) {d : ℝ}
    (hstrip : ∀ h, d ≤ (Γ.pt h).re)
    (hband : ∀ a ∈ PoleSetQ, d ≤ a.re → a ∉ collide x → hgt κ a ∈ outerHeights κ x r₀)
    (hleft : ∀ a ∈ PoleSetQ, hgt κ a ∈ outerHeights κ x r₀ → absc κ a < Γ₀.ξ (hgt κ a))
    (heq : ∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h)
    (harc : ∀ a ∈ collide x, IsArc r₀ ε (fun h => Γ.ξ (h + hgt κ a) - absc κ a)) :
    ∀ a ∈ PoleSetQ, absc κ a < Γ.ξ (hgt κ a) := by
  intro a ha
  by_cases hc : a ∈ collide x
  · have hw := (harc a hc).west_of
    simpa using hw
  · by_cases hd : d ≤ a.re
    · rw [heq _ (hband a ha hd hc)]
      exact hleft a ha (hband a ha hd hc)
    · have hs := hstrip (hgt κ a)
      rw [graph_re_eq] at hs
      rw [re_eq_absc_sub_mul_hgt κ a] at hd
      linarith

/-- Right-side constraints transfer in the same way. The colliding right point is
`a + (v-x)`, so its height and abscissa shift by `Im ε` and `Re ε`. -/
theorem outer_contour_right {κ : ℝ} {x v : ℂ} {r₀ : ℝ}
    (Γ₀ Γ : SlantGraph κ) {d : ℝ}
    (hstrip : ∀ h, (Γ.pt h).re ≤ v.re - d)
    (hband : ∀ b ∈ PoleSetQ, d ≤ b.re → b ∉ collide x → hgt κ (v - b) ∈ outerHeights κ x r₀)
    (hright : ∀ b ∈ PoleSetQ, hgt κ (v - b) ∈ outerHeights κ x r₀ →
      Γ₀.ξ (hgt κ (v - b)) < absc κ (v - b))
    (heq : ∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h)
    (harc : ∀ a ∈ collide x, IsArc r₀ ((v - x) / slantDir κ)
      (fun h => Γ.ξ (h + hgt κ a) - absc κ a)) :
    ∀ b ∈ PoleSetQ, Γ.ξ (hgt κ (v - b)) < absc κ (v - b) := by
  intro b hb
  by_cases hc : b ∈ collide x
  · have ha := collide_sub hc
    have hw := (harc (x - b) ha).east_of
    have hh : ((v - x) / slantDir κ).im + hgt κ (x - b) = hgt κ (v - b) := by
      simp only [hgt, ← Complex.add_im, ← add_div]
      congr 2
      ring
    have hr : ((v - x) / slantDir κ).re + absc κ (x - b) = absc κ (v - b) := by
      simp only [absc, ← Complex.add_re, ← add_div]
      congr 2
      ring
    rw [hh] at hw
    linarith
  · by_cases hd : d ≤ b.re
    · rw [heq _ (hband b hb hd hc)]
      exact hright b hb (hband b hb hd hc)
    · have hs := hstrip (hgt κ (v - b))
      have hre := re_eq_absc_sub_mul_hgt κ (v - b)
      rw [graph_re_eq] at hs
      simp only [Complex.sub_re] at hre
      linarith

/-- The strip margin of every glued graph follows from the outer strip margin
and the size bound of the arcs at the finitely many collision points. -/
theorem outer_contour_strip {κ : ℝ} {x v ε : ℂ} {r₀ d : ℝ} (hr₀ : 0 < r₀)
    (Γ₀ Γ : SlantGraph κ)
    (heq : ∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h)
    (houter : ∀ h ∈ outerHeights κ x r₀,
      d ≤ (Γ₀.pt h).re ∧ (Γ₀.pt h).re ≤ v.re - d)
    (hmargin : ∀ a ∈ collide x,
      d + 2 * r₀ * ‖slantDir κ‖ ≤ a.re ∧ a.re ≤ v.re - d - 2 * r₀ * ‖slantDir κ‖)
    (harc : ∀ a ∈ collide x, IsArc r₀ ε (fun h => Γ.ξ (h + hgt κ a) - absc κ a)) :
    ∀ h : ℝ, d ≤ (Γ.pt h).re ∧ (Γ.pt h).re ≤ v.re - d := by
  intro h
  by_cases hh : h ∈ outerHeights κ x r₀
  · have hp : Γ.pt h = Γ₀.pt h := by simp only [SlantGraph.pt, heq h hh]
    rw [hp]
    exact houter h hh
  · obtain ⟨a, ha, hha⟩ : ∃ a ∈ collide x, |h - hgt κ a| < r₀ := by
      change ¬ (∀ a ∈ collide x, r₀ ≤ |h - hgt κ a|) at hh
      push_neg at hh
      exact hh
    have ht : h - hgt κ a ∈ Icc (-r₀) r₀ :=
      ⟨(abs_lt.mp hha).1.le, (abs_lt.mp hha).2.le⟩
    have hs := (harc a ha).small (h - hgt κ a) ht
    have hp := graph_arc_point Γ a (h - hgt κ a)
    simp only [sub_add_cancel] at hp hs
    have hn : ‖Γ.pt h - a‖ < 2 * r₀ * ‖slantDir κ‖ := by
      rw [← hp, add_sub_cancel_left, norm_mul]
      have hw : 0 < ‖slantDir κ‖ := norm_pos_iff.mpr (ThmA.slantDir_ne_zero κ)
      nlinarith
    have hre := Complex.abs_re_le_norm (Γ.pt h - a)
    simp only [Complex.sub_re] at hre
    have hb := abs_le.mp hre
    have hm := hmargin a ha
    constructor <;> linarith

/-- Agreement outside finitely many bounded bands forces the same tail line. -/
lemma outer_graph_tail_eq {κ : ℝ} {x : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hfin : (collide x).Finite) (Γ₀ Γ : SlantGraph κ)
    (heq : ∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h) : Γ.c = Γ₀.c := by
  classical
  let h := max (max Γ₀.T Γ.T) (r₀ + 1 + ∑ a ∈ hfin.toFinset, |hgt κ a|)
  have hh : r₀ + 1 + ∑ a ∈ hfin.toFinset, |hgt κ a| ≤ h := le_max_right _ _
  have hh0 : 0 ≤ h := by
    have hn : 0 ≤ ∑ a ∈ hfin.toFinset, |hgt κ a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have ho : h ∈ outerHeights κ x r₀ := by
    intro a ha
    have hs : |hgt κ a| ≤ ∑ b ∈ hfin.toFinset, |hgt κ b| :=
      Finset.single_le_sum (f := fun b => |hgt κ b|) (fun _ _ => abs_nonneg _)
        (hfin.mem_toFinset.mpr ha)
    have ht := le_abs_self (h - hgt κ a)
    linarith [le_abs_self (hgt κ a)]
  have h₀ : Γ₀.T ≤ |h| := by
    rw [abs_of_nonneg hh0]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have h₁ : Γ.T ≤ |h| := by
    rw [abs_of_nonneg hh0]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have he := heq h ho
  rw [Γ.tail h h₁, Γ₀.tail h h₀] at he
  linarith

/-- Assembly of the universal separating-graph clause of `exists_outer_contour`,
from explicit outer constraints, collision margins, and the isolated-band property. -/
theorem outer_contour_separating {κ : ℝ} {x v : ℂ} {r₀ d : ℝ} (hr₀ : 0 < r₀) (hd : 0 < d)
    (Γ₀ Γ : SlantGraph κ) (hfin : (collide x).Finite)
    (htail : Binf < Γ₀.c ∧ Γ₀.c < v.re - Binf)
    (heq : ∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h)
    (houter : ∀ h ∈ outerHeights κ x r₀,
      d ≤ (Γ₀.pt h).re ∧ (Γ₀.pt h).re ≤ v.re - d)
    (hmargin : ∀ a ∈ collide x,
      d + 2 * r₀ * ‖slantDir κ‖ ≤ a.re ∧ a.re ≤ v.re - d - 2 * r₀ * ‖slantDir κ‖)
    (hbandL : ∀ a ∈ PoleSetQ, d ≤ a.re → a ∉ collide x → hgt κ a ∈ outerHeights κ x r₀)
    (hbandR : ∀ b ∈ PoleSetQ, d ≤ b.re → b ∉ collide x → hgt κ (v - b) ∈ outerHeights κ x r₀)
    (hleft : ∀ a ∈ PoleSetQ, hgt κ a ∈ outerHeights κ x r₀ → absc κ a < Γ₀.ξ (hgt κ a))
    (hright : ∀ b ∈ PoleSetQ, hgt κ (v - b) ∈ outerHeights κ x r₀ →
      Γ₀.ξ (hgt κ (v - b)) < absc κ (v - b))
    (harc : ∀ a ∈ collide x, IsArc r₀ ((v - x) / slantDir κ)
      (fun h => Γ.ξ (h + hgt κ a) - absc κ a)) : IsSeparating v Γ := by
  have hs := outer_contour_strip hr₀ Γ₀ Γ heq houter hmargin harc
  refine ⟨⟨d, hd, hs⟩, ?_, ?_, ?_⟩
  · simpa only [outer_graph_tail_eq hr₀ hfin Γ₀ Γ heq] using htail
  · exact outer_contour_left Γ₀ Γ (fun h => (hs h).1) hbandL hleft heq harc
  · exact outer_contour_right Γ₀ Γ (fun h => (hs h).2) hbandR hright heq harc

end GoldbachBoundaries.HInf.Fill


