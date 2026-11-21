import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-! Radius and band choices for the outer contour. No contour existence statement is used here. -/
noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma collide_finite (hZ1 : Z1) {x : ℂ} (hx : x ∈ Xcat) : (collide x).Finite := by
  have he : collide x = Prod.fst '' pinchPairs x := by
    ext a
    constructor
    · intro ha
      exact ⟨(a, x - a), ⟨ha.1, ha.2, by simp⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩
      exact ⟨ha, by rw [← hab]; simpa using hb⟩
  rw [he]
  exact (M1.pinchPairs_finite hZ1 hx.2).image _

lemma hgt_injOn_poles {κ : ℝ} (hκ : IsGenericSlope κ) : Set.InjOn (hgt κ) PoleSetQ := by
  intro a ha b hb he
  by_contra hn
  apply hκ.1 a ha b hb hn (absc κ a - absc κ b)
  have hw := ThmA.slantDir_ne_zero κ
  have hd : (a - b) / slantDir κ = ((absc κ a - absc κ b : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [absc, sub_div]
    · simpa [hgt, sub_div] using sub_eq_zero.mpr he
  exact (div_eq_iff hw).mp hd

lemma finite_positive_lower_bound {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d < f i := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha hs ih =>
    obtain ⟨d, hd, hds⟩ := ih (fun i hi => hf i (mem_insert_of_mem _ hi))
    refine ⟨min d (f a / 2), lt_min hd (by have := hf a (mem_insert _ _); positivity), ?_⟩
    intro i hi
    rcases mem_insert_iff.mp hi with rfl | hi
    · have := hf i (mem_insert _ _)
      exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (hds i hi)

/-- A generic pinch has a disc meeting no cut other than its own. -/
lemma exists_pinch_slit_disc (hZ1 : Z1) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ}
    (hx : x ∈ Xcat) {top : EReal} (hxV : x ∈ Vt top) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ VInf top ∧ ball x ρ \ rayW κ x ⊆ Om κ top := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp (isOpen_VInf top) x ⟨hxV, hx.2⟩
  let K : Set ℂ := closedBall x (r / 2)
  have hKV : K ⊆ VInf top := fun z hz => hrV
    (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  let K' : Set ℂ := (fun p : ℂ × ℝ => p.1 + (p.2 : ℂ) * slantDir κ) '' (K ×ˢ Icc (0 : ℝ) 1)
  have hK'c : IsCompact K' := (isCompact_closedBall x (r / 2) |>.prod isCompact_Icc).image (by fun_prop)
  have hK'2 : K' ⊆ halfPlane (2 * Binf) := by
    rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    have hz2 := (hKV hz).2
    change 2 * Binf < (z + (t : ℂ) * slantDir κ).re
    simp [slantDir]
    linarith [ht.1]
  have hF := finite_inter_pinch hZ1 hK'c hK'2
  let C : Set ℂ := ⋃ y ∈ (K' ∩ Pinch) \ {x}, rayW κ y
  have hCc : IsClosed C := (hF.subset sdiff_subset).isClosed_biUnion fun y _ => isClosed_rayW κ y
  have hxC : x ∉ C := by
    intro hm
    obtain ⟨y, hy, t, ht, he⟩ := mem_iUnion₂.mp hm
    exact hκ.2 y hy.1.2 x hx.1 hy.2 t (by linear_combination -he)
  obtain ⟨s, hs, hsC⟩ := Metric.isOpen_iff.mp hCc.isOpen_compl x hxC
  refine ⟨min s (r / 2), lt_min hs (by positivity), ?_, ?_⟩
  · exact fun z hz => hKV (ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hz))
  · rintro z ⟨hz, hzx⟩
    have hzK : z ∈ K := ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hz)
    refine ⟨hKV hzK, ?_⟩
    intro hcut
    obtain ⟨y, hy, t, ht, he⟩ := mem_iUnion₂.mp hcut
    by_cases hxy : y = x
    · exact hzx (hxy ▸ ⟨t, ht, he⟩)
    · apply hsC (ball_subset_ball (min_le_left _ _) hz)
      refine mem_iUnion₂.mpr ⟨y, ⟨⟨?_, hy⟩, hxy⟩, t, ht, he⟩
      have hy2 := re_le_two_of_mem_pinch hy
      have hz1 := (hKV hzK).1.1
      have hre : z.re = y.re - t := by rw [he]; simp [slantDir]
      exact ⟨(z, t), ⟨hzK, ht, by linarith⟩, by simp only; rw [he]; ring⟩

end GoldbachBoundaries.HInf.Fill

