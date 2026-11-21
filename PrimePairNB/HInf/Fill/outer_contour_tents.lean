import PrimePairNB.HInf.Fill.outer_contour_sides
import PrimePairNB.HInf.Fill.exists_separating_iff
import PrimePairNB.HInf.Fill.exists_trapezoid_graph

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma outer_order {κ : ℝ} (hκ : IsGenericSlope κ) {x a b : ℂ}
    (hx : x ∈ Xcat) (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ)
    (hh : hgt κ a = hgt κ (x - b)) : a + b = x := by
  have he : a + b = x - ((x.re - (a + b).re : ℝ) : ℂ) * slantDir κ := by
    apply eq_sub_of_hgt_eq
    simp only [hgt, add_div, sub_div, Complex.add_im, Complex.sub_im] at hh ⊢
    linarith
  by_contra hn
  apply hκ.2 x hx.1 (a + b) ⟨a, ha, b, hb, rfl⟩ (Ne.symm hn)
    (x.re - (a + b).re)
  linear_combination -he

lemma outer_tip {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat)
    {e : ℝ} (he : 0 < e) (he1 : e < x.re - 1) (he2 : 2 * e < x.re) (i : ℝ) :
    ∃ t : ℝ, e < t ∧ t < x.re - e ∧
      (∀ a ∈ PoleSetQ, hgt κ a = i → a.re ≤ t ∧ (a ∉ collide x → a.re < t)) ∧
      (∀ b ∈ PoleSetQ, hgt κ (x - b) = i → t ≤ x.re - b.re ∧ (b ∉ collide x → t < x.re - b.re)) ∧
      (∀ a ∈ collide x, hgt κ a = i → t = a.re) := by
  classical
  by_cases hc : ∃ a ∈ collide x, hgt κ a = i
  · obtain ⟨a, ha, hai⟩ := hc
    have hb := M1.poleSetQ_re_bounds ha.2
    have hax : x.re - a.re ≤ 1 := by simpa using hb.2.1
    refine ⟨a.re, by linarith, by linarith [(M1.poleSetQ_re_bounds ha.1).2.1], ?_, ?_, ?_⟩
    · intro p hp hpi
      have hp : p = a := hgt_injOn_poles hκ hp ha.1 (hpi.trans hai.symm)
      subst p
      exact ⟨le_rfl, fun hn => (hn ha).elim⟩
    · intro b hb hbi
      have hab := outer_order hκ hx ha.1 hb (hai.trans hbi.symm)
      have hbe : b = x - a := by linear_combination hab
      subst b
      exact ⟨by simp, fun hn => (hn (collide_sub ha)).elim⟩
    · intro p hp hpi
      have hp : p = a := hgt_injOn_poles hκ hp.1 ha.1 (hpi.trans hai.symm)
      simp [hp]
  · have hno : ∀ a ∈ PoleSetQ, ∀ b ∈ PoleSetQ,
        hgt κ a = i → hgt κ (x - b) = i → a.re < x.re - b.re := by
      intro a ha b hb hai hbi
      have hab := outer_order hκ hx ha hb (hai.trans hbi.symm)
      have hae : x - a = b := by linear_combination -hab
      exact (hc ⟨a, ⟨ha, hae ▸ hb⟩, hai⟩).elim
    let A := {a | a ∈ PoleSetQ ∧ e ≤ a.re ∧ hgt κ a = i}
    let B := {b | b ∈ PoleSetQ ∧ e ≤ b.re ∧ hgt κ (x - b) = i}
    have hAf : A.Finite := (finite_poleSetQ_height κ he |i|).subset fun a ha =>
      ⟨ha.1, ha.2.1, by rw [ha.2.2]⟩
    have hBf : B.Finite := (finite_poleSetQ_height κ he (|i| + |hgt κ x|)).subset fun b hb => by
      refine ⟨hb.1, hb.2.1, ?_⟩
      have h : hgt κ b = hgt κ x - i := by
        have := hb.2.2; rw [hgt_sub] at this; linarith
      rw [h]
      exact (abs_sub _ _).trans (by rw [add_comm])
    obtain ⟨t, htA, htB⟩ := exists_between_finite (A := insert e (re '' A))
      (B := insert (x.re - e) ((fun b => x.re - b.re) '' B))
      ((hAf.image _).insert _) ((hBf.image _).insert _) (insert_nonempty _ _) (insert_nonempty _ _) (by
        rintro u (rfl | ⟨a, ha, rfl⟩) v (rfl | ⟨b, hb, rfl⟩)
        · linarith
        · linarith [(M1.poleSetQ_re_bounds hb.1).2.1]
        · linarith [(M1.poleSetQ_re_bounds ha.1).2.1]
        · exact hno a ha.1 b hb.1 ha.2.2 hb.2.2)
    have ht1 := htA e (mem_insert _ _)
    have ht2 := htB (x.re - e) (mem_insert _ _)
    refine ⟨t, ht1, ht2, ?_, ?_, fun a ha hai => (hc ⟨a, ha, hai⟩).elim⟩
    · intro a ha hai
      have hlt : a.re < t := by
        by_cases hd : e ≤ a.re
        · exact htA _ (mem_insert_of_mem _ ⟨a, ⟨ha, hd, hai⟩, rfl⟩)
        · linarith
      exact ⟨hlt.le, fun _ => hlt⟩
    · intro b hb hbi
      have hlt : t < x.re - b.re := by
        by_cases hd : e ≤ b.re
        · exact htB _ (mem_insert_of_mem _ ⟨b, ⟨hb, hd, hbi⟩, rfl⟩)
        · linarith
      exact ⟨hlt.le, fun _ => hlt⟩

/-- Tents with flat collision tops and strict sides at every other pole. -/
theorem outer_contour_tents (hZ1 : Z1) {κ : ℝ} (hκ : IsGenericSlope κ)
    {x : ℂ} (hx : x ∈ Xcat) (hx1 : 1 < x.re) {R : ℝ} (hR : 0 < R) :
    ∃ r₀ e : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧ 0 < e ∧
      (∀ a ∈ collide x, ∀ b ∈ collide x, a ≠ b → 2 * r₀ < |hgt κ a - hgt κ b|) ∧
      ∃ Γ : SlantGraph κ, Γ.c = x.re / 2 ∧
        (∀ h, e ≤ (Γ.pt h).re ∧ (Γ.pt h).re ≤ x.re - e) ∧
        (∀ a ∈ collide x, ∀ h, |h - hgt κ a| ≤ r₀ → Γ.ξ h = absc κ a) ∧
        (∀ a ∈ PoleSetQ, a ∉ collide x → absc κ a < Γ.ξ (hgt κ a)) ∧
        (∀ b ∈ PoleSetQ, b ∉ collide x → Γ.ξ (hgt κ (x - b)) < absc κ (x - b)) := by
  classical
  let c := x.re / 2
  let e := (x.re - 1) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have he1 : e < x.re - 1 := by dsimp [e]; linarith
  have he2 : 2 * e < x.re := by dsimp [e]; linarith
  have hce : c - e = 1 / 2 := by dsimp [c, e]; ring
  let η := (c - Binf) / 2
  have hcB : Binf < c := by dsimp [c]; linarith [hx.2]
  have hη : 0 < η := by dsimp [η]; linarith
  have hF := (M1.Fdelta_spec hZ1 η hη).1
  let C := collide x
  have hC : C.Finite := collide_finite hZ1 hx
  let H := (hgt κ '' Fdelta η ∪ (fun b => hgt κ (x - b)) '' Fdelta η) ∪ hgt κ '' C
  have hH : H.Finite := ((hF.image _).union (hF.image _)).union (hC.image _)
  let S := hH.toFinset
  have hSmem : ∀ i, i ∈ S ↔ i ∈ H := fun _ => hH.mem_toFinset
  let Hm := ∑ i ∈ S, |i|
  have hHm : ∀ i ∈ S, |i| ≤ Hm := fun i hi =>
    Finset.single_le_sum (f := fun j => |j|) (fun _ _ => abs_nonneg _) hi
  let A := {a | a ∈ PoleSetQ ∧ e ≤ a.re ∧ |hgt κ a| ≤ Hm + 1}
  let B := {b | b ∈ PoleSetQ ∧ e ≤ b.re ∧ |hgt κ (x - b)| ≤ Hm + 1}
  have hA : A.Finite := finite_poleSetQ_height κ he _
  have hB : B.Finite := (finite_poleSetQ_height κ he (Hm + 1 + |hgt κ x|)).subset fun b hb => by
    refine ⟨hb.1, hb.2.1, ?_⟩
    have h : hgt κ b = hgt κ x - hgt κ (x - b) := by rw [hgt_sub]; ring
    rw [h]
    exact (abs_sub _ _).trans (by linarith [hb.2.2])
  have hG : (H ∪ hgt κ '' A ∪ (fun b => hgt κ (x - b)) '' B).Finite :=
    (hH.union (hA.image _)).union (hB.image _)
  let G := hG.toFinset
  have hGmem : ∀ i, i ∈ G ↔ i ∈ H ∪ hgt κ '' A ∪ (fun b => hgt κ (x - b)) '' B :=
    fun _ => hG.mem_toFinset
  have hSG : ∀ i ∈ S, i ∈ G := fun i hi => (hGmem i).2 (Or.inl (Or.inl ((hSmem i).1 hi)))
  obtain ⟨w, hw, hgap⟩ := exists_gap G
  choose t ht1 ht2 ht3 ht4 ht5 using outer_tip hκ hx he he1 he2
  obtain ⟨m, hm, hmt⟩ := exists_pos_le_finset S
    (fun i => min (t i - e) (x.re - e - t i))
    (fun i _ => lt_min (by linarith [ht1 i]) (by linarith [ht2 i]))
  let q := min (min R (w / 4)) (min (1 / 4) (m / (8 * (|κ| + 1))))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqR : q ≤ R := (min_le_left _ _).trans (min_le_left _ _)
  have hqw : q ≤ w / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hq1 : q ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hqm : q ≤ m / (8 * (|κ| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hkq : |κ| * (2 * q) ≤ m / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * (|κ| + 1))).mp hqm
    nlinarith [abs_nonneg κ]
  obtain ⟨Γ, hΓc, hline, hplat, hramp⟩ := exists_trapezoid_graph κ c S id (fun _ => q)
    (fun i => t i + κ * i) hq (fun _ _ => hq.le) (fun i hi j hj hij => by
      have := hgap i (hSG i hi) j (hSG j hj) hij
      simpa only [id] using (by linarith : q + q + 2 * q < |i - j|))
  simp only [id] at hline hplat hramp
  have hstrip : ∀ h, e ≤ Γ.ξ h - κ * h ∧ Γ.ξ h - κ * h ≤ x.re - e := by
    intro h
    by_cases hh : ∀ i ∈ S, q + q ≤ |h - i|
    · rw [hline h hh]
      constructor <;> dsimp [c, e] <;> linarith
    · push_neg at hh
      obtain ⟨i, hi, hhi⟩ := hh
      obtain ⟨l, ⟨hl0, hl1⟩, hΓ⟩ := hramp i hi h hhi
      have hab : |κ * (i - h)| ≤ m / 2 := by
        rw [abs_mul, abs_sub_comm i h]
        exact (mul_le_mul_of_nonneg_left hhi.le (abs_nonneg _)).trans (by linarith [hkq])
      obtain ⟨ha1, ha2⟩ := abs_le.mp hab
      have hmi := hmt i hi
      have hm1 := hmi.trans (min_le_left _ _)
      have hm2 := hmi.trans (min_le_right _ _)
      have heq : Γ.ξ h - κ * h = (1 - l) * c + l * (t i + κ * (i - h)) := by rw [hΓ]; ring
      rw [heq]
      constructor
      · nlinarith [mul_nonneg (show 0 ≤ 1 - l by linarith) (show 0 ≤ c - e by linarith),
          mul_nonneg hl0 (show 0 ≤ t i + κ * (i - h) - e by linarith)]
      · have hxc : x.re - c = c := by dsimp [c]; ring
        nlinarith [mul_nonneg (show 0 ≤ 1 - l by linarith) (show 0 ≤ x.re - e - c by linarith),
          mul_nonneg hl0 (show 0 ≤ x.re - e - (t i + κ * (i - h)) by linarith)]
  have hband : ∀ h i, i ∈ S → |h - i| < q + q → |h| ≤ Hm + 1 := by
    intro h i hi hhi
    have := hHm i hi
    have : |h| ≤ |h - i| + |i| := by simpa using abs_add_le (h - i) i
    linarith
  have hnogap : ∀ h i, i ∈ S → |h - i| < q + q → h ≠ i → h ∉ G := by
    intro h i hi hhi hne hh
    have := hgap h hh i (hSG i hi) hne
    linarith
  refine ⟨q, e, hq, hqR, he, ?_, Γ, hΓc, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hn
    have hai : hgt κ a ∈ S := (hSmem _).2 (Or.inr ⟨a, ha, rfl⟩)
    have hbi : hgt κ b ∈ S := (hSmem _).2 (Or.inr ⟨b, hb, rfl⟩)
    have hne : hgt κ a ≠ hgt κ b := fun hh => hn (hgt_injOn_poles hκ ha.1 hb.1 hh)
    have := hgap _ (hSG _ hai) _ (hSG _ hbi) hne
    linarith
  · intro h; simpa only [pt_re] using hstrip h
  · intro a ha h hh
    have hai : hgt κ a ∈ S := (hSmem _).2 (Or.inr ⟨a, ha, rfl⟩)
    rw [hplat _ hai h hh, ht5 _ a ha rfl, re_eq_absc κ a]
    ring
  · intro a ha hac
    have hr := re_eq_absc κ a
    suffices a.re < Γ.ξ (hgt κ a) - κ * hgt κ a by linarith
    by_cases hh : ∀ i ∈ S, q + q ≤ |hgt κ a - i|
    · rw [hline _ hh]
      have haF : a ∉ Fdelta η := fun haF => by
        have := hh _ ((hSmem _).2 (Or.inl (Or.inl ⟨a, haF, rfl⟩)))
        simp only [sub_self, abs_zero] at this; linarith
      have hbound : a.re ≤ Binf + η := by by_contra h; exact haF ⟨ha, not_le.mp h⟩
      dsimp [η] at hbound
      linarith
    · push_neg at hh
      obtain ⟨i, hi, hhi⟩ := hh
      by_cases hai : hgt κ a = i
      · rw [hplat i hi _ (by rw [hai]; simp; exact hq.le), hai]
        linarith [(ht3 i a ha hai).2 hac]
      · by_contra hn
        have hd : e ≤ a.re := by linarith [(hstrip (hgt κ a)).1, not_lt.mp hn]
        exact hnogap _ i hi hhi hai ((hGmem _).2
          (Or.inl (Or.inr ⟨a, ⟨ha, hd, hband _ i hi hhi⟩, rfl⟩)))
  · intro b hb hbc
    have hr := re_eq_absc κ (x - b)
    simp only [sub_re] at hr
    suffices Γ.ξ (hgt κ (x - b)) - κ * hgt κ (x - b) < x.re - b.re by linarith
    by_cases hh : ∀ i ∈ S, q + q ≤ |hgt κ (x - b) - i|
    · rw [hline _ hh]
      have hbF : b ∉ Fdelta η := fun hbF => by
        have := hh _ ((hSmem _).2 (Or.inl (Or.inr ⟨b, hbF, rfl⟩)))
        simp only [sub_self, abs_zero] at this; linarith
      have hbound : b.re ≤ Binf + η := by by_contra h; exact hbF ⟨hb, not_le.mp h⟩
      dsimp [η, c] at hbound ⊢
      linarith [hx.2]
    · push_neg at hh
      obtain ⟨i, hi, hhi⟩ := hh
      by_cases hbi : hgt κ (x - b) = i
      · rw [hplat i hi _ (by rw [hbi]; simp; exact hq.le), hbi]
        linarith [(ht4 i b hb hbi).2 hbc]
      · by_contra hn
        have hd : e ≤ b.re := by linarith [(hstrip (hgt κ (x - b))).2, not_lt.mp hn]
        exact hnogap _ i hi hhi hbi ((hGmem _).2
          (Or.inr ⟨b, ⟨hb, hd, hband _ i hi hhi⟩, rfl⟩))
end GoldbachBoundaries.HInf.Fill
