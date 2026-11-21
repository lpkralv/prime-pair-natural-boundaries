import PrimePairNB.HInf.Fill.absc_lt_iff_re_lt
import PrimePairNB.HInf.Fill.exists_trapezoid_graph

/-! Proof of `exists_separating_iff`: the tent construction.

Margins, in the real-part coordinate `R h = Γ.ξ h - κ h`. `c = Re v / 2`, `ε₀ = (Re v - 1) / 2`, `F = F_η` with
`η = (c - B_∞) / 2`. Off the bands the graph is the line `Re z = c`; `S` is the finite set of heights of `F` and of
`v - F`, so the only left or right points on the wrong side of the line sit at heights in `S`. A tip `t i` is chosen for
every height (`exists_tip`). The gap set `G` holds `S` and the heights in `|h| ≤ Hm + 1` of the points of `Σ` and
`v - Σ` of depth at least `ε₀`, and `w` is below half its gaps, so a band meets no such point except at its centre. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma exists_pos_le_finset {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, 0 < f i) :
    ∃ m : ℝ, 0 < m ∧ ∀ i ∈ S, m ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S _ ih =>
    obtain ⟨m, hm, hle⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    refine ⟨min m (f a), lt_min hm (hf a (Finset.mem_insert_self _ _)), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle i hi)

lemma exists_gap (G : Finset ℝ) : ∃ w : ℝ, 0 < w ∧ ∀ g ∈ G, ∀ g' ∈ G, g ≠ g' → 2 * w < |g - g'| := by
  classical
  obtain ⟨m, hm, hle⟩ := exists_pos_le_finset ((G ×ˢ G).filter fun p => p.1 ≠ p.2)
    (fun p => |p.1 - p.2| / 3) (fun p hp => by
      have := (Finset.mem_filter.mp hp).2
      have : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr this)
      positivity)
  refine ⟨m, hm, fun g hg g' hg' hne => ?_⟩
  have := hle (g, g') (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hg, hg'⟩, hne⟩)
  simp only at this
  linarith

lemma exists_between_finite {A B : Set ℝ} (hA : A.Finite) (hB : B.Finite) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, a < b) : ∃ t : ℝ, (∀ a ∈ A, a < t) ∧ ∀ b ∈ B, t < b := by
  obtain ⟨a₀, ha₀, hmax⟩ := Set.exists_max_image A id hA hAn
  obtain ⟨b₀, hb₀, hmin⟩ := Set.exists_min_image B id hB hBn
  obtain ⟨t, h1, h2⟩ := exists_between (h a₀ ha₀ b₀ hb₀)
  exact ⟨t, fun a ha => (hmax a ha).trans_lt h1, fun b hb => h2.trans_le (hmin b hb)⟩

/-- (S): a left point and a right point on one `κ`-line are in order, unless `v` is on a cut. -/
lemma re_lt_of_not_mem_ray {κ : ℝ} {v a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ)
    (hv : v ∉ ⋃ x ∈ Pinch, rayW κ x) (hh : hgt κ a = hgt κ (v - b)) : a.re < v.re - b.re := by
  by_contra hc
  apply hv
  refine mem_iUnion₂.mpr ⟨a + b, ⟨a, ha, b, hb, rfl⟩, a.re - (v - b).re, ?_, ?_⟩
  · simp only [sub_re]
    linarith
  · have := eq_sub_of_hgt_eq hh
    linear_combination this

/-- The tip on one height: strictly between all left and all right points of that height, and in `(ε₀, Re v - ε₀)`. -/
lemma exists_tip (κ : ℝ) {v : ℂ} (hv : v ∉ ⋃ x ∈ Pinch, rayW κ x) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : ε₀ < v.re - 1)
    (hε₂ : 2 * ε₀ < v.re) (i : ℝ) :
    ∃ t : ℝ, ε₀ < t ∧ t < v.re - ε₀ ∧ (∀ a ∈ PoleSetQ, hgt κ a = i → a.re < t) ∧
      ∀ b ∈ PoleSetQ, hgt κ (v - b) = i → t < v.re - b.re := by
  set LP : Set ℂ := {a | a ∈ PoleSetQ ∧ ε₀ ≤ a.re ∧ hgt κ a = i} with hLP
  set RP : Set ℂ := {b | b ∈ PoleSetQ ∧ ε₀ ≤ b.re ∧ hgt κ (v - b) = i} with hRP
  have hLf : LP.Finite := (finite_poleSetQ_height κ hε₀ |i|).subset fun a ha =>
    ⟨ha.1, ha.2.1, by rw [ha.2.2]⟩
  have hRf : RP.Finite := (finite_poleSetQ_height κ hε₀ (|i| + |hgt κ v|)).subset fun b hb => by
    refine ⟨hb.1, hb.2.1, ?_⟩
    have e : hgt κ b = hgt κ v - i := by
      have := hb.2.2
      rw [hgt_sub] at this
      linarith
    rw [e]
    exact (abs_sub _ _).trans (by rw [add_comm])
  obtain ⟨t, h1, h2⟩ := exists_between_finite (A := insert ε₀ (re '' LP))
    (B := insert (v.re - ε₀) ((fun b => v.re - b.re) '' RP))
    ((hLf.image _).insert _) ((hRf.image _).insert _) (insert_nonempty _ _) (insert_nonempty _ _) (by
      rintro x (rfl | ⟨a, ha, rfl⟩) y (rfl | ⟨b, hb, rfl⟩)
      · linarith
      · have := (M1.poleSetQ_re_bounds hb.1).2.1
        simp only
        linarith
      · have := (M1.poleSetQ_re_bounds ha.1).2.1
        linarith
      · exact re_lt_of_not_mem_ray ha.1 hb.1 hv (ha.2.2.trans hb.2.2.symm))
  have h3 : ε₀ < t := h1 _ (mem_insert _ _)
  have h4 : t < v.re - ε₀ := h2 _ (mem_insert _ _)
  refine ⟨t, h3, h4, fun a ha hh => ?_, fun b hb hh => ?_⟩
  · by_cases hd : ε₀ ≤ a.re
    · exact h1 _ (mem_insert_of_mem _ ⟨a, ⟨ha, hd, hh⟩, rfl⟩)
    · linarith
  · by_cases hd : ε₀ ≤ b.re
    · exact h2 _ (mem_insert_of_mem _ ⟨b, ⟨hb, hd, hh⟩, rfl⟩)
    · linarith

/-- The "if" direction of `exists_separating_iff`, the tent construction. -/
theorem exists_separating_of_mem_Om (hZ1 : Z1) {κ : ℝ} {top : EReal} {v : ℂ} (hv : v ∈ Om κ top) :
    ∃ Γ : SlantGraph κ, IsSeparating v Γ := by
  classical
  obtain ⟨⟨⟨hv1, -⟩, hvB⟩, hvcut⟩ := hv
  set c : ℝ := v.re / 2 with hc
  set ε₀ : ℝ := (v.re - 1) / 2 with hε₀def
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; linarith
  have hε₁ : ε₀ < v.re - 1 := by rw [hε₀def]; linarith
  have hε₂ : 2 * ε₀ < v.re := by rw [hε₀def]; linarith
  have hcε : c - ε₀ = 1 / 2 := by rw [hc, hε₀def]; ring
  have hvc : v.re - c = c := by rw [hc]; ring
  set η : ℝ := (c - Binf) / 2 with hη
  have hcB : Binf < c := by rw [hc]; linarith
  have hηpos : 0 < η := by rw [hη]; linarith
  have hFf : (Fdelta η).Finite := (M1.Fdelta_spec hZ1 η hηpos).1
  -- the heights that need a tent
  set H : Set ℝ := hgt κ '' Fdelta η ∪ (fun b => hgt κ (v - b)) '' Fdelta η with hH
  have hHf : H.Finite := (hFf.image _).union (hFf.image _)
  set S : Finset ℝ := hHf.toFinset with hS
  have hSmem : ∀ i, i ∈ S ↔ i ∈ H := fun i => hHf.mem_toFinset
  set Hm : ℝ := ∑ i ∈ S, |i| with hHm
  have hHmle : ∀ i ∈ S, |i| ≤ Hm := fun i hi =>
    Finset.single_le_sum (f := fun j : ℝ => |j|) (fun _ _ => abs_nonneg _) hi
  -- the points of depth `≥ ε₀` in the window
  set AP : Set ℂ := {a | a ∈ PoleSetQ ∧ ε₀ ≤ a.re ∧ |hgt κ a| ≤ Hm + 1} with hAP
  set BP : Set ℂ := {b | b ∈ PoleSetQ ∧ ε₀ ≤ b.re ∧ |hgt κ (v - b)| ≤ Hm + 1} with hBP
  have hAf : AP.Finite := finite_poleSetQ_height κ hε₀ _
  have hBf : BP.Finite := (finite_poleSetQ_height κ hε₀ (Hm + 1 + |hgt κ v|)).subset fun b hb => by
    refine ⟨hb.1, hb.2.1, ?_⟩
    have e : hgt κ b = hgt κ v - hgt κ (v - b) := by rw [hgt_sub]; ring
    rw [e]
    exact (abs_sub _ _).trans (by linarith [hb.2.2])
  have hGf : (H ∪ hgt κ '' AP ∪ (fun b => hgt κ (v - b)) '' BP).Finite :=
    (hHf.union (hAf.image _)).union (hBf.image _)
  set G : Finset ℝ := hGf.toFinset with hG
  have hGmem : ∀ i, i ∈ G ↔ i ∈ H ∪ hgt κ '' AP ∪ (fun b => hgt κ (v - b)) '' BP := fun i => hGf.mem_toFinset
  have hSG : ∀ i ∈ S, i ∈ G := fun i hi => (hGmem i).2 (Or.inl (Or.inl ((hSmem i).1 hi)))
  obtain ⟨w₁, hw₁, hgap⟩ := exists_gap G
  -- the tips
  have htip := exists_tip κ hvcut hε₀ hε₁ hε₂
  choose t ht1 ht2 ht3 ht4 using htip
  obtain ⟨m₁, hm₁, hm₁le⟩ := exists_pos_le_finset S (fun i => min (t i - ε₀) (v.re - ε₀ - t i)) (fun i _ =>
    lt_min (by linarith [ht1 i]) (by linarith [ht2 i]))
  set m : ℝ := min m₁ (1 / 2) with hm
  have hmpos : 0 < m := lt_min hm₁ (by norm_num)
  have hmhalf : m ≤ 1 / 2 := min_le_right _ _
  have hmt : ∀ i ∈ S, m ≤ t i - ε₀ ∧ m ≤ v.re - ε₀ - t i := fun i hi => by
    have := hm₁le i hi
    have h0 : m ≤ m₁ := min_le_left _ _
    exact ⟨(h0.trans this).trans (min_le_left _ _), (h0.trans this).trans (min_le_right _ _)⟩
  have hk1 : 0 < |κ| + 1 := by positivity
  set w : ℝ := min (min w₁ 1) (m / (2 * (|κ| + 1))) with hw
  have hwpos : 0 < w := lt_min (lt_min hw₁ one_pos) (by positivity)
  have hww₁ : w ≤ w₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hw1 : w ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hκw : |κ| * w ≤ m / 2 := by
    have h1 : w ≤ m / (2 * (|κ| + 1)) := min_le_right _ _
    have h2 : w * (|κ| + 1) ≤ m / 2 := by
      calc w * (|κ| + 1) ≤ m / (2 * (|κ| + 1)) * (|κ| + 1) := by gcongr
        _ = m / 2 := by field_simp
    nlinarith [abs_nonneg κ]
  obtain ⟨Γ, hΓc, hline, hplat, hramp⟩ := Fill.exists_trapezoid_graph κ c S id (fun _ => 0)
    (fun i => t i + κ * i) hwpos (fun _ _ => le_refl _) (fun i hi j hj hij => by
      have := hgap i (hSG i hi) j (hSG j hj) hij
      simp only [id]
      linarith)
  simp only [id, zero_add] at hline hplat hramp
  -- real parts of the graph
  have hR : ∀ h : ℝ, ε₀ + m / 2 ≤ Γ.ξ h - κ * h ∧ Γ.ξ h - κ * h ≤ v.re - ε₀ - m / 2 := by
    intro h
    by_cases hb : ∀ i ∈ S, w ≤ |h - i|
    · rw [hline h hb]
      constructor <;> linarith
    · push Not at hb
      obtain ⟨i, hi, hhi⟩ := hb
      obtain ⟨l, ⟨hl0, hl1⟩, he⟩ := hramp i hi h hhi
      have hA : |κ * (i - h)| ≤ m / 2 := by
        rw [abs_mul]
        refine le_trans ?_ hκw
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_sub_comm]
        exact hhi.le
      obtain ⟨hA1, hA2⟩ := abs_le.mp hA
      obtain ⟨hm1, hm2⟩ := hmt i hi
      have e2 : Γ.ξ h - κ * h = (1 - l) * c + l * (t i + κ * (i - h)) := by
        rw [he]; ring
      rw [e2]
      have hl1' : 0 ≤ 1 - l := by linarith
      constructor
      · have p1 : 0 ≤ (1 - l) * (c - (ε₀ + m / 2)) := mul_nonneg hl1' (by linarith)
        have p2 : 0 ≤ l * (t i + κ * (i - h) - (ε₀ + m / 2)) := mul_nonneg hl0 (by linarith)
        nlinarith
      · have p1 : 0 ≤ (1 - l) * (v.re - ε₀ - m / 2 - c) := mul_nonneg hl1' (by linarith)
        have p2 : 0 ≤ l * (v.re - ε₀ - m / 2 - (t i + κ * (i - h))) := mul_nonneg hl0 (by linarith)
        nlinarith
  have hband : ∀ h i : ℝ, i ∈ S → |h - i| < w → |h| ≤ Hm + 1 := by
    intro h i hi hhi
    have := hHmle i hi
    have h2 : |h| ≤ |h - i| + |i| := by
      simpa using abs_add_le (h - i) i
    linarith
  have hnogap : ∀ h i : ℝ, i ∈ S → |h - i| < w → h ≠ i → h ∉ G := by
    intro h i hi hhi hne hG'
    have := hgap h hG' i (hSG i hi) hne
    linarith
  refine ⟨Γ, ⟨⟨ε₀, hε₀, fun h => ?_⟩, ⟨?_, ?_⟩, fun a ha => ?_, fun b hb => ?_⟩⟩
  · rw [pt_re]
    obtain ⟨h1, h2⟩ := hR h
    constructor <;> linarith
  · rw [hΓc]; exact hcB
  · rw [hΓc]; linarith
  · have hr := re_eq_absc κ a
    suffices a.re < Γ.ξ (hgt κ a) - κ * hgt κ a by linarith
    by_cases hb : ∀ i ∈ S, w ≤ |hgt κ a - i|
    · rw [hline _ hb]
      have haF : a ∉ Fdelta η := fun hF => by
        have := hb (hgt κ a) ((hSmem _).2 (Or.inl ⟨a, hF, rfl⟩))
        simp at this
        linarith
      have : a.re ≤ Binf + η := by
        by_contra hcc
        exact haF ⟨ha, not_le.mp hcc⟩
      have : Binf + η < c := by rw [hη]; linarith
      linarith
    · push Not at hb
      obtain ⟨i, hi, hhi⟩ := hb
      by_cases hei : hgt κ a = i
      · rw [hplat i hi _ (by rw [hei]; simp)]
        have := ht3 i a ha hei
        rw [hei]
        linarith
      · by_contra hcc
        have hd : ε₀ ≤ a.re := by linarith [(hR (hgt κ a)).1, not_lt.mp hcc]
        apply hnogap _ i hi hhi hei
        exact (hGmem _).2 (Or.inl (Or.inr ⟨a, ⟨ha, hd, hband _ i hi hhi⟩, rfl⟩))
  · have hr := re_eq_absc κ (v - b)
    have hre' : (v - b).re = v.re - b.re := by simp
    suffices Γ.ξ (hgt κ (v - b)) - κ * hgt κ (v - b) < v.re - b.re by linarith
    by_cases hb' : ∀ i ∈ S, w ≤ |hgt κ (v - b) - i|
    · rw [hline _ hb']
      have hbF : b ∉ Fdelta η := fun hF => by
        have := hb' (hgt κ (v - b)) ((hSmem _).2 (Or.inr ⟨b, hF, rfl⟩))
        simp at this
        linarith
      have : b.re ≤ Binf + η := by
        by_contra hcc
        exact hbF ⟨hb, not_le.mp hcc⟩
      have : Binf + η < c := by rw [hη]; linarith
      linarith
    · push Not at hb'
      obtain ⟨i, hi, hhi⟩ := hb'
      by_cases hei : hgt κ (v - b) = i
      · rw [hplat i hi _ (by rw [hei]; simp)]
        have := ht4 i b hb hei
        rw [hei]
        linarith
      · by_contra hcc
        have hd : ε₀ ≤ b.re := by linarith [(hR (hgt κ (v - b))).2, not_lt.mp hcc]
        apply hnogap _ i hi hhi hei
        exact (hGmem _).2 (Or.inr ⟨b, ⟨hb, hd, hband _ i hi hhi⟩, rfl⟩)

/-- **Blocked exactly on the cuts.** A separating `κ`-graph for `v ∈ 𝒱_∞` exists iff `v ∈ Ω_θ`.
No genericity. The "if" direction is the tent construction. -/
theorem exists_separating_iff (hZ1 : Z1) {κ : ℝ} {top : EReal} {v : ℂ} (hv : v ∈ VInf top) :
    (∃ Γ : SlantGraph κ, IsSeparating v Γ) ↔ v ∈ Om κ top := by
  constructor
  · rintro ⟨Γ, hΓ⟩
    refine ⟨hv, fun hm => ?_⟩
    obtain ⟨x, ⟨a, ha, b, hb, rfl⟩, t, ht, he⟩ := mem_iUnion₂.mp hm
    have e : v - b = a - (t : ℂ) * slantDir κ := by
      rw [he]; ring
    have h1 := hΓ.left a ha
    have h2 := hΓ.right b hb
    rw [e, hgt_sub_mul, absc_sub_mul] at h2
    linarith
  · exact exists_separating_of_mem_Om hZ1

end GoldbachBoundaries.HInf.Fill

