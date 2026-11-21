import PrimePairNB.HInf.Defs

/-! Finite gluing by zero extensions of the arcs. The endpoint conditions make each extension continuous. -/
noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

private def arcExtend (r : ℝ) (ξ : ℝ → ℝ) (h : ℝ) : ℝ :=
  if h ∈ Icc (-r) r then ξ h else 0

private lemma arcExtend_eq_zero {r : ℝ} {ξ : ℝ → ℝ} {ε : ℂ}
    (hξ : IsArc r ε ξ) {h : ℝ} (hh : r ≤ |h|) : arcExtend r ξ h = 0 := by
  unfold arcExtend
  split_ifs with hm
  · have : h = -r ∨ h = r := by
      rcases le_abs.mp hh with hh | hh
      · exact Or.inr (le_antisymm hm.2 hh)
      · exact Or.inl (by linarith [hm.1])
    rcases this with rfl | rfl
    · exact hξ.ends.1
    · exact hξ.ends.2
  · rfl

private lemma arcExtend_regular {r : ℝ} (hr : 0 < r) {ξ : ℝ → ℝ} {ε : ℂ}
    (hξ : IsArc r ε ξ) :
    Continuous (arcExtend r ξ) ∧ ∃ S : Finset ℝ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ h : ℝ, h ∉ S → DifferentiableAt ℝ (arcExtend r ξ) h ∧ |deriv (arcExtend r ξ) h| ≤ L := by
  classical
  have hc : Continuous (arcExtend r ξ) := by
    apply continuous_if
    · intro h hh
      change h ∈ frontier (Icc (-r) r) at hh
      rw [frontier_Icc (by linarith : -r ≤ r)] at hh
      simp only [mem_insert_iff, mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · exact hξ.ends.1
      · exact hξ.ends.2
    · change ContinuousOn ξ (closure (Icc (-r) r))
      simpa only [closure_Icc] using hξ.cont
    · exact continuousOn_const
  obtain ⟨S, hS⟩ := hξ.brk
  obtain ⟨L, hL⟩ := hξ.lip
  refine ⟨hc, S ∪ {-r, r}, max L 0, le_max_right _ _, ?_⟩
  intro h hh
  have hnS : h ∉ S := fun hs => hh (Finset.mem_union_left _ hs)
  have hn0 : h ≠ -r := fun he => hh (Finset.mem_union_right _ (by simp [he]))
  have hn1 : h ≠ r := fun he => hh (Finset.mem_union_right _ (by simp [he]))
  by_cases hm : h ∈ Ioo (-r) r
  · have he : arcExtend r ξ =ᶠ[𝓝 h] ξ := by
      filter_upwards [isOpen_Ioo.mem_nhds hm] with t ht
      simp [arcExtend, show t ∈ Icc (-r) r from ⟨ht.1.le, ht.2.le⟩]
    have hd := (hS h hm hnS).congr_of_eventuallyEq he
    refine ⟨hd, ?_⟩
    rw [he.deriv_eq]
    exact (hL h hm).trans (le_max_left _ _)
  · have hm' : h ∈ (Icc (-r) r)ᶜ := by
      intro hcc
      exact hm ⟨lt_of_le_of_ne hcc.1 (Ne.symm hn0), lt_of_le_of_ne hcc.2 hn1⟩
    have he : arcExtend r ξ =ᶠ[𝓝 h] (fun _ => 0) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hm'] with t ht
      exact if_neg ht
    exact ⟨differentiableAt_const (0 : ℝ) |>.congr_of_eventuallyEq he,
      by rw [he.deriv_eq]; simpa using le_max_right L 0⟩

/-- `IsArc` depends only on the closed interval when `ε` is small. -/
lemma isArc_congr_Icc {r : ℝ} (hr : 0 < r) {ε : ℂ} (hε : ‖ε‖ < r / 4)
    {ξ η : ℝ → ℝ} (hξ : IsArc r ε ξ) (he : EqOn η ξ (Icc (-r) r)) : IsArc r ε η := by
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have him : ε.im ∈ Icc (-r) r := by
    have hi := Complex.abs_im_le_norm ε
    have ha := abs_le.mp hi
    constructor <;> linarith
  have hder : ∀ h ∈ Ioo (-r) r, deriv η h = deriv ξ h := by
    intro h hh
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hh] with t ht
    exact he ⟨ht.1.le, ht.2.le⟩
  refine ⟨hξ.cont.congr (fun h hh => he hh), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hξ.brk
    refine ⟨S, fun h hh hn => (hS h hh hn).congr_of_eventuallyEq ?_⟩
    filter_upwards [isOpen_Ioo.mem_nhds hh] with t ht
    exact he ⟨ht.1.le, ht.2.le⟩
  · obtain ⟨L, hL⟩ := hξ.lip
    exact ⟨L, fun h hh => by rw [hder h hh]; exact hL h hh⟩
  · exact ⟨(he ⟨le_rfl, by linarith⟩).trans hξ.ends.1,
      (he ⟨by linarith, le_rfl⟩).trans hξ.ends.2⟩
  · intro h hh; rw [he hh]; exact hξ.small h hh
  · rw [he h0]; exact hξ.west_of
  · rw [he him]; exact hξ.east_of

/-- Gluing arcs into the flat tops of an outer graph. Continuity at each band's ends is `IsArc.ends`. -/
theorem exists_glued_graph {κ : ℝ} (Γ₀ : SlantGraph κ) {x : ℂ} (hfin : (collide x).Finite) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hdisj : ∀ a ∈ collide x, ∀ a' ∈ collide x, a ≠ a' → 2 * r₀ < |hgt κ a - hgt κ a'|)
    (hflat : ∀ a ∈ collide x, ∀ h : ℝ, |h - hgt κ a| ≤ r₀ → Γ₀.ξ h = absc κ a)
    {ε : ℂ} (hε : ‖ε‖ < r₀ / 4) (ξs : ℂ → ℝ → ℝ) (hξ : ∀ a ∈ collide x, IsArc r₀ ε (ξs a)) :
    ∃ Γ : SlantGraph κ, Γ.c = Γ₀.c ∧ (∀ h ∈ outerHeights κ x r₀, Γ.ξ h = Γ₀.ξ h) ∧
      ∀ a ∈ collide x, IsArc r₀ ε (fun h => Γ.ξ (h + hgt κ a) - absc κ a) ∧
        ∀ h ∈ Icc (-r₀) r₀, Γ.ξ (h + hgt κ a) = absc κ a + ξs a h := by
  classical
  let s := hfin.toFinset
  let d (a : ℂ) (h : ℝ) := arcExtend r₀ (ξs a) (h - hgt κ a)
  have hreg : ∀ a ∈ s, Continuous (d a) ∧ ∃ S : Finset ℝ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ h : ℝ, h ∉ S → DifferentiableAt ℝ (d a) h ∧ |deriv (d a) h| ≤ L := by
    intro a ha
    obtain ⟨hc, S, L, hL, hd⟩ := arcExtend_regular hr₀ (hξ a (hfin.mem_toFinset.mp ha))
    refine ⟨hc.comp (by fun_prop), S.image (fun t => t + hgt κ a), L, hL, ?_⟩
    intro h hh
    have hn : h - hgt κ a ∉ S := by
      intro ht
      exact hh (Finset.mem_image.mpr ⟨h - hgt κ a, ht, by ring⟩)
    refine ⟨?_, ?_⟩
    · exact ((hd _ hn).1.hasDerivAt.comp_sub_const h (hgt κ a)).differentiableAt
    · dsimp [d]
      rw [deriv_comp_sub_const]
      exact (hd _ hn).2
  choose S L hL hd using fun a : s => (hreg a a.2).2
  let S' (a : ℂ) : Finset ℝ := if ha : a ∈ s then S ⟨a, ha⟩ else ∅
  let L' (a : ℂ) : ℝ := if ha : a ∈ s then L ⟨a, ha⟩ else 0
  have hd' : ∀ a ∈ s, ∀ h : ℝ, h ∉ S' a →
      DifferentiableAt ℝ (d a) h ∧ |deriv (d a) h| ≤ L' a := by
    intro a ha h hh
    simpa only [S', L', dif_pos ha] using hd ⟨a, ha⟩ h (by simpa [S', ha] using hh)
  let E (h : ℝ) := ∑ a ∈ s, d a h
  let brk := Γ₀.brk ∪ s.biUnion S'
  have hdiff : ∀ h : ℝ, h ∉ brk → DifferentiableAt ℝ E h := by
    intro h hh
    apply DifferentiableAt.fun_sum
    intro a ha
    apply (hd' a ha h _).1
    exact fun hn => hh (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha, hn⟩))
  have hbase : ∀ h : ℝ, h ∉ brk → DifferentiableAt ℝ Γ₀.ξ h :=
    fun h hh => Γ₀.diff h (fun hn => hh (Finset.mem_union_left _ hn))
  have hzero : ∀ a ∈ s, ∀ h, r₀ ≤ |h - hgt κ a| → d a h = 0 := by
    intro a ha h hh
    exact arcExtend_eq_zero (hξ a (hfin.mem_toFinset.mp ha)) hh
  let T := max Γ₀.T (1 + ∑ a ∈ s, (|hgt κ a| + r₀))
  have htail : ∀ h : ℝ, T ≤ |h| → E h = 0 := by
    intro h hh
    apply Finset.sum_eq_zero
    intro a ha
    apply hzero a ha h
    have hb : |hgt κ a| + r₀ ≤ ∑ b ∈ s, (|hgt κ b| + r₀) :=
      Finset.single_le_sum (f := fun b => |hgt κ b| + r₀) (fun b hb => by positivity) ha
    have ht := abs_sub_abs_le_abs_sub h (hgt κ a)
    have hT := le_trans (le_max_right Γ₀.T _) hh
    linarith
  obtain ⟨L₀, hL₀⟩ := Γ₀.lip
  let Γ : SlantGraph κ :=
    { ξ := fun h => Γ₀.ξ h + E h
      cont := Γ₀.cont.add (continuous_finset_sum _ (fun a ha => (hreg a ha).1))
      c := Γ₀.c
      T := T
      tail := fun h hh => by
        rw [htail h hh, add_zero]
        exact Γ₀.tail h ((le_max_left _ _).trans hh)
      brk := brk
      diff := fun h hh => (hbase h hh).add (hdiff h hh)
      lip := by
        refine ⟨L₀ + ∑ a ∈ s, L' a, fun h hh => ?_⟩
        rw [deriv_fun_add (hbase h hh) (hdiff h hh)]
        have hn : ∀ a ∈ s, h ∉ S' a := fun a ha hn =>
          hh (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha, hn⟩))
        have he : deriv E h = ∑ a ∈ s, deriv (d a) h :=
          deriv_fun_sum (fun a ha => (hd' a ha h (hn a ha)).1)
        rw [he]
        apply (abs_add_le _ _).trans
        apply add_le_add
        · exact hL₀ h (fun hn => hh (Finset.mem_union_left _ hn))
        · exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun a ha => (hd' a ha h (hn a ha)).2) }
  have hband : ∀ a ∈ collide x, ∀ h ∈ Icc (-r₀) r₀,
      Γ.ξ (h + hgt κ a) = absc κ a + ξs a h := by
    intro a ha h hh
    have habs : |h| ≤ r₀ := abs_le.mpr ⟨hh.1, hh.2⟩
    have hs : E (h + hgt κ a) = ξs a h := by
      dsimp [E]
      rw [Finset.sum_eq_single a]
      · simp only [d, arcExtend, add_sub_cancel_right, if_pos hh]
      · intro b hb hba
        apply hzero b hb
        have hsep := hdisj a ha b (hfin.mem_toFinset.mp hb) (Ne.symm hba)
        have ht := abs_sub_le (hgt κ a) (h + hgt κ a) (hgt κ b)
        have ht' : |hgt κ a - (h + hgt κ a)| = |h| := by ring_nf; simp
        rw [ht'] at ht
        linarith
      · exact fun hn => (hn (hfin.mem_toFinset.mpr ha)).elim
    change Γ₀.ξ (h + hgt κ a) + E (h + hgt κ a) = _
    rw [hs, hflat a ha _ (by simpa using habs)]
  refine ⟨Γ, rfl, ?_, ?_⟩
  · intro h hh
    change Γ₀.ξ h + E h = Γ₀.ξ h
    have : E h = 0 := Finset.sum_eq_zero fun a ha =>
      hzero a ha h (hh a (hfin.mem_toFinset.mp ha))
    rw [this, add_zero]
  · intro a ha
    refine ⟨isArc_congr_Icc hr₀ hε (hξ a ha) ?_, hband a ha⟩
    intro h hh
    change Γ.ξ (h + hgt κ a) - absc κ a = ξs a h
    rw [hband a ha h hh]
    ring

end GoldbachBoundaries.HInf.Fill

