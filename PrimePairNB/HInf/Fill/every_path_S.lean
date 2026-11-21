import PrimePairNB.HInf.Fill.boundary_S
import PrimePairNB.HInf.Fill.pinch_countable

/-!
# `every_path_S`

As `every_path_G`. The invariant `PathGoodS` holds at every `t`: on a disc about `γ t` inside `σ > 0`, the germ is analytic,
and admissible at each point off `catS`. It holds on a clopen set of times, hence at all of them.

`no_extension_any_path_S` and `every_path_stays_S` read off the same invariant.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- On a disc about `p` inside `σ > 0`, `h` is analytic, and admissible at each point off `catS`. -/
def PathGoodS (h : ℂ → ℂ) (p : ℂ) : Prop :=
  ∃ ρ > 0, ball p ρ ⊆ halfPlane 0 ∧ AnalyticOnNhd ℂ h (ball p ρ) ∧ ∀ w ∈ ball p ρ, w ∉ catS → AdmS h w

/-- An analytic admissible germ stays admissible along a joined set off the catalogue. -/
lemma admS_of_joinedIn {h : ℂ → ℂ} {a b : ℂ} {T : Set ℂ} (ha : AdmS h a) (hj : JoinedIn T a b)
    (hT : T ⊆ halfPlane 0 \ catS) (han : ∀ z ∈ T, AnalyticAt ℂ h z) : AdmS h b := by
  have hmem := hj.somePath_mem
  set p := hj.somePath
  have h1 : (p.toContinuousMap : C(unitInterval, ℂ)) 1 = b := p.target
  have h0 : (p.toContinuousMap : C(unitInterval, ℂ)) 0 = a := p.source
  have := admS_trans ha p.toContinuousMap h0 (fun t => hT (hmem t))
    (ThmA.isTerminalGerm_of_analyticAt (fun t => han _ (hmem t)) EventuallyEq.rfl)
  rwa [h1] at this

/-- There is a point off `catS` in every non-empty open set. -/
lemma exists_not_catS {V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty) : ∃ w ∈ V, w ∉ catS := by
  have hc : ((fun s : ℂ => 2 * s + 1) ⁻¹' Pinch).Countable := by
    refine pinch_countable.preimage_of_injOn (fun a _ b _ hab => ?_)
    have h2 : (2 : ℂ) * a = 2 * b := add_right_cancel hab
    exact mul_left_cancel₀ two_ne_zero h2
  obtain ⟨w, hw, hwc⟩ := (hc.dense_compl ℝ).inter_open_nonempty V hV hne
  exact ⟨w, hw, fun h => hwc (mem_catS_iff.mp h).2⟩

/-- `ball p ρ` lies in `σ > 0` when `ρ ≤ Re p`. -/
lemma ball_subset_halfPlane_zero {p : ℂ} {ρ : ℝ} (h : ρ ≤ p.re) : ball p ρ ⊆ halfPlane 0 := by
  intro w hw
  have h1 : |w.re - p.re| ≤ ‖w - p‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have h2 : ‖w - p‖ < ρ := by rw [← dist_eq_norm]; exact hw
  show (0 : ℝ) < w.re
  linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]

/-- **The invariant holds at every time.** -/
theorem pathGoodS_all (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) {f : unitInterval → ℂ → ℂ} (hf : IsContinuationAlong γ f)
    (hf0 : f 0 =ᶠ[𝓝 (γ 0)] Sser) (t : unitInterval) : PathGoodS (f t) (γ t) := by
  set A : Set unitInterval := {t | PathGoodS (f t) (γ t)} with hA
  -- start
  have h0A : (0 : unitInterval) ∈ A := by
    obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hf0
    have hpos : 0 < (γ 0).re - 1 := sub_pos.mpr h0
    have hre : ∀ w ∈ ball (γ 0) (min ρ₁ ((γ 0).re - 1)), 1 < w.re := by
      intro w hw
      have h1 : |w.re - (γ 0).re| ≤ ‖w - γ 0‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : ‖w - γ 0‖ < (γ 0).re - 1 := by
        rw [← dist_eq_norm]; exact lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _)
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]
    have heq : ∀ w ∈ ball (γ 0) (min ρ₁ ((γ 0).re - 1)), f 0 =ᶠ[𝓝 w] Sser := by
      intro w hw
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hb z (ball_subset_ball (min_le_left _ _) hz)
    refine ⟨min ρ₁ ((γ 0).re - 1), lt_min hρ₁ hpos, fun w hw => ?_,
      fun w hw => (Sser_analyticAt (by linarith [hre w hw])).congr (heq w hw).symm, fun w hw _ => ?_⟩
    · show (0 : ℝ) < w.re
      linarith [hre w hw]
    · exact admS_congr (admS_of_one_lt (hre w hw)) (heq w hw).symm
  -- open
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro t ⟨ρ, hρ, hsub, han, had⟩
    filter_upwards [(γ.continuous.tendsto t).eventually_mem (ball_mem_nhds _ hρ), hf.locallyEq t] with t' ht' hloc
    obtain ⟨ρ₂, hρ₂, hρ₂s⟩ := Metric.isOpen_iff.mp isOpen_ball (γ t') ht'
    obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hloc
    have heq : ∀ w ∈ ball (γ t') (min ρ₁ ρ₂), f t' =ᶠ[𝓝 w] f t := by
      intro w hw
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hb z (ball_subset_ball (min_le_left _ _) hz)
    have hin : ∀ w ∈ ball (γ t') (min ρ₁ ρ₂), w ∈ ball (γ t) ρ := fun w hw =>
      hρ₂s (ball_subset_ball (min_le_right _ _) hw)
    exact ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun w hw => hsub (hin w hw),
      fun w hw => (han w (hin w hw)).congr (heq w hw).symm,
      fun w hw hwc => admS_congr (had w (hin w hw) hwc) (heq w hw).symm⟩
  -- closed
  have hAc : IsClosed A := by
    apply isClosed_of_closure_subset
    intro t ht
    obtain ⟨ρ, hρ, han⟩ := Metric.eventually_nhds_iff_ball.mp (hf.analyticAt t).eventually_analyticAt
    have hnear : ∀ ε > 0, ∃ w ∈ ball (γ t) ε, AdmS (f t) w := by
      intro ε hε
      obtain ⟨t', ht'A, ht'b, hloc⟩ := (mem_closure_iff_frequently.mp ht).and_eventually
        (((γ.continuous.tendsto t).eventually_mem (ball_mem_nhds _ hε)).and (hf.locallyEq t)) |>.exists
      obtain ⟨ρ', hρ', -, -, had⟩ := ht'A
      obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hloc
      obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball _ ht'b
      obtain ⟨w, hw, hwP⟩ := exists_not_catS (V := ball (γ t') (min ρ' (min ρ₁ ρ₂))) isOpen_ball
        ⟨_, mem_ball_self (lt_min hρ' (lt_min hρ₁ hρ₂))⟩
      refine ⟨w, hsub (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hw),
        admS_congr (had w (ball_subset_ball (min_le_left _ _) hw) hwP) ?_⟩
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hb z (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz)
    have hge : 0 ≤ (γ t).re := by
      by_contra hlt'
      have hlt : (γ t).re < 0 := not_le.mp hlt'
      obtain ⟨w, hw, had⟩ := hnear (0 - (γ t).re) (by linarith)
      have h1 : (0 : ℝ) < w.re := (admS_mem had).1
      have h3 : |w.re - (γ t).re| ≤ ‖w - γ t‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h4 : ‖w - γ t‖ < 0 - (γ t).re := by rw [← dist_eq_norm]; exact hw
      linarith [(abs_lt.mp (lt_of_le_of_lt h3 h4)).2]
    have hgt : 0 < (γ t).re := by
      refine lt_of_le_of_ne hge fun hre => ?_
      set y := (γ t).im with hy
      have hγeq : γ t = (y : ℂ) * I := Complex.ext (by simp [← hre]) (by simp [hy])
      obtain ⟨w, hw, had⟩ := hnear ρ hρ
      rw [hγeq] at hw han
      exact boundary_S hH hZ1 hZ2 hZ3 hZ4 hZ5 had y ρ hρ hw
        ⟨hw, f t, fun z hz => (han z hz).meromorphicAt, EventuallyEq.rfl⟩
    obtain ⟨ρ₃, hρ₃, hnp⟩ : ∃ ρ₃ > 0, ∀ w ∈ ball (γ t) ρ₃, w ≠ γ t → w ∉ catS := by
      have h := eventually_not_catS hZ1 hH hgt
      rw [eventually_nhdsWithin_iff] at h
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
      exact ⟨ε, hε, fun w hw hne => hball w hw hne⟩
    set ρ₀ := min ρ (min ρ₃ (γ t).re) with hρ₀
    have hρ₀pos : 0 < ρ₀ := lt_min hρ (lt_min hρ₃ hgt)
    have h1 : ρ₀ ≤ ρ := min_le_left _ _
    have h2 : ρ₀ ≤ ρ₃ := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : ρ₀ ≤ (γ t).re := (min_le_right _ _).trans (min_le_right _ _)
    have hHH : ball (γ t) ρ₀ ⊆ halfPlane 0 := ball_subset_halfPlane_zero h3
    refine ⟨ρ₀, hρ₀pos, hHH, fun z hz => han z (ball_subset_ball h1 hz), fun w hw hwc => ?_⟩
    obtain ⟨w', hw', had⟩ := hnear ρ₀ hρ₀pos
    have hpc := ThmA.PathIntoFill.isPathConnected_ball_diff catS (γ t) hρ₀pos
      (fun v hv hne => hnp v (ball_subset_ball h2 hv) hne)
    exact admS_of_joinedIn had (hpc.joinedIn w' ⟨hw', (admS_mem had).2⟩ w ⟨hw, hwc⟩)
      (fun z hz => ⟨hHH hz.1, hz.2⟩) (fun z hz => han z (ball_subset_ball h1 hz.1))
  have huniv : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨0, h0A⟩
  have : t ∈ A := huniv ▸ mem_univ t
  exact this

/-- Proof of `HInf.every_path_S` (paper, Corollary 8.3 for `S`). -/
theorem every_path_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5)
    {γ : C(unitInterval, ℂ)} (h0 : 1 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm Sser γ g) (h1 : γ 1 ∉ catS) :
    AdmS g (γ 1) := by
  obtain ⟨f, hf, hf0, hg1⟩ := hg
  obtain ⟨ρ, hρ, -, -, had⟩ := pathGoodS_all hH hZ1 hZ2 hZ3 hZ4 hZ5 h0 hf hf0 1
  exact admS_congr (had _ (mem_ball_self hρ) h1) hg1.symm

end GoldbachBoundaries.HInf.Fill

