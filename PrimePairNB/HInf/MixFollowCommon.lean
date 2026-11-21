import PrimePairNB.HInf.Fill.every_path_G
import PrimePairNB.HInf.ExistsAdmS

/-! Shared path and existence arguments in the pinch coordinate. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.Follow

abbrev Adm (F g : ℂ → ℂ) (s : ℂ) : Prop :=
  IsAdmissibleGermOn F (HH \ catG) (halfPlane 2) g s

lemma adm_congr {F : ℂ → ℂ} {g g' : ℂ → ℂ} {s : ℂ} (h : Adm F g s) (hgg : g =ᶠ[𝓝 s] g') : Adm F g' s := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := h
  exact ⟨γ, hγ, h0, rfl, f, hf, hf0, hgg.symm.trans hg1⟩

lemma adm_mem {F : ℂ → ℂ} {g : ℂ → ℂ} {s : ℂ} (h : Adm F g s) : s ∈ HH \ catG := by
  obtain ⟨γ, hγ, -, rfl, -⟩ := h
  exact hγ 1

/-- Continue an admissible germ along a path off the catalogue. -/
lemma adm_trans {F : ℂ → ℂ} {g g' : ℂ → ℂ} {s : ℂ} (hg : Adm F g s) (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s)
    (hγ : ∀ t, γ t ∈ HH \ catG) (hg' : IsTerminalGerm g γ g') : Adm F g' (γ 1) := by
  obtain ⟨γ₁, hγ₁, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, hδr, hδ⟩ := ThmA.isTerminalGerm_trans_proof hterm (hγ0.trans h1.symm) hg'
  refine ⟨δ, fun t => ?_, by rw [hδ0]; exact h2, hδ1, hδ⟩
  rcases hδr t with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]; exact hγ₁ u
  · rw [← hu]; exact hγ u

lemma adm_of_two_lt {F : ℂ → ℂ}
    (han : ∀ s : ℂ, 2 < s.re → AnalyticAt ℂ F s) {w : ℂ} (hw : 2 < w.re) : Adm F F w := by
  have hmem : w ∈ HH \ catG :=
    ⟨by show 1 < w.re; linarith,
      fun hc => by linarith [re_le_two_of_mem_pinch (mem_catG_iff.mp hc).2]⟩
  exact ⟨ContinuousMap.const _ w, fun _ => hmem, hw, rfl,
    ThmA.isTerminalGerm_of_analyticAt (fun _ => han w hw) EventuallyEq.rfl⟩

/-- On a disc about `p` inside `σ > 1`, `h` is analytic, and admissible at each point off `catG`. -/
def PathGood (F : ℂ → ℂ) (h : ℂ → ℂ) (p : ℂ) : Prop :=
  ∃ ρ > 0, ball p ρ ⊆ HH ∧ AnalyticOnNhd ℂ h (ball p ρ) ∧ ∀ w ∈ ball p ρ, w ∉ catG → Adm F h w

/-- An analytic admissible germ stays admissible along a joined set off the catalogue. -/
lemma adm_of_joinedIn {F : ℂ → ℂ} {h : ℂ → ℂ} {a b : ℂ} {T : Set ℂ} (ha : Adm F h a) (hj : JoinedIn T a b)
    (hT : T ⊆ HH \ catG) (han : ∀ z ∈ T, AnalyticAt ℂ h z) : Adm F h b := by
  have hmem := hj.somePath_mem
  set p := hj.somePath
  have h1 : (p.toContinuousMap : C(unitInterval, ℂ)) 1 = b := p.target
  have h0 : (p.toContinuousMap : C(unitInterval, ℂ)) 0 = a := p.source
  have := adm_trans ha p.toContinuousMap h0 (fun t => hT (hmem t))
    (ThmA.isTerminalGerm_of_analyticAt (fun t => han _ (hmem t)) EventuallyEq.rfl)
  rwa [h1] at this

/-- **The invariant holds at every time.** -/
theorem pathGood_all {F : ℂ → ℂ} (hH : Hinf) (hZ1 : Z1)
    (hF : ∀ s : ℂ, 2 < s.re → AnalyticAt ℂ F s)
    (hboundary : ∀ (g : ℂ → ℂ) (s : ℂ), Adm F g s → ∀ y r : ℝ, 0 < r →
      s ∈ ball (1 + (y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g s (ball (1 + (y : ℂ) * I) r))
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) {f : unitInterval → ℂ → ℂ} (hf : IsContinuationAlong γ f)
    (hf0 : f 0 =ᶠ[𝓝 (γ 0)] F) (t : unitInterval) : PathGood F (f t) (γ t) := by
  set A : Set unitInterval := {t | PathGood F (f t) (γ t)} with hA
  -- start
  have h0A : (0 : unitInterval) ∈ A := by
    obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hf0
    have hpos : 0 < (γ 0).re - 2 := sub_pos.mpr h0
    have hre : ∀ w ∈ ball (γ 0) (min ρ₁ ((γ 0).re - 2)), 2 < w.re := by
      intro w hw
      have h1 : |w.re - (γ 0).re| ≤ ‖w - γ 0‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : ‖w - γ 0‖ < (γ 0).re - 2 := by
        rw [← dist_eq_norm]; exact lt_of_lt_of_le (mem_ball.mp hw) (min_le_right _ _)
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 h2)).1]
    have heq : ∀ w ∈ ball (γ 0) (min ρ₁ ((γ 0).re - 2)), f 0 =ᶠ[𝓝 w] F := by
      intro w hw
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hb z (ball_subset_ball (min_le_left _ _) hz)
    refine ⟨min ρ₁ ((γ 0).re - 2), lt_min hρ₁ hpos, fun w hw => ?_,
      fun w hw => (hF w (hre w hw)).congr (heq w hw).symm, fun w hw _ => ?_⟩
    · show 1 < w.re
      linarith [hre w hw]
    · exact adm_congr (adm_of_two_lt hF (hre w hw)) (heq w hw).symm
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
      fun w hw hwc => adm_congr (had w (hin w hw) hwc) (heq w hw).symm⟩
  -- closed
  have hAc : IsClosed A := by
    apply isClosed_of_closure_subset
    intro t ht
    obtain ⟨ρ, hρ, han⟩ := Metric.eventually_nhds_iff_ball.mp (hf.analyticAt t).eventually_analyticAt
    have hnear : ∀ ε > 0, ∃ w ∈ ball (γ t) ε, Adm F (f t) w := by
      intro ε hε
      obtain ⟨t', ht'A, ht'b, hloc⟩ := (mem_closure_iff_frequently.mp ht).and_eventually
        (((γ.continuous.tendsto t).eventually_mem (ball_mem_nhds _ hε)).and (hf.locallyEq t)) |>.exists
      obtain ⟨ρ', hρ', -, -, had⟩ := ht'A
      obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hloc
      obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball _ ht'b
      obtain ⟨w, hw, hwP⟩ := exists_not_pinch (V := ball (γ t') (min ρ' (min ρ₁ ρ₂))) isOpen_ball
        ⟨_, mem_ball_self (lt_min hρ' (lt_min hρ₁ hρ₂))⟩
      refine ⟨w, hsub (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hw),
        adm_congr (had w (ball_subset_ball (min_le_left _ _) hw) (not_catG_of_not_pinch hwP)) ?_⟩
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hb z (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz)
    have hge : 1 ≤ (γ t).re := by
      by_contra hlt'
      have hlt : (γ t).re < 1 := not_le.mp hlt'
      obtain ⟨w, hw, had⟩ := hnear (1 - (γ t).re) (by linarith)
      have h1 : (1 : ℝ) < w.re := (adm_mem had).1
      have h3 : |w.re - (γ t).re| ≤ ‖w - γ t‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h4 : ‖w - γ t‖ < 1 - (γ t).re := by rw [← dist_eq_norm]; exact hw
      linarith [(abs_lt.mp (lt_of_le_of_lt h3 h4)).2]
    have hgt : 1 < (γ t).re := by
      refine lt_of_le_of_ne hge fun hre => ?_
      set y := (γ t).im with hy
      have hγeq : γ t = 1 + (y : ℂ) * I := Complex.ext (by simp [← hre]) (by simp [hy])
      obtain ⟨w, hw, had⟩ := hnear ρ hρ
      rw [hγeq] at hw han
      exact hboundary (f t) w had y ρ hρ hw
        ⟨hw, f t, fun z hz => (han z hz).meromorphicAt, EventuallyEq.rfl⟩
    obtain ⟨ρ₃, hρ₃, hnp⟩ : ∃ ρ₃ > 0, ∀ w ∈ ball (γ t) ρ₃, w ≠ γ t → w ∉ Pinch := by
      have h := eventually_not_pinch hZ1 hH hgt
      rw [eventually_nhdsWithin_iff] at h
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
      exact ⟨ε, hε, fun w hw hne => hball w hw hne⟩
    have hx1 : 0 < (γ t).re - 1 := sub_pos.mpr hgt
    set ρ₀ := min ρ (min ρ₃ ((γ t).re - 1)) with hρ₀
    have hρ₀pos : 0 < ρ₀ := lt_min hρ (lt_min hρ₃ hx1)
    have h1 : ρ₀ ≤ ρ := min_le_left _ _
    have h2 : ρ₀ ≤ ρ₃ := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : ρ₀ ≤ (γ t).re - 1 := (min_le_right _ _).trans (min_le_right _ _)
    have hHH : ball (γ t) ρ₀ ⊆ HH := ThmA.ball_subset_HH h3
    refine ⟨ρ₀, hρ₀pos, hHH, fun z hz => han z (ball_subset_ball h1 hz), fun w hw hwc => ?_⟩
    obtain ⟨w', hw', had⟩ := hnear ρ₀ hρ₀pos
    have hpc := ThmA.PathIntoFill.isPathConnected_ball_diff catG (γ t) hρ₀pos
      (fun v hv hne => not_catG_of_not_pinch (hnp v (ball_subset_ball h2 hv) hne))
    exact adm_of_joinedIn had (hpc.joinedIn w' ⟨hw', (adm_mem had).2⟩ w ⟨hw, hwc⟩)
      (fun z hz => ⟨hHH hz.1, hz.2⟩) (fun z hz => han z (ball_subset_ball h1 hz.1))
  have huniv : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨0, h0A⟩
  have : t ∈ A := huniv ▸ mem_univ t
  exact this

/-- Every continuation has an admissible terminal germ off the catalogue. -/
theorem every_path {F : ℂ → ℂ} (hH : Hinf) (hZ1 : Z1)
    (hF : ∀ s : ℂ, 2 < s.re → AnalyticAt ℂ F s)
    (hboundary : ∀ (g : ℂ → ℂ) (s : ℂ), Adm F g s → ∀ y r : ℝ, 0 < r →
      s ∈ ball (1 + (y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g s (ball (1 + (y : ℂ) * I) r))
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) {g : ℂ → ℂ}
    (hg : IsTerminalGerm F γ g) (h1 : γ 1 ∉ catG) : Adm F g (γ 1) := by
  obtain ⟨f, hf, hf0, hg1⟩ := hg
  obtain ⟨ρ, hρ, -, -, had⟩ := pathGood_all hH hZ1 hF hboundary h0 hf hf0 1
  exact adm_congr (had _ (mem_ball_self hρ) h1) hg1.symm

/-- A cut-free segment supplies a germ at every point of the admissible region. -/
theorem exists_adm_iff {F : ℂ → ℂ}
    (hcont : ∀ (γ : C(unitInterval, ℂ)), (∀ t, γ t ∈ HH \ catG) →
      2 < (γ 0).re → ContinuesAlong F γ) {s : ℂ} :
    (∃ g : ℂ → ℂ, Adm F g s) ↔ s ∈ HH \ catG := by
  constructor
  · rintro ⟨g, hg⟩
    exact adm_mem hg
  · rintro ⟨hs, hc⟩
    have hs' : 1 < s.re := hs
    have hp : s ∉ Pinch := fun hp => hc (mem_catG_iff.mpr ⟨hs', hp⟩)
    obtain ⟨κ, hκ⟩ := exists_slope_not_mem_cuts hp
    let γ : C(unitInterval, ℂ) :=
      ⟨fun t => s + ((2 * (1 - (t : ℝ)) : ℝ) : ℂ) * slantDir κ, by fun_prop⟩
    have hre (t : unitInterval) : (γ t).re = s.re + 2 * (1 - (t : ℝ)) := by
      simp [γ, slantDir]
    have hγ : ∀ t, γ t ∈ HH \ catG := by
      intro t
      refine ⟨?_, ?_⟩
      · show 1 < (γ t).re
        rw [hre]; linarith [t.2.2]
      · intro ht
        have hcut := add_not_mem_cuts hκ (t := 2 * (1 - (t : ℝ))) (by linarith [t.2.2])
        apply hcut
        exact mem_iUnion₂.mpr ⟨γ t, (mem_catG_iff.mp ht).2, 0, le_rfl, by simp [γ]⟩
    have h0 : 2 < (γ 0).re := by rw [hre]; simp; linarith
    obtain ⟨f, hf, hf0⟩ := hcont γ hγ h0
    refine ⟨f 1, γ, hγ, h0, ?_, f, hf, hf0, EventuallyEq.rfl⟩
    simp [γ]

/-- Every positive-radius disc on `Re v = 1` meets the admissible region. -/
theorem exists_adm_near {F : ℂ → ℂ}
    (hex : ∀ s ∈ HH \ catG, ∃ g : ℂ → ℂ, Adm F g s) :
    ∀ y r : ℝ, 0 < r → ∃ (s : ℂ) (g : ℂ → ℂ),
      s ∈ ball (1 + (y : ℂ) * I) r ∧ Adm F g s := by
  intro y r hr
  have hV : IsOpen (ball (1 + (y : ℂ) * I) r ∩ HH) :=
    isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hne : (ball (1 + (y : ℂ) * I) r ∩ HH).Nonempty := by
    refine ⟨(1 + (y : ℂ) * I) + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_eq]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : 0 < r / 2)]
      linarith
    · show 1 < ((1 + (y : ℂ) * I) + ((r / 2 : ℝ) : ℂ)).re
      simp; linarith
  obtain ⟨w, ⟨hwb, hwH⟩, hwP⟩ := exists_not_pinch hV hne
  obtain ⟨g, hg⟩ := hex w ⟨hwH, not_catG_of_not_pinch hwP⟩
  exact ⟨w, g, hwb, hg⟩

end GoldbachBoundaries.HInf.Follow
