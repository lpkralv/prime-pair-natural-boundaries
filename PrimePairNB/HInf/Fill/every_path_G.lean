import PrimePairNB.HInf.Fill.boundary_G

/-!
# `every_path_G`

The germ `f t` along a continuation may pass over a catalogue point, so it need not be admissible at `γ t`. The invariant
`PathGood` is what does hold at every `t`: on a disc about `γ t` inside `σ > 1`, the germ is analytic, and admissible at
each point off `catG`. It holds on a clopen set of times, hence at all of them.

Closed: at a limit time `t`, the germ is admissible at points near `γ t`, so `boundary_G` keeps `γ t` off `σ = 1`. In a disc
that meets `catG` at most at `γ t` the rest of the disc is path connected, so admissibility spreads over it.

`no_extension_any_path_G` and `every_path_stays_G` read off the same invariant.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- On a disc about `p` inside `σ > 1`, `h` is analytic, and admissible at each point off `catG`. -/
def PathGood (h : ℂ → ℂ) (p : ℂ) : Prop :=
  ∃ ρ > 0, ball p ρ ⊆ HH ∧ AnalyticOnNhd ℂ h (ball p ρ) ∧ ∀ w ∈ ball p ρ, w ∉ catG → AdmG h w

/-- An analytic admissible germ stays admissible along a joined set off the catalogue. -/
lemma admG_of_joinedIn {h : ℂ → ℂ} {a b : ℂ} {T : Set ℂ} (ha : AdmG h a) (hj : JoinedIn T a b)
    (hT : T ⊆ HH \ catG) (han : ∀ z ∈ T, AnalyticAt ℂ h z) : AdmG h b := by
  have hmem := hj.somePath_mem
  set p := hj.somePath
  have h1 : (p.toContinuousMap : C(unitInterval, ℂ)) 1 = b := p.target
  have h0 : (p.toContinuousMap : C(unitInterval, ℂ)) 0 = a := p.source
  have := admG_trans ha p.toContinuousMap h0 (fun t => hT (hmem t))
    (ThmA.isTerminalGerm_of_analyticAt (fun t => han _ (hmem t)) EventuallyEq.rfl)
  rwa [h1] at this

/-- There is a point off `Σ + Σ` in every non-empty open set. -/
lemma exists_not_pinch {V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty) : ∃ w ∈ V, w ∉ Pinch := by
  obtain ⟨w, hw, hwc⟩ := (pinch_countable.dense_compl ℝ).inter_open_nonempty V hV hne
  exact ⟨w, hw, hwc⟩

lemma not_catG_of_not_pinch {w : ℂ} (h : w ∉ Pinch) : w ∉ catG := fun hc => h (mem_catG_iff.mp hc).2

/-- **The invariant holds at every time.** -/
theorem pathGood_all (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) {f : unitInterval → ℂ → ℂ} (hf : IsContinuationAlong γ f)
    (hf0 : f 0 =ᶠ[𝓝 (γ 0)] G) (t : unitInterval) : PathGood (f t) (γ t) := by
  set A : Set unitInterval := {t | PathGood (f t) (γ t)} with hA
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
    have heq : ∀ w ∈ ball (γ 0) (min ρ₁ ((γ 0).re - 2)), f 0 =ᶠ[𝓝 w] G := by
      intro w hw
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hb z (ball_subset_ball (min_le_left _ _) hz)
    refine ⟨min ρ₁ ((γ 0).re - 2), lt_min hρ₁ hpos, fun w hw => ?_,
      fun w hw => (ThmA.G_analyticAt (hre w hw)).congr (heq w hw).symm, fun w hw _ => ?_⟩
    · show 1 < w.re
      linarith [hre w hw]
    · exact admG_congr (admG_of_two_lt (hre w hw)) (heq w hw).symm
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
      fun w hw hwc => admG_congr (had w (hin w hw) hwc) (heq w hw).symm⟩
  -- closed
  have hAc : IsClosed A := by
    apply isClosed_of_closure_subset
    intro t ht
    obtain ⟨ρ, hρ, han⟩ := Metric.eventually_nhds_iff_ball.mp (hf.analyticAt t).eventually_analyticAt
    have hnear : ∀ ε > 0, ∃ w ∈ ball (γ t) ε, AdmG (f t) w := by
      intro ε hε
      obtain ⟨t', ht'A, ht'b, hloc⟩ := (mem_closure_iff_frequently.mp ht).and_eventually
        (((γ.continuous.tendsto t).eventually_mem (ball_mem_nhds _ hε)).and (hf.locallyEq t)) |>.exists
      obtain ⟨ρ', hρ', -, -, had⟩ := ht'A
      obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff_ball.mp hloc
      obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball _ ht'b
      obtain ⟨w, hw, hwP⟩ := exists_not_pinch (V := ball (γ t') (min ρ' (min ρ₁ ρ₂))) isOpen_ball
        ⟨_, mem_ball_self (lt_min hρ' (lt_min hρ₁ hρ₂))⟩
      refine ⟨w, hsub (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hw),
        admG_congr (had w (ball_subset_ball (min_le_left _ _) hw) (not_catG_of_not_pinch hwP)) ?_⟩
      filter_upwards [isOpen_ball.mem_nhds hw] with z hz
      exact hb z (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz)
    have hge : 1 ≤ (γ t).re := by
      by_contra hlt'
      have hlt : (γ t).re < 1 := not_le.mp hlt'
      obtain ⟨w, hw, had⟩ := hnear (1 - (γ t).re) (by linarith)
      have h1 : (1 : ℝ) < w.re := (admG_mem had).1
      have h3 : |w.re - (γ t).re| ≤ ‖w - γ t‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h4 : ‖w - γ t‖ < 1 - (γ t).re := by rw [← dist_eq_norm]; exact hw
      linarith [(abs_lt.mp (lt_of_le_of_lt h3 h4)).2]
    have hgt : 1 < (γ t).re := by
      refine lt_of_le_of_ne hge fun hre => ?_
      set y := (γ t).im with hy
      have hγeq : γ t = 1 + (y : ℂ) * I := Complex.ext (by simp [← hre]) (by simp [hy])
      obtain ⟨w, hw, had⟩ := hnear ρ hρ
      rw [hγeq] at hw han
      exact boundary_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 had y ρ hρ hw
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
    exact admG_of_joinedIn had (hpc.joinedIn w' ⟨hw', (admG_mem had).2⟩ w ⟨hw, hwc⟩)
      (fun z hz => ⟨hHH hz.1, hz.2⟩) (fun z hz => han z (ball_subset_ball h1 hz.1))
  have huniv : A = univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨0, h0A⟩
  have : t ∈ A := huniv ▸ mem_univ t
  exact this

/-- A germ reached from `σ > 2` along any path in `ℂ`, ending off the catalogue,
is admissible. The path may pass through catalogue points on a holomorphic germ, so this differs from
`Statements.rem_every_path`, whose "the path stays in `ℍ ∖ 𝒞`" needs `X_α ≠ 0` at every catalogue point, known under RH
only. -/
theorem every_path_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm G γ g) (h1 : γ 1 ∉ catG) :
    AdmG g (γ 1) := by
  obtain ⟨f, hf, hf0, hg1⟩ := hg
  obtain ⟨ρ, hρ, -, -, had⟩ := pathGood_all hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 h0 hf hf0 1
  exact admG_congr (had _ (mem_ball_self hρ) h1) hg1.symm

end GoldbachBoundaries.HInf.Fill
