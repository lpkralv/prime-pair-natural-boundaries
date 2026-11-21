import PrimePairNB.ThmA.Assembly

/-!
# The theorem on `G`: the statements

The statements `isTerminalGerm_trans`, `thm_A_continuation`, `thm_A_local`, `thm_G_boundary`,
`rem_every_path` of `Statements.lean`, and the slant lemma `lem_slant_proof`, here named `*_proof` in the
namespace `GoldbachBoundaries.ThmA` (so `IsGoodSlant` is `ThmA.IsGoodSlant`, which has the same body
as `Statements.lean`'s). Each proof is assembled from the lemmas of `G13_Continuation` to
`G20_Branches`, which are proved in `Fill/<name>.lean` and collected by `Assembly.lean`.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each.

`Statements.lean` imports this file and closes each of its five statements with `exact`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-! ## the slant lemma -/

set_option linter.unusedVariables false in
theorem lem_slant_proof (hRH : RiemannHypothesis) : ∃ κ : ℝ, IsGoodSlant κ := by
  obtain ⟨κ, h0, h1, h2⟩ := exists_goodSlant_of_countable catalogue_countable
  exact ⟨κ, h0, h1, h2⟩

/-! ## Concatenation -/

theorem isTerminalGerm_trans_proof {F g g' : ℂ → ℂ} {γ₁ γ₂ : C(unitInterval, ℂ)}
    (h₁ : IsTerminalGerm F γ₁ g) (h₁₂ : γ₂ 0 = γ₁ 1) (h₂ : IsTerminalGerm g γ₂ g') :
    ∃ γ : C(unitInterval, ℂ), γ 0 = γ₁ 0 ∧ γ 1 = γ₂ 1 ∧
      (∀ t, γ t ∈ range γ₁ ∪ range γ₂) ∧ IsTerminalGerm F γ g' := by
  obtain ⟨f₁, hf₁, h0₁, hg₁⟩ := h₁
  obtain ⟨f₂, hf₂, h0₂, hg₂⟩ := h₂
  have hlink : f₂ 0 =ᶠ[𝓝 (γ₂ 0)] f₁ 1 := by
    rw [h₁₂] at h0₂ ⊢
    exact h0₂.trans hg₁
  obtain ⟨f, hf, hf0, hf1⟩ := isContinuationAlong_concat h₁₂ hf₁ hf₂ hlink
  refine ⟨concatPath γ₁ γ₂ h₁₂, concatPath_zero _ _ _, concatPath_one _ _ _, concatPath_mem _ _ _,
    f, hf, ?_, ?_⟩
  · rw [hf0, concatPath_zero]; exact h0₁
  · rw [hf1, concatPath_one]; exact hg₂

/-- Continuing an admissible germ along a further path in `HH \ catalogue` gives an admissible germ. -/
theorem admissible_continuation' {g g' : ℂ → ℂ} {s₁ : ℂ} (hg : IsAdmissibleGerm g s₁)
    (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s₁) (hγ : ∀ t, γ t ∈ HH \ catalogue)
    (hg' : IsTerminalGerm g γ g') : IsAdmissibleGerm g' (γ 1) := by
  obtain ⟨γ₁, hγ₁, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, hδr, hδ⟩ := isTerminalGerm_trans_proof hterm (hγ0.trans h1.symm) hg'
  refine ⟨δ, fun t => ?_, by rw [hδ0]; exact h2, hδ1, hδ⟩
  rcases hδr t with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]; exact hγ₁ u
  · rw [← hu]; exact hγ u

/-- Complements of a point are codiscrete. -/
theorem eventually_codiscreteWithin_notMem_singleton (U : Set ℂ) (α : ℂ) :
    ∀ᶠ z in codiscreteWithin U, z ∉ ({α} : Set ℂ) := by
  rw [Filter.Eventually, mem_codiscreteWithin]
  intro x _
  rw [disjoint_principal_right]
  by_cases hx : x = α
  · subst hx
    filter_upwards [self_mem_nhdsWithin] with z hz hz'
    exact hz (by simpa using hz'.2)
  · filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hx)] with z hz hz'
    exact hz (by simpa using hz'.2)

/-! ## the main theorem on `G`, sentences 1–2 -/

theorem thm_A_continuation_proof (hRH : RiemannHypothesis) :
    ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ HH \ catalogue) → 2 < (γ 0).re →
      ContinuesAlong G γ := by
  intro γ hγ h2
  obtain ⟨κ, hκ⟩ := lem_slant_proof hRH
  have hP := isPrincipalSheet_Gnat hRH hκ
  obtain ⟨f, hf, hf0, -⟩ :=
    exists_continuationAlong_of_uniform (isBranch_uniform hκ hP) hγ (isBranch_G hP h2)
  exact ⟨f, hf, hf0⟩

/-! ## the main theorem on `G`, local form of every branch -/

theorem thm_A_local_proof (hRH : RiemannHypothesis) :
    ∃ X : ℂ → ℂ → ℂ,
      (∀ α ∈ catalogue, DifferentiableOn ℂ (X α) HH ∧ X α α = 0) ∧
      HasCatalogueValues (fun α => deriv (X α) α) ∧
      (∀ α ∈ catalogue, deriv (X α) α ≠ 0) ∧
      ∀ κ : ℝ, IsGoodSlant κ → ∀ α ∈ catalogue, ∃ r : ℝ, 0 < r ∧
        ∀ s₁ ∈ slitDisc (slantDir κ) α r, ∀ g : ℂ → ℂ, IsAdmissibleGerm g s₁ →
          ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball α r) ∧
            g =ᶠ[𝓝 s₁] fun s => X α s * logAt (slantDir κ) α s + h s := by
  refine ⟨X, fun α hα => ⟨X_differentiableOn hα, X_self α⟩, (X_deriv_spec hRH).1,
    (X_deriv_spec hRH).2, ?_⟩
  intro κ hκ α hα
  have hP := isPrincipalSheet_Gnat hRH hκ
  obtain ⟨r, hr, hrα, hsub, H, hH, hEq⟩ := hP.local_form α hα
  refine ⟨r, hr, fun s₁ hs₁ g hg => ?_⟩
  obtain ⟨-, hev⟩ := isBranch_of_admissible hκ hP hg
  obtain ⟨m, hm, hgm⟩ := hev.self_of_nhds (hsub hs₁)
  have hmA := MSpan_analyticOn hm
  refine ⟨fun s => H s + m s, fun z hz =>
    ((hH z hz).add (hmA z (ball_subset_HH hrα hz))).differentiableAt.differentiableWithinAt, ?_⟩
  have hopen := (slitDisc_facts κ hr hrα).1
  filter_upwards [hgm, hopen.mem_nhds hs₁] with s hs1 hs2
  rw [hs1, hEq hs2]; ring

/-! ## the boundary theorem for `G` -/

theorem thm_G_boundary_proof (hRH : RiemannHypothesis) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : IsAdmissibleGerm g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  rintro ⟨-, f, hfm, hfg⟩
  obtain ⟨κ, hκ⟩ := lem_slant_proof hRH
  have hP := isPrincipalSheet_Gnat hRH hκ
  have hs₁m := admissible_mem hg
  obtain ⟨f', hf'm, hf'g, hf'an⟩ := exists_meromorphic_update hfm hfg
  -- step 1: a catalogue point `α` in the disc, its local model, a small disc about it
  obtain ⟨α, hα, hαD⟩ := exists_catalogue_mem_ball y hr
  obtain ⟨rα, hrα, hrαle, hsub, H, hH, hEq⟩ := hP.local_form α hα
  obtain ⟨ε₁, hε₁, hε₁an⟩ : ∃ ε₁ > 0, ∀ z ∈ ball α ε₁, z ≠ α → AnalyticAt ℂ f' z := by
    have h := (hf'm α hαD).eventually_analyticAt
    rw [eventually_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
    exact ⟨ε, hε, fun z hz hne => hball z hz hne⟩
  obtain ⟨ε₂, hε₂, hε₂D⟩ := Metric.isOpen_iff.mp isOpen_ball α hαD
  set ε₀ := min rα (min ε₁ ε₂) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hrα (lt_min hε₁ hε₂)
  have hε₀r : ε₀ ≤ rα := min_le_left _ _
  have hε₀1 : ε₀ ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀2 : ε₀ ≤ ε₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hε₀α : ε₀ ≤ α.re - 1 := hε₀r.trans hrαle
  -- step 2: a path from `s₁` to the slit disc avoiding the poles of `f` and `𝒞`
  set D := ball (1 + (y : ℂ) * I) r with hD
  set S : Set ℂ := {z | ¬ AnalyticAt ℂ f' z} ∪ catalogue with hS
  have hUo : IsOpen (D ∩ HH) := isOpen_ball.inter (isOpen_halfPlane 1)
  have hUc : IsConnected (D ∩ HH) :=
    ⟨⟨s₁, hs₁, hs₁m.1⟩, ((convex_ball _ _).inter (convex_halfSpace_re_gt (1 : ℝ))).isPreconnected⟩
  have hSc : ∀ᶠ z in codiscreteWithin (D ∩ HH), z ∉ S := by
    have h1 : ∀ᶠ z in codiscreteWithin (D ∩ HH), AnalyticAt ℂ f' z :=
      codiscreteWithin_mono inter_subset_left hf'an
    have h2 : ∀ᶠ z in codiscreteWithin (D ∩ HH), z ∉ catalogue :=
      codiscreteWithin_mono inter_subset_right catalogue_locallyFinite.2.1
    filter_upwards [h1, h2] with z hz1 hz2
    rintro (h | h)
    · exact h hz1
    · exact hz2 h
  have hs₁S : s₁ ∉ S := by
    rintro (h | h)
    · exact h ((admissible_analyticAt hg).congr hf'g.symm)
    · exact hs₁m.2 h
  set V := slitDisc (slantDir κ) α ε₀ with hV
  have hVo : IsOpen V := (slitDisc_facts κ hε₀pos hε₀α).1
  have hVne : V.Nonempty := by
    obtain ⟨s, hs, -⟩ := exists_mem_slitDisc κ (α := α) hε₀pos
    exact ⟨s, hs⟩
  have hVsub : V ⊆ slitDisc (slantDir κ) α rα := slitDisc_mono hε₀r
  have hVU : V ⊆ D ∩ HH := fun s hs =>
    ⟨hε₂D (ball_subset_ball hε₀2 hs.1), (Omega_subset (hsub (hVsub hs))).1⟩
  obtain ⟨s₂, hs₂V, -, γ, hγ0, hγ1, hγ⟩ :=
    exists_path_into hUo hUc hSc ⟨hs₁, hs₁m.1⟩ hs₁S hVo hVne hVU
  have hterm : IsTerminalGerm g γ f' := isTerminalGerm_of_analyticAt
    (fun t => by by_contra h; exact (hγ t).2 (Or.inl h)) (by rw [hγ0]; exact hf'g)
  have hadm : IsAdmissibleGerm f' (γ 1) := admissible_continuation' hg γ hγ0
    (fun t => ⟨(hγ t).1.2, fun h => (hγ t).2 (Or.inr h)⟩) hterm
  rw [hγ1] at hadm
  -- step 3: near `s₂` the germ is `G^♮ + ∑ ν M`, hence `X_α Log_α + (holomorphic)`
  obtain ⟨-, hev⟩ := isBranch_of_admissible hκ hP hadm
  obtain ⟨m, hm, hfm⟩ := hev.self_of_nhds (hsub (hVsub hs₂V))
  have hmA := MSpan_analyticOn hm
  have hballHH : ball α ε₀ ⊆ HH := ball_subset_HH hε₀α
  have hX := (X_differentiableOn hα).analyticOnNhd (isOpen_halfPlane 1)
  -- step 4: continuity across the cut contradicts the jump `2πi X_α ≢ 0`
  refine no_analytic_across_log (κ := κ) hε₀pos hε₀α (X₀ := X α) (H := fun s => H s + m s)
    (F := f') (fun z hz => hX z (hballHH hz)) ((X_deriv_spec hRH).2 α hα)
    (fun z hz => (hH z (ball_subset_ball hε₀r hz)).add (hmA z (hballHH hz)))
    (fun z hz hne => hε₁an z (ball_subset_ball hε₀1 hz) hne) hs₂V ?_
  have hopen := (slitDisc_facts κ hrα hrαle).1
  filter_upwards [hfm, hopen.mem_nhds (hVsub hs₂V)] with s hs1 hs2
  rw [hs1, hEq hs2]; ring

/-! ## the every-path statement -/

theorem rem_every_path_proof (hRH : RiemannHypothesis) :
    ∀ γ : C(unitInterval, ℂ), 2 < (γ 0).re → ContinuesAlong G γ → ∀ t, γ t ∈ HH \ catalogue := by
  intro γ h2 hcont
  obtain ⟨f, hf, hf0⟩ := hcont
  by_contra hcon'
  have hcon : ∃ t, γ t ∉ HH \ catalogue := not_forall.mp hcon'
  obtain ⟨κ, hκ⟩ := lem_slant_proof hRH
  have hP := isPrincipalSheet_Gnat hRH hκ
  have hUo : IsOpen (HH \ catalogue) := catalogue_locallyFinite.2.2
  have h0U : γ 0 ∈ HH \ catalogue :=
    ⟨show (1 : ℝ) < (γ 0).re by linarith, fun h => by linarith [re_le_two_of_mem_catalogue h]⟩
  obtain ⟨t₁, ht₁, ht₁0, hbefore⟩ := exists_firstExit γ hUo h0U hcon
  -- germs before the exit time are admissible
  have hadm : ∀ t, t < t₁ → IsAdmissibleGerm (f t) (γ t) := by
    intro t ht
    obtain ⟨δ, hδ0, hδ1, hδr, hδ⟩ := isTerminalGerm_restrict hf hf0 t
    refine ⟨δ, fun s => ?_, by rw [hδ0]; exact h2, hδ1, hδ⟩
    obtain ⟨t', ht', hδs⟩ := hδr s
    rw [hδs]; exact hbefore t' (lt_of_le_of_lt ht' ht)
  obtain ⟨ρ, hρ, hρan⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hf.analyticAt t₁).eventually_analyticAt
  have hleft : ∀ ε > 0, ∃ t' < t₁, γ t' ∈ ball (γ t₁) ε ∧ f t' =ᶠ[𝓝 (γ t')] f t₁ := by
    intro ε hε
    exact exists_lt_of_eventually ht₁0
      (((γ.continuous.tendsto t₁).eventually_mem (ball_mem_nhds _ hε)).and (hf.locallyEq t₁))
  by_cases hH : γ t₁ ∈ HH
  · -- the path would pass through a catalogue point: monodromy
    have hα : γ t₁ ∈ catalogue := by
      by_contra h; exact ht₁ ⟨hH, h⟩
    set α := γ t₁ with hαdef
    obtain ⟨rα, hrα, hrαle, hsub, H, hH', hEq⟩ := hP.local_form α hα
    set ε₀ := min rα ρ with hε₀
    have hε₀pos : 0 < ε₀ := lt_min hrα hρ
    have hε₀r : ε₀ ≤ rα := min_le_left _ _
    have hε₀ρ : ε₀ ≤ ρ := min_le_right _ _
    have hε₀α : ε₀ ≤ α.re - 1 := hε₀r.trans hrαle
    obtain ⟨t', ht't, hγt', hgerm⟩ := hleft ε₀ hε₀pos
    have hγt'U := hbefore t' ht't
    have hne : γ t' ∉ ({α} : Set ℂ) := fun h => hγt'U.2 ((mem_singleton_iff.mp h) ▸ hα)
    have hVo : IsOpen (slitDisc (slantDir κ) α ε₀) := (slitDisc_facts κ hε₀pos hε₀α).1
    have hVne : (slitDisc (slantDir κ) α ε₀).Nonempty := by
      obtain ⟨s, hs, -⟩ := exists_mem_slitDisc κ (α := α) hε₀pos
      exact ⟨s, hs⟩
    obtain ⟨s₃, hs₃V, -, δ, hδ0, hδ1, hδ⟩ := exists_path_into isOpen_ball
      ⟨⟨α, mem_ball_self hε₀pos⟩, (convex_ball α ε₀).isPreconnected⟩
      (eventually_codiscreteWithin_notMem_singleton _ α) hγt' hne hVo hVne (fun s hs => hs.1)
    have hballHH : ball α ε₀ ⊆ HH := ball_subset_HH hε₀α
    have hδU : ∀ s, δ s ∈ HH \ catalogue := by
      intro s
      refine ⟨hballHH (hδ s).1, fun hc => ?_⟩
      have hneα : δ s ≠ α := fun h => (hδ s).2 (mem_singleton_iff.mpr h)
      by_cases hcut : δ s ∈ cut (slantDir κ) α
      · exact hneα (catalogue_inter_cut hκ hα hcut hc)
      · exact (Omega_subset (hsub ⟨ball_subset_ball hε₀r (hδ s).1, hcut⟩)).2 hc
    have hterm : IsTerminalGerm (f t') δ (f t₁) := isTerminalGerm_of_analyticAt
      (fun s => hρan _ (ball_subset_ball hε₀ρ (hδ s).1)) (by rw [hδ0]; exact hgerm.symm)
    have hadm' := admissible_continuation' (hadm t' ht't) δ hδ0 hδU hterm
    rw [hδ1] at hadm'
    obtain ⟨-, hev⟩ := isBranch_of_admissible hκ hP hadm'
    obtain ⟨m, hm, hfm⟩ := hev.self_of_nhds (hsub (slitDisc_mono hε₀r hs₃V))
    have hmA := MSpan_analyticOn hm
    have hX := (X_differentiableOn hα).analyticOnNhd (isOpen_halfPlane 1)
    refine no_analytic_across_log (κ := κ) hε₀pos hε₀α (X₀ := X α) (H := fun s => H s + m s)
      (F := f t₁) (fun z hz => hX z (hballHH hz)) ((X_deriv_spec hRH).2 α hα)
      (fun z hz => (hH' z (ball_subset_ball hε₀r hz)).add (hmA z (hballHH hz)))
      (fun z hz _ => hρan z (ball_subset_ball hε₀ρ hz)) hs₃V ?_
    have hopen := (slitDisc_facts κ hrα hrαle).1
    filter_upwards [hfm, hopen.mem_nhds (slitDisc_mono hε₀r hs₃V)] with s hs1 hs2
    rw [hs1, hEq hs2]; ring
  · -- the path would cross `σ = 1`: the germ there would extend to a disc on the line
    have hle : (γ t₁).re ≤ 1 := by
      have : ¬ (1 < (γ t₁).re) := hH
      exact not_lt.mp this
    have hge : 1 ≤ (γ t₁).re := by
      by_contra hlt'
      have hlt : (γ t₁).re < 1 := not_le.mp hlt'
      obtain ⟨t', ht't, hγt', -⟩ := hleft (1 - (γ t₁).re) (by linarith)
      have h1 : (1 : ℝ) < (γ t').re := (hbefore t' ht't).1
      have h3 : |(γ t').re - (γ t₁).re| ≤ ‖γ t' - γ t₁‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h4 : ‖γ t' - γ t₁‖ < 1 - (γ t₁).re := by rw [← dist_eq_norm]; exact hγt'
      linarith [(abs_lt.mp (lt_of_le_of_lt h3 h4)).2]
    have hre : (γ t₁).re = 1 := le_antisymm hle hge
    set y := (γ t₁).im with hy
    have hγeq : γ t₁ = 1 + (y : ℂ) * I := Complex.ext (by simp [hre]) (by simp [hy])
    obtain ⟨t', ht't, hγt', hgerm⟩ := hleft ρ hρ
    rw [hγeq] at hγt' hρan
    exact thm_G_boundary_proof hRH (hadm t' ht't) y ρ hρ hγt'
      ⟨hγt', f t₁, fun z hz => (hρan z hz).meromorphicAt,
        hgerm.symm.filter_mono nhdsWithin_le_nhds⟩

/-! ## the domain corollary -/

end GoldbachBoundaries.ThmA
