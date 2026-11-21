import PrimePairNB.ThmA.Defs

/-!
# Analytic continuation along paths (general; no RH)

Germ-chain continuation (`IsContinuationAlong`, `Defs.lean`). Three lemmas (uniqueness,
existence for uniform germ families, concatenation; proved in `Fill/<name>.lean`) and
proofs of reparametrisation, restriction to an initial piece, and preservation of a uniform family
along a continuation (`continuationAlong_preserve`, in `Assembly.lean`). All general. TauCeti's
`IsAnalyticContinuationAlong` has the same shape.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-! ### Real proofs -/

theorem concatPath_zero (γ₁ γ₂ : C(unitInterval, ℂ)) (h : γ₂ 0 = γ₁ 1) :
    concatPath γ₁ γ₂ h 0 = γ₁ 0 :=
  Path.source _

theorem concatPath_one (γ₁ γ₂ : C(unitInterval, ℂ)) (h : γ₂ 0 = γ₁ 1) :
    concatPath γ₁ γ₂ h 1 = γ₂ 1 :=
  Path.target _

theorem concatPath_mem (γ₁ γ₂ : C(unitInterval, ℂ)) (h : γ₂ 0 = γ₁ 1) (t : unitInterval) :
    concatPath γ₁ γ₂ h t ∈ range γ₁ ∪ range γ₂ := by
  have := Path.trans_range (⟨γ₁, rfl, rfl⟩ : Path (γ₁ 0) (γ₁ 1)) (⟨γ₂, h, rfl⟩ : Path (γ₁ 1) (γ₂ 1))
  have hmem : concatPath γ₁ γ₂ h t ∈
      range ((⟨γ₁, rfl, rfl⟩ : Path (γ₁ 0) (γ₁ 1)).trans (⟨γ₂, h, rfl⟩ : Path (γ₁ 1) (γ₂ 1))) :=
    ⟨t, rfl⟩
  rw [this] at hmem
  exact hmem

/-- Reparametrisation of a continuation by a continuous self-map of `[0,1]`. -/
theorem continuationAlong_comp {γ : C(unitInterval, ℂ)} {f : unitInterval → ℂ → ℂ}
    (hf : IsContinuationAlong γ f) (m : C(unitInterval, unitInterval)) :
    IsContinuationAlong (γ.comp m) (fun t => f (m t)) where
  analyticAt t := hf.analyticAt (m t)
  locallyEq t := (m.continuous.tendsto t).eventually (hf.locallyEq (m t))

theorem scaleMap_zero (t : unitInterval) : scaleMap t 0 = 0 := by
  ext; simp [scaleMap]

theorem scaleMap_one (t : unitInterval) : scaleMap t 1 = t := by
  ext; simp [scaleMap]

theorem scaleMap_le (t s : unitInterval) : scaleMap t s ≤ t := by
  show (s : ℝ) * t ≤ t
  exact mul_le_of_le_one_left t.2.1 s.2.2

/-- The germ reached at time `t` is a terminal germ along the initial piece `γ|[0,t]`
(reparametrised to `[0,1]`). -/
theorem isTerminalGerm_restrict {F : ℂ → ℂ} {γ : C(unitInterval, ℂ)} {f : unitInterval → ℂ → ℂ}
    (hf : IsContinuationAlong γ f) (h0 : f 0 =ᶠ[𝓝 (γ 0)] F) (t : unitInterval) :
    ∃ δ : C(unitInterval, ℂ), δ 0 = γ 0 ∧ δ 1 = γ t ∧ (∀ s, ∃ t' : unitInterval, t' ≤ t ∧ δ s = γ t') ∧
      IsTerminalGerm F δ (f t) := by
  refine ⟨γ.comp (scaleMap t), ?_, ?_, fun s => ⟨scaleMap t s, scaleMap_le t s, rfl⟩,
    fun s => f (scaleMap t s), continuationAlong_comp hf (scaleMap t), ?_, ?_⟩
  · simp [scaleMap_zero]
  · simp [scaleMap_one]
  · simpa [scaleMap_zero] using h0
  · simp [scaleMap_one]

/-- A function analytic along the whole path is its own continuation. -/
theorem isTerminalGerm_of_analyticAt {g F : ℂ → ℂ} {γ : C(unitInterval, ℂ)}
    (hF : ∀ t, AnalyticAt ℂ F (γ t)) (h0 : F =ᶠ[𝓝 (γ 0)] g) : IsTerminalGerm g γ F :=
  ⟨fun _ => F, ⟨hF, fun _ => Eventually.of_forall fun _ => EventuallyEq.rfl⟩, h0, EventuallyEq.rfl⟩

/-- First exit time of a path from an open set. -/
theorem exists_firstExit (γ : C(unitInterval, ℂ)) {U : Set ℂ} (hU : IsOpen U) (h0 : γ 0 ∈ U)
    (h : ∃ t, γ t ∉ U) : ∃ t₁, γ t₁ ∉ U ∧ 0 < t₁ ∧ ∀ t < t₁, γ t ∈ U := by
  set A : Set unitInterval := {t | γ t ∉ U} with hAdef
  have hA : IsClosed A := hU.isClosed_compl.preimage γ.continuous
  have hmem : sInf A ∈ A := hA.csInf_mem h (OrderBot.bddBelow A)
  refine ⟨sInf A, hmem, ?_, fun t ht => ?_⟩
  · rcases (show (0 : unitInterval) ≤ sInf A from (sInf A).2.1).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hmem
      exact absurd h0 hmem
  · by_contra hc
    exact absurd (csInf_le (OrderBot.bddBelow A) hc) (not_le.mpr ht)

/-- A property holding near `t₁ > 0` holds at some earlier time. -/
theorem exists_lt_of_eventually {t₁ : unitInterval} (h : 0 < t₁) {p : unitInterval → Prop}
    (hp : ∀ᶠ t in 𝓝 t₁, p t) : ∃ t < t₁, p t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hp
  have h1 : (0 : ℝ) < t₁ := h
  set x : ℝ := max 0 ((t₁ : ℝ) - δ / 2) with hx
  have hx0 : 0 ≤ x := le_max_left _ _
  have hx1 : x ≤ 1 := max_le zero_le_one (by linarith [t₁.2.2])
  refine ⟨⟨x, hx0, hx1⟩, ?_, hball ?_⟩
  · show x < (t₁ : ℝ)
    exact max_lt h1 (by linarith)
  · show dist x (t₁ : ℝ) < δ
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : (t₁ : ℝ) - δ / 2 ≤ x := le_max_right _ _
      linarith
    · have : x < (t₁ : ℝ) := max_lt h1 (by linarith)
      linarith

end GoldbachBoundaries.ThmA
