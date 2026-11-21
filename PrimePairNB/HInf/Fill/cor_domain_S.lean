import PrimePairNB.HInf.Fill.boundary_S

/-!
# `cor_domain_S`

As `cor_domain_G`: move the germ along a path in the component of `W ∩ {σ > 0}` to a disc on the line `σ = 0`, and apply
`boundary_S` there. `ThmA.exists_component_reaching_line` is about `σ = 1`, so it is applied to `W` shifted by `1`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `ThmA.exists_component_reaching_line` for the line `σ = 0`. -/
lemma exists_component_reaching_line_zero {W : Set ℂ} (hWo : IsOpen W) (hWc : IsConnected W)
    (hWL : (W ∩ {s : ℂ | s.re = 0}).Nonempty) {s₁ : ℂ} (hs₁ : s₁ ∈ W) (hs₁H : s₁ ∈ halfPlane 0) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ U ⊆ W ∩ halfPlane 0 ∧ s₁ ∈ U ∧
      ∃ y r : ℝ, 0 < r ∧ ball ((y : ℂ) * I) r ⊆ W ∧ ball ((y : ℂ) * I) r ∩ halfPlane 0 ⊆ U := by
  set W' : Set ℂ := (fun z : ℂ => z - 1) ⁻¹' W with hW'
  have hW'o : IsOpen W' := hWo.preimage (by fun_prop)
  have himg : (fun z : ℂ => z + 1) '' W = W' := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      show w + 1 - 1 ∈ W
      simpa using hw
    · intro hz
      exact ⟨z - 1, hz, by simp⟩
  have hW'c : IsConnected W' := by
    rw [← himg]
    exact hWc.image _ (by fun_prop)
  have hW'L : (W' ∩ lineOne).Nonempty := by
    obtain ⟨z, hz, hz0⟩ := hWL
    refine ⟨z + 1, by show z + 1 - 1 ∈ W; simpa using hz, ?_⟩
    have hz0' : z.re = 0 := hz0
    show (z + 1).re = 1
    simp [hz0']
  have hs₁' : s₁ + 1 ∈ W' := by show s₁ + 1 - 1 ∈ W; simpa using hs₁
  have hs₁H' : s₁ + 1 ∈ HH := by
    have h0 : (0 : ℝ) < s₁.re := hs₁H
    show (1 : ℝ) < (s₁ + 1).re
    simp
    linarith
  obtain ⟨U', hU'o, hU'c, hU's, hs₁U', y, r, hr, hbW, hbU⟩ :=
    ThmA.exists_component_reaching_line hW'o hW'c hW'L hs₁' hs₁H'
  have hball : ∀ z : ℂ, z ∈ ball ((y : ℂ) * I) r → z + 1 ∈ ball (1 + (y : ℂ) * I) r := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rwa [show z + 1 - (1 + (y : ℂ) * I) = z - (y : ℂ) * I by ring]
  refine ⟨(fun z : ℂ => z + 1) ⁻¹' U', hU'o.preimage (by fun_prop), ?_, ?_, hs₁U', y, r, hr, ?_, ?_⟩
  · have himg' : (fun z : ℂ => z - 1) '' U' = (fun z : ℂ => z + 1) ⁻¹' U' := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        show w - 1 + 1 ∈ U'
        simpa using hw
      · intro hz
        exact ⟨z + 1, hz, by simp⟩
    rw [← himg']
    exact hU'c.image _ (by fun_prop)
  · intro z hz
    have hz' := hU's hz
    refine ⟨by simpa using (show z + 1 - 1 ∈ W from hz'.1), ?_⟩
    have h1 : (1 : ℝ) < (z + 1).re := hz'.2
    show (0 : ℝ) < z.re
    simp at h1
    linarith
  · intro z hz
    have := hbW (hball z hz)
    simpa using (show z + 1 - 1 ∈ W from this)
  · intro z hz
    refine hbU ⟨hball z hz.1, ?_⟩
    have h0 : (0 : ℝ) < z.re := hz.2
    show (1 : ℝ) < (z + 1).re
    simp
    linarith

/-- Proof of `HInf.cor_domain_S` (paper, Theorem 8.2(b) for `S`). -/
theorem cor_domain_S (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : AdmS g s₁) {W : Set ℂ} (hWo : IsOpen W) (hWc : IsConnected W) (hWL : (W ∩ {s : ℂ | s.re = 0}).Nonempty)
    (hs₁ : s₁ ∈ W) : ¬ GermExtendsMeromorphically g s₁ W := by
  rintro ⟨-, f, hfm, hfg⟩
  have hs₁m := admS_mem hg
  obtain ⟨U, hUo, hUc, hUsub, hs₁U, y, r, hr, hball, hballU⟩ :=
    exists_component_reaching_line_zero hWo hWc hWL hs₁ hs₁m.1
  obtain ⟨f', hf'm, hf'g, hf'an⟩ := ThmA.exists_meromorphic_update hfm hfg
  set S : Set ℂ := {z | ¬ AnalyticAt ℂ f' z} ∪ catS with hS
  have hSc : ∀ᶠ z in codiscreteWithin U, z ∉ S := by
    have h1 : ∀ᶠ z in codiscreteWithin U, AnalyticAt ℂ f' z :=
      codiscreteWithin_mono (fun z hz => (hUsub hz).1) hf'an
    have h2 : ∀ᶠ z in codiscreteWithin U, z ∉ catS :=
      codiscreteWithin_mono (fun z hz => (hUsub hz).2) (codiscrete_not_catS hZ1 hH)
    filter_upwards [h1, h2] with z hz1 hz2
    rintro (h | h)
    · exact h hz1
    · exact hz2 h
  have hs₁S : s₁ ∉ S := by
    rintro (h | h)
    · exact h ((admS_analyticAt hg).congr hf'g.symm)
    · exact hs₁m.2 h
  have hVo : IsOpen (ball ((y : ℂ) * I) r ∩ halfPlane 0) := isOpen_ball.inter (isOpen_halfPlane 0)
  have hVne : (ball ((y : ℂ) * I) r ∩ halfPlane 0).Nonempty := by
    refine ⟨(y : ℂ) * I + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · show (0 : ℝ) < ((y : ℂ) * I + ((r / 2 : ℝ) : ℂ)).re
      simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, zero_add]
      linarith
  obtain ⟨s₃, hs₃V, -, δ, hδ0, hδ1, hδ⟩ := ThmA.exists_path_into hUo hUc hSc hs₁U hs₁S hVo hVne hballU
  have hterm : IsTerminalGerm g δ f' := ThmA.isTerminalGerm_of_analyticAt
    (fun t => by by_contra h; exact (hδ t).2 (Or.inl h)) (by rw [hδ0]; exact hf'g)
  have hadm := admS_trans hg δ hδ0
    (fun t => ⟨(hUsub (hδ t).1).2, fun h => (hδ t).2 (Or.inr h)⟩) hterm
  rw [hδ1] at hadm
  exact boundary_S hH hZ1 hZ2 hZ3 hZ4 hZ5 hadm y r hr hs₃V.1
    ⟨hs₃V.1, f', hf'm.mono_set hball, EventuallyEq.rfl⟩

end GoldbachBoundaries.HInf.Fill

