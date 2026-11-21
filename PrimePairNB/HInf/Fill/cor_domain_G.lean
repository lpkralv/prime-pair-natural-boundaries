import PrimePairNB.HInf.Fill.boundary_G

/-!
# `cor_domain_G`

Move the germ along a path in the component of `W ∩ {σ > 1}` to
a disc on the line, and apply `boundary_G` there.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- For `G`: no meromorphic extension over a connected open set that meets the line. -/
theorem cor_domain_G (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) {g : ℂ → ℂ}
    {s₁ : ℂ} (hg : AdmG g s₁) {W : Set ℂ} (hWo : IsOpen W) (hWc : IsConnected W) (hWL : (W ∩ lineOne).Nonempty)
    (hs₁ : s₁ ∈ W) : ¬ GermExtendsMeromorphically g s₁ W := by
  rintro ⟨-, f, hfm, hfg⟩
  have hs₁m := admG_mem hg
  obtain ⟨U, hUo, hUc, hUsub, hs₁U, y, r, hr, hball, hballU⟩ :=
    ThmA.exists_component_reaching_line hWo hWc hWL hs₁ hs₁m.1
  obtain ⟨f', hf'm, hf'g, hf'an⟩ := ThmA.exists_meromorphic_update hfm hfg
  set S : Set ℂ := {z | ¬ AnalyticAt ℂ f' z} ∪ catG with hS
  have hSc : ∀ᶠ z in codiscreteWithin U, z ∉ S := by
    have h1 : ∀ᶠ z in codiscreteWithin U, AnalyticAt ℂ f' z :=
      codiscreteWithin_mono (fun z hz => (hUsub hz).1) hf'an
    have h2 : ∀ᶠ z in codiscreteWithin U, z ∉ catG :=
      codiscreteWithin_mono (fun z hz => (hUsub hz).2) (codiscrete_not_catG hZ1 hH)
    filter_upwards [h1, h2] with z hz1 hz2
    rintro (h | h)
    · exact h hz1
    · exact hz2 h
  have hs₁S : s₁ ∉ S := by
    rintro (h | h)
    · exact h ((admG_analyticAt hg).congr hf'g.symm)
    · exact hs₁m.2 h
  have hVo : IsOpen (ball (1 + (y : ℂ) * I) r ∩ HH) := isOpen_ball.inter (isOpen_halfPlane 1)
  have hVne : (ball (1 + (y : ℂ) * I) r ∩ HH).Nonempty := by
    refine ⟨1 + (y : ℂ) * I + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · show (1 : ℝ) < (1 + (y : ℂ) * I + ((r / 2 : ℝ) : ℂ)).re
      simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero]
      linarith
  obtain ⟨s₃, hs₃V, -, δ, hδ0, hδ1, hδ⟩ := ThmA.exists_path_into hUo hUc hSc hs₁U hs₁S hVo hVne hballU
  have hterm : IsTerminalGerm g δ f' := ThmA.isTerminalGerm_of_analyticAt
    (fun t => by by_contra h; exact (hδ t).2 (Or.inl h)) (by rw [hδ0]; exact hf'g)
  have hadm := admG_trans hg δ hδ0
    (fun t => ⟨(hUsub (hδ t).1).2, fun h => (hδ t).2 (Or.inr h)⟩) hterm
  rw [hδ1] at hadm
  exact boundary_G hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 hadm y r hr hs₃V.1
    ⟨hs₃V.1, f', hf'm.mono_set hball, EventuallyEq.rfl⟩

end GoldbachBoundaries.HInf.Fill
