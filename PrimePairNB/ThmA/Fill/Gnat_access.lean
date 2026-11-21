import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.N1A_access
import PrimePairNB.ThmA.Fill.Dc_access_two
import PrimePairNB.ThmA.Fill.Gnat_spec
import PrimePairNB.ThmA.Fill.Pv_spec
import PrimePairNB.ThmA.Fill.analyticAt_N1A
import PrimePairNB.ThmA.Fill.analyticOn_Dc
import PrimePairNB.ThmA.Fill.cutDisc_facts
import PrimePairNB.ThmA.Fill.decomp_exists
import PrimePairNB.ThmA.Fill.exists_good_discs

/-!
# `Gnat_access` (the access lemma for `G^♮`)

`s₀ = α - t₀v`, `σ₀ = Re s₀`. We pick `b ∈ (1/2, 1)` with `2b < σ₀` and continue `N₁^♮` and `𝒟` from
the `+` side to a ball about `s₀` (`G_access_parts`), in three cases:

* (i) `α ≠ 2`: `b = 1/4 + σ₀/4`; `t₀ < 1-b` since `Re(α-1) ≤ 1/2` (RH); `N1A_access` with `A = P_v`
  (the anchor is off the line `2 + ℝv` by the good slant); `𝒟` is holomorphic at `s₀ ∉ 𝒮 + 𝒮`.
* (ii) `α = 2`, `σ₀ > 3/2`: `b = σ₀/2 - 1/4`, `t₀ < 1-b`; `N1A_access` (anchor on the `+` real side of
  the ray); `Dc_access_two`.
* (iii) `α = 2`, `σ₀ ≤ 3/2`: `b = 1/4 + σ₀/4`, `1-b < t₀ < 2(1-b)`; the anchor lies on the ray of
  `P_v`, so replace `P_v` by its continuation `F` from the `+` side (`Pv_spec` (3)), use
  `analyticAt_N1A`, and `N1A_congr` on the `+` side; `Dc_access_two`.

Then `Gp = (2F_N - F_D + H̃_b)/Γ` on a cut disc inside `σ > 2b`, and `Gp = Gb b = G^♮` on `V⁺`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

theorem G_two_mem_catalogue : (2 : ℂ) ∈ catalogue := Or.inl (Or.inl (mem_singleton 2))

theorem G_ball_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    ∃ ρ > 0, AnalyticOnNhd ℂ f (ball z ρ) :=
  Metric.eventually_nhds_iff_ball.mp hf.eventually_analyticAt

/-- The continuations of `N₁^♮` and `𝒟` from the `+` side at a cut point (three cases). -/
theorem G_access_parts (hRH : RiemannHypothesis) {κ : ℝ} (hκ : IsGoodSlant κ) {α : ℂ}
    (hα : α ∈ catalogue) {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀1 : t₀ < α.re - 1) :
    ∃ b ∈ Ioo (1 / 2 : ℝ) 1, 2 * b < (α - (t₀ : ℂ) * slantDir κ).re ∧
      ∃ ρ > 0, ∃ FN FD : ℂ → ℂ,
        AnalyticOnNhd ℂ FN (ball (α - (t₀ : ℂ) * slantDir κ) ρ) ∧
        AnalyticOnNhd ℂ FD (ball (α - (t₀ : ℂ) * slantDir κ) ρ) ∧
        ∀ s ∈ ball (α - (t₀ : ℂ) * slantDir κ) ρ,
          0 < ((s - (α - (t₀ : ℂ) * slantDir κ)) / slantDir κ).im →
            FN s = N1nat κ b s ∧ FD s = Dc κ b s := by
  have hv := slantDir_ne_zero κ
  set s₀ := α - (t₀ : ℂ) * slantDir κ with hs₀
  have hσ : s₀.re = α.re - t₀ := by simp [hs₀, slantDir]
  have hα2 := re_le_two_of_mem_catalogue hα
  have h1 : 1 < s₀.re := by rw [hσ]; linarith
  have hwbre : ∀ b : ℝ, (wb κ b).re = b := by intro b; simp [wb, slantDir]
  -- the segment `s₀ - 1 + uv` meets `Σ` only at `u = t₀`
  have hseg : ∀ u : ℝ, u ≠ t₀ → s₀ - 1 + (u : ℂ) * slantDir κ ∉ PoleSetQ := by
    intro u hu hmem
    have hc := one_add_mem_catalogue_of_mem_poleSetQ hmem
    by_cases heq : α = 1 + (s₀ - 1 + (u : ℂ) * slantDir κ)
    · have : ((t₀ - u : ℝ) : ℂ) * slantDir κ = 0 := by
        rw [hs₀] at heq; push_cast; linear_combination heq
      rcases mul_eq_zero.mp this with h | h
      · exact hu (by have := Complex.ofReal_eq_zero.mp h; linarith)
      · exact hv h
    · exact hκ.2.2 α hα _ hc heq (t₀ - u) (by rw [hs₀]; push_cast; ring)
  have hpole : s₀ - 1 + (t₀ : ℂ) * slantDir κ ∈ PoleSetQ := by
    rw [show s₀ - 1 + (t₀ : ℂ) * slantDir κ = α - 1 by rw [hs₀]; ring]
    exact sub_one_mem_poleSetQ_of_mem_catalogue hα
  -- combining two continuations on the smaller ball
  have hcomb : ∀ b : ℝ, ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → 0 < ρ₂ → ∀ FN FD : ℂ → ℂ,
      AnalyticOnNhd ℂ FN (ball s₀ ρ₁) → AnalyticOnNhd ℂ FD (ball s₀ ρ₂) →
      (∀ s ∈ ball s₀ ρ₁, 0 < ((s - s₀) / slantDir κ).im → FN s = N1nat κ b s) →
      (∀ s ∈ ball s₀ ρ₂, 0 < ((s - s₀) / slantDir κ).im → FD s = Dc κ b s) →
      ∃ ρ > 0, ∃ FN FD : ℂ → ℂ, AnalyticOnNhd ℂ FN (ball s₀ ρ) ∧ AnalyticOnNhd ℂ FD (ball s₀ ρ) ∧
        ∀ s ∈ ball s₀ ρ, 0 < ((s - s₀) / slantDir κ).im → FN s = N1nat κ b s ∧ FD s = Dc κ b s := by
    intro b ρ₁ ρ₂ hρ₁ hρ₂ FN FD hFN hFD hN hD
    have h1' : ball s₀ (min ρ₁ ρ₂) ⊆ ball s₀ ρ₁ := ball_subset_ball (min_le_left _ _)
    have h2' : ball s₀ (min ρ₁ ρ₂) ⊆ ball s₀ ρ₂ := ball_subset_ball (min_le_right _ _)
    exact ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, FN, FD, hFN.mono h1', hFD.mono h2',
      fun s hs him => ⟨hN s (h1' hs) him, hD s (h2' hs) him⟩⟩
  by_cases h2 : α = 2
  · subst h2
    have hσ2 : s₀.re = 2 - t₀ := by rw [hσ]; norm_num
    by_cases h32 : 3 / 2 < s₀.re
    · -- case (ii)
      set b : ℝ := s₀.re / 2 - 1 / 4 with hbdef
      have hb : b ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by rw [hbdef]; linarith, by rw [hbdef]; linarith⟩
      have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
      have ht₀b : t₀ < 1 - b := by rw [hbdef]; linarith
      have hanc : (s₀ - wb κ b - 1) / slantDir κ = ((1 - b - t₀ : ℝ) : ℂ) := by
        rw [hs₀, wb]; field_simp; push_cast; ring
      have hA : AnalyticAt ℂ (Pv κ) (s₀ - wb κ b) := by
        refine ((Pv_spec hRH κ).2.1 _ ?_ ?_).1
        · rw [sub_re, hwbre]; linarith
        · rw [hanc]; exact Complex.ofReal_mem_slitPlane.mpr (by linarith)
      obtain ⟨r₁, hr₁, FN, hFN, hFNeq⟩ := N1A_access hRH hb' ⟨ht₀, ht₀b⟩ h1 hpole hA
        (fun u _ hu => hseg u hu)
      obtain ⟨r₂, hr₂, FD, hFD, hFDeq⟩ := Dc_access_two κ hb' (t₀ := t₀)
        ⟨ht₀, by linarith⟩ (by linarith)
      exact ⟨b, hb, by rw [hbdef]; linarith,
        hcomb b r₁ r₂ hr₁ hr₂ FN FD hFN hFD hFNeq hFDeq⟩
    · -- case (iii)
      push Not at h32
      set b : ℝ := 1 / 4 + s₀.re / 4 with hbdef
      have hb : b ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by rw [hbdef]; linarith, by rw [hbdef]; linarith⟩
      have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
      have ht₀b : 1 - b < t₀ := by rw [hbdef]; linarith
      have ht₀b2 : t₀ < 2 * (1 - b) := by rw [hbdef]; linarith
      set z₀ := s₀ - wb κ b with hz₀
      have hanc : (z₀ - 1) / slantDir κ = ((1 - b - t₀ : ℝ) : ℂ) := by
        rw [hz₀, hs₀, wb]; field_simp; push_cast; ring
      have hz₀re : 1 / 2 < z₀.re := by rw [hz₀, sub_re, hwbre]; linarith
      have hz₀ne : z₀ ≠ 1 := by
        intro h
        have : ((1 - b - t₀ : ℝ) : ℂ) = 0 := by rw [← hanc, h]; simp
        have := Complex.ofReal_eq_zero.mp this
        linarith
      obtain ⟨r₃, hr₃, FP, hFP, hFPeq⟩ := (Pv_spec hRH κ).2.2 z₀ hz₀re hz₀ne
      have hN : AnalyticAt ℂ (N1A κ b FP) s₀ :=
        analyticAt_N1A hb' h1 (hFP z₀ (mem_ball_self hr₃))
          (fun u hu => hseg u (by linarith [hu.2]))
      obtain ⟨r₄, hr₄, hN'⟩ := G_ball_of_analyticAt hN
      obtain ⟨r₂, hr₂, FD, hFD, hFDeq⟩ := Dc_access_two κ hb' (t₀ := t₀)
        ⟨ht₀, ht₀b2⟩ (by linarith)
      refine ⟨b, hb, by rw [hbdef]; linarith, hcomb b (min r₃ r₄) r₂ (lt_min hr₃ hr₄) hr₂
        (N1A κ b FP) FD (hN'.mono (ball_subset_ball (min_le_right _ _))) hFD ?_ hFDeq⟩
      intro s hs him
      apply N1A_congr
      apply hFPeq
      · rw [mem_ball, dist_eq_norm, hz₀, sub_sub_sub_cancel_right, ← dist_eq_norm]
        exact lt_of_lt_of_le (mem_ball.mp hs) (min_le_left _ _)
      · have : (s - wb κ b - 1) / slantDir κ = (s - s₀) / slantDir κ + ((1 - b - t₀ : ℝ) : ℂ) := by
          rw [← hanc, hz₀]; field_simp; ring
        rw [this, add_im, Complex.ofReal_im, add_zero]
        exact him
  · -- case (i)
    have hare : (α - 1).re ≤ 1 / 2 := by
      by_contra hlt
      push Not at hlt
      have hmem : α - 1 ∈ PoleSetQ ∩ halfPlane (1 / 2) :=
        ⟨sub_one_mem_poleSetQ_of_mem_catalogue hα, hlt⟩
      rw [(lem_Sigma_iv_proof hRH).1] at hmem
      exact h2 (by have := mem_singleton_iff.mp hmem; linear_combination this)
    have hare' : α.re ≤ 3 / 2 := by simp at hare; linarith
    set b : ℝ := 1 / 4 + s₀.re / 4 with hbdef
    have hb : b ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by rw [hbdef]; linarith, by rw [hbdef]; linarith⟩
    have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
    have ht₀b : t₀ < 1 - b := by rw [hbdef]; linarith
    -- `s₀` is off the line `2 + ℝv`
    have hoff : ∀ x : ℝ, s₀ ≠ 2 + (x : ℂ) * slantDir κ := by
      intro x h
      exact hκ.2.2 α hα 2 G_two_mem_catalogue h2 (x + t₀)
        (by rw [hs₀] at h; push_cast; linear_combination h)
    have hA : AnalyticAt ℂ (Pv κ) (s₀ - wb κ b) := by
      refine ((Pv_spec hRH κ).2.1 _ ?_ ?_).1
      · rw [sub_re, hwbre]; linarith
      · rw [Complex.mem_slitPlane_iff]
        right
        intro him
        set w := (s₀ - wb κ b - 1) / slantDir κ with hw
        have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
        have hmul : w * slantDir κ = s₀ - wb κ b - 1 := by rw [hw]; field_simp
        apply hoff (w.re - (1 - b))
        rw [hwr] at hmul
        rw [wb] at hmul
        push_cast at hmul ⊢
        linear_combination -hmul
    obtain ⟨r₁, hr₁, FN, hFN, hFNeq⟩ := N1A_access hRH hb' ⟨ht₀, ht₀b⟩ h1 hpole hA
      (fun u _ hu => hseg u hu)
    have hSS : s₀ ∉ segSS κ b := by
      rintro ⟨w, -, hw⟩
      exact hoff (-w) (by rw [hw]; push_cast; ring)
    obtain ⟨r₂, hr₂, hD⟩ := G_ball_of_analyticAt (analyticOn_Dc κ hb' s₀ hSS)
    exact ⟨b, hb, by rw [hbdef]; linarith,
      hcomb b r₁ r₂ hr₁ hr₂ FN (Dc κ b) hFN hD hFNeq (fun _ _ _ => rfl)⟩

/-- **the access lemma** for `G^♮`, in the form of `IsPrincipalSheet.access`. Under RH.

Sketch. `s₀ = α - t₀v`, `0 < t₀ < Re α - 1`, `σ₀ = Re s₀`. Case (i) `α ≠ 2`: `b ∈ (1/2, σ₀/2)`, so
`t₀ < 1-b` (as `Re a ≤ 1/2 < b`, `lem_Sigma_iv_proof`); anchor off the ray of `P_v` (else
`s₀ ∈ cut_2`); `N1A_access` with `A = Pv`; `𝒟` holomorphic at `s₀` (`analyticOn_Dc`, `s₀ ∉ cut_2`).
Case (ii) `α = 2`, `σ₀ > 3/2`: `b ∈ (1/2, σ₀ - 1)`, `t₀ < 1-b`; `N1A_access` with `a = 1`;
`Dc_access_two`. Case (iii) `α = 2`, `σ₀ ≤ 3/2`: `b ∈ (1/2, σ₀/2)`, `1-b < t₀ < 2(1-b)`; the segment
misses `Σ` (good slant); the anchor lies inside the ray of `P_v`: take `A = F` from `Pv_spec`(3)
(continuation from the `+` side) and `analyticAt_N1A`, with `N1A_congr` on the `+` side
(`Im((s - w_b - 1)/v) = Im((s-2)/v)`); `Dc_access_two`. In all cases `Htil_spec`, `Gnat = Gb b` on
`V⁺ ⊆ Ω_ℍ ∩ R_b` (`Gnat_spec`, `cutDisc_facts`), `Im((s-α)/v) = Im((s-s₀)/v)`, and shrink `r` to an
`IsCutDisc` (`exists_good_discs`, `IsCutDisc.mono`) inside `R_b`. -/
theorem Gnat_access (hRH : RiemannHypothesis) {κ : ℝ} (hκ : IsGoodSlant κ) {α : ℂ}
    (hα : α ∈ catalogue) {s₀ : ℂ} (hs₀ : s₀ ∈ cut (slantDir κ) α) (hne : s₀ ≠ α) :
    ∃ r : ℝ, 0 < r ∧ IsCutDisc κ α s₀ r ∧
      ∃ Gp : ℂ → ℂ, AnalyticOnNhd ℂ Gp (ball s₀ r) ∧ EqOn Gp (Gnat κ) (upperPart κ α s₀ r) := by
  have hv := slantDir_ne_zero κ
  obtain ⟨rc, hrc, hDc⟩ := (exists_good_discs hκ hα).2 s₀ hs₀ hne
  have hs₀' := hs₀
  obtain ⟨t₀, ht₀, ht₀1, rfl⟩ := hs₀'
  have ht₀pos : 0 < t₀ := by
    rcases ht₀.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; simp) hne
  obtain ⟨b, hb, h2b, ρ, hρ, FN, FD, hFN, hFD, heq⟩ := G_access_parts hRH hκ hα ht₀pos ht₀1
  set s₀ := α - (t₀ : ℂ) * slantDir κ with hs₀def
  set r : ℝ := min (min ρ rc) (s₀.re - 2 * b) with hrdef
  have hr : 0 < r := lt_min (lt_min hρ hrc) (by linarith)
  have hD : IsCutDisc κ α s₀ r := hDc.mono ((min_le_left _ _).trans (min_le_right _ _))
  have hballρ : ball s₀ r ⊆ ball s₀ ρ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hballH : ball s₀ r ⊆ halfPlane (2 * b) := by
    intro s hs
    have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : ‖s - s₀‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hs
    have h3 : r ≤ s₀.re - 2 * b := min_le_right _ _
    have := (abs_lt.mp (lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3))).1
    show 2 * b < s.re
    linarith
  have hHt := (Htil_spec hRH (κ := κ) hb).1.analyticOnNhd (isOpen_halfPlane (2 * b))
  have hpos : ∀ s ∈ ball s₀ r, 0 < s.re := fun s hs => by
    have := hballH hs
    have : 2 * b < s.re := this
    linarith [hb.1]
  have hGamma : ∀ s : ℂ, 0 < s.re → AnalyticAt ℂ Gamma s := by
    intro s hs
    have hGd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz =>
      (Complex.differentiableAt_Gamma z (fun m hm => by
        have : z.re = -(m : ℝ) := by rw [hm]; simp
        have : (0 : ℝ) < z.re := hz
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])).differentiableWithinAt
    exact hGd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  refine ⟨r, hr, hD, fun s => (2 * FN s - FD s + Htil κ b s) / Gamma s, ?_, ?_⟩
  · intro s hs
    refine AnalyticAt.div ?_ (hGamma s (hpos s hs)) (Complex.Gamma_ne_zero_of_re_pos (hpos s hs))
    exact ((analyticAt_const.mul (hFN s (hballρ hs))).sub (hFD s (hballρ hs))).add
      (hHt s (hballH hs))
  · intro s hs
    obtain ⟨-, hupΩ, -, -, -, -, -⟩ := cutDisc_facts hs₀ hD
    have hsΩ := hupΩ hs
    have him : 0 < ((s - s₀) / slantDir κ).im := by
      have hsplit : (s - α) / slantDir κ = (s - s₀) / slantDir κ + ((-t₀ : ℝ) : ℂ) := by
        rw [hs₀def]; field_simp; push_cast; ring
      have := hs.2
      rw [hsplit, add_im, Complex.ofReal_im, add_zero] at this
      exact this
    obtain ⟨hN, hDc'⟩ := heq s (hballρ hs.1) him
    rw [(Gnat_spec hRH κ).2.2 b hb ⟨hsΩ, hballH hs.1⟩, Gb]
    simp only
    rw [hN, hDc']

end GoldbachBoundaries.ThmA
