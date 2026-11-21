import PrimePairNB.Paper2.M1.Fill.E1Common
import PrimePairNB.Paper2.M1.Fill.differentiableOn_verticalIntegral'
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.isOpen_RegC

/-!
# `Ic_differentiableOn`

On the line `Re w = c` no point is in `Σ_Q` (it would be in `F_δ` with `Re = c`), and for `s` in the region no
`s - w` is (it would be a `b ∈ F_δ` with `σ = c + Re b`). So the integrand is jointly continuous on
`RegC × line` and holomorphic in `s`; on a compact `K ⊆ RegC` it is dominated by `M (1 + |y|)^{-2}`
(`E1_norm_gs_le_far` far out, compactness of `K × [-|Y|, |Y|]` near the real axis). Then
`differentiableOn_verticalIntegral'`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Points of the line and their reflections avoid `Σ_Q` (and lie in `Re > 0`). -/
lemma E1_line_regular (hZ1 : Z1) {δ c : ℝ} (h : AdmC δ c) {s w : ℂ} (hs : s ∈ RegC δ c)
    (hw : w.re = c) : 0 < w.re ∧ w ∉ PoleSetQ ∧ 0 < (s - w).re ∧ s - w ∉ PoleSetQ := by
  have hB := half_le_Binf hZ1
  have hc := h.2.2.1
  have hδ := h.1
  have hs1 := hs.1
  refine ⟨by rw [hw]; linarith, fun hp => ?_, by simp only [sub_re, hw]; linarith, fun hp => ?_⟩
  · exact h.2.2.2.2 w ⟨hp, by rw [hw]; linarith⟩ hw.symm
  · have he := hs.2 (s - w) ⟨hp, by simp only [sub_re, hw]; linarith⟩
    simp only [sub_re, hw] at he
    exact he (by ring)

/-- A bound `C (1 + |y|)^{-2}` for `|y| ≥ Y` and `B` for `|y| ≤ |Y|` gives one bound `M (1 + |y|)^{-2}`. -/
lemma E1_bound_inv_sq (C Y B : ℝ) : ∃ M : ℝ, ∀ y v : ℝ, (Y ≤ |y| → v ≤ C / (1 + |y|) ^ 2) →
    (|y| ≤ |Y| → v ≤ B) → v ≤ M * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  refine ⟨max C 0 + max B 0 * (1 + |Y|) ^ 2, fun y v h1 h2 => ?_⟩
  set M : ℝ := max C 0 + max B 0 * (1 + |Y|) ^ 2 with hM
  have hpos : 0 < 1 + |y| := by positivity
  have hrpow : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg hpos.le]
    norm_cast
  rw [hrpow, ← div_eq_mul_inv]
  have hBn : 0 ≤ max B 0 * (1 + |Y|) ^ 2 := by positivity
  by_cases hy : Y ≤ |y|
  · calc v ≤ C / (1 + |y|) ^ 2 := h1 hy
      _ ≤ max C 0 / (1 + |y|) ^ 2 := by gcongr; exact le_max_left _ _
      _ ≤ M / (1 + |y|) ^ 2 := by gcongr; rw [hM]; linarith
  · push Not at hy
    have hyY : |y| ≤ |Y| := le_trans hy.le (le_abs_self Y)
    have hv : v ≤ max B 0 := le_trans (h2 hyY) (le_max_left _ _)
    rw [le_div_iff₀ (by positivity)]
    calc v * (1 + |y|) ^ 2 ≤ max B 0 * (1 + |Y|) ^ 2 := by
          rcases le_or_gt v 0 with hv0 | hv0
          · nlinarith [sq_nonneg (1 + |y|)]
          · gcongr
      _ ≤ M := by rw [hM]; linarith [le_max_right C 0]

/-- **`I_c` is holomorphic on the region** (Z1, Z2, Z3). On the line no point is in `Σ_Q` (a point of `Σ_Q` with
real part `c > B_∞ + 2δ` would be in `F_δ`), and for `s` in the region no `s - w` is (its real part `σ - c > B_∞ + 2δ`
would put it in `F_δ` with `σ = c + Re b`); so the integrand is continuous on `RegC × line`, and dominated on compact
sets by `E1_norm_gs_le_far` plus a bound on the compact part of the line. Uses: `differentiableOn_verticalIntegral'`,
`E1_norm_gs_le_far`, `isOpen_RegC`, `meromorphicAt_Qcont`, `analyticAt_Qcont_sub_sum` (or `isQCont_eventuallyEq`). -/
theorem Ic_differentiableOn (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c : ℝ} (h : AdmC δ c) :
    DifferentiableOn ℂ (IcQ Qcont c) (RegC δ c) := by
  have hB := half_le_Binf hZ1
  have hδ := h.1
  have hc := h.2.2.1
  set F : ℂ → ℂ → ℂ := fun s w => KerS s w * Qcont w * Qcont (s - w) with hFdef
  have hre_line : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := fun y => by simp
  -- joint continuity on `RegC × line`
  have hcont : ContinuousOn (fun p : ℂ × ℝ => F p.1 (c + p.2 * I)) (RegC δ c ×ˢ univ) := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    obtain ⟨hw0, hwP, hsw0, hswP⟩ := E1_line_regular hZ1 h hs (hre_line y)
    have hs0 : 0 < s.re := by linarith [hs.1]
    have g1 : ContinuousAt (fun p : ℂ × ℝ => (c : ℂ) + p.2 * I) (s, y) := by fun_prop
    have g2 : ContinuousAt (fun p : ℂ × ℝ => p.1 - ((c : ℂ) + p.2 * I)) (s, y) := by fun_prop
    have hG1 : ContinuousAt (fun p : ℂ × ℝ => Gamma ((c : ℂ) + p.2 * I)) (s, y) :=
      ContinuousAt.comp (g := Gamma) (TIdentity.differentiableAt_Gamma_of_re_pos hw0).continuousAt g1
    have hG2 : ContinuousAt (fun p : ℂ × ℝ => Gamma (p.1 - ((c : ℂ) + p.2 * I))) (s, y) :=
      ContinuousAt.comp (g := Gamma) (TIdentity.differentiableAt_Gamma_of_re_pos hsw0).continuousAt g2
    have hG3 : ContinuousAt (fun p : ℂ × ℝ => Gamma p.1) (s, y) :=
      ContinuousAt.comp (g := Gamma) (TIdentity.differentiableAt_Gamma_of_re_pos hs0).continuousAt
        continuousAt_fst
    have hQ1 : ContinuousAt (fun p : ℂ × ℝ => Qcont ((c : ℂ) + p.2 * I)) (s, y) :=
      ContinuousAt.comp (g := Qcont) (E1_analyticAt_Qcont hw0 hwP).continuousAt g1
    have hQ2 : ContinuousAt (fun p : ℂ × ℝ => Qcont (p.1 - ((c : ℂ) + p.2 * I))) (s, y) :=
      ContinuousAt.comp (g := Qcont) (E1_analyticAt_Qcont hsw0 hswP).continuousAt g2
    have hall := ((hG1.mul hG2).div hG3 (Complex.Gamma_ne_zero_of_re_pos hs0)).mul hQ1 |>.mul hQ2
    exact hall.continuousWithinAt
  -- holomorphy in `s`
  have hhol : ∀ y : ℝ, DifferentiableOn ℂ (fun s => F s (c + y * I)) (RegC δ c) := by
    intro y s hs
    obtain ⟨hw0, hwP, hsw0, hswP⟩ := E1_line_regular hZ1 h hs (hre_line y)
    have hs0 : 0 < s.re := by linarith [hs.1]
    have h2 : DifferentiableAt ℂ (fun s => Gamma (s - ((c : ℂ) + y * I))) s :=
      (TIdentity.differentiableAt_Gamma_of_re_pos hsw0).comp s
        (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s - ((c : ℂ) + y * I)) s)
    have h3 : DifferentiableAt ℂ (fun s => Qcont (s - ((c : ℂ) + y * I))) s :=
      DifferentiableAt.comp (g := Qcont) s (E1_analyticAt_Qcont hsw0 hswP).differentiableAt
        (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s - ((c : ℂ) + y * I)) s)
    have hK : DifferentiableAt ℂ (fun s => KerS s ((c : ℂ) + y * I)) s := by
      unfold KerS
      exact ((differentiableAt_const _).mul h2).div
        (TIdentity.differentiableAt_Gamma_of_re_pos hs0) (Complex.Gamma_ne_zero_of_re_pos hs0)
    exact ((hK.mul (differentiableAt_const _)).mul h3).differentiableWithinAt
  -- domination on compact subsets
  have hdom : ∀ K ⊆ RegC δ c, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ s ∈ K, ∀ y : ℝ, ‖F s (c + y * I)‖ ≤ g y := by
    intro K hKU hK
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, integrable_zero _ _ _, fun s hs => by simp [hKe] at hs⟩
    obtain ⟨s₀, hs₀K, hmin⟩ := hK.exists_isMinOn hKne continuous_re.continuousOn
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hσ₁ : c + Binf + 2 * δ ≤ s₀.re := (hKU hs₀K).1.le
    obtain ⟨C, Y, hCY⟩ := E1_norm_gs_le_far (σ₂ := R) (τ₀ := R) (c₂ := c) hZ1 hZ2 hZ3 hδ hc.le hσ₁
    obtain ⟨Bd, hBd⟩ := (hK.prod (isCompact_Icc (a := -|Y|) (b := |Y|))).exists_bound_of_continuousOn
      (hcont.mono (prod_mono hKU (subset_univ _)))
    obtain ⟨M, hM⟩ := E1_bound_inv_sq C Y Bd
    refine ⟨fun y => M * (1 + ‖y‖) ^ (-(2 : ℝ)),
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul M, ?_⟩
    intro s hs y
    refine hM y _ (fun hy => ?_) (fun hy => ?_)
    · have hsre : s₀.re ≤ s.re := hmin hs
      have hsR : ‖s‖ ≤ R := hR s hs
      have h1 : s.re ≤ R := le_trans (re_le_norm s) hsR
      have h2 : |s.im| ≤ R := le_trans (abs_im_le_norm s) hsR
      have hyw : |y| = |((c : ℂ) + y * I).im| := by simp
      have := (hCY s hsre h1 h2 ((c : ℂ) + y * I) (by simp) (by simp) (by rw [← hyw]; exact hy)).2.2
      rw [← hyw] at this
      exact this
    · exact hBd (s, y) ⟨hs, abs_le.mp hy⟩
  exact differentiableOn_verticalIntegral' (isOpen_RegC hZ1 h) hcont hhol hdom

end GoldbachBoundaries.Paper2.M1
