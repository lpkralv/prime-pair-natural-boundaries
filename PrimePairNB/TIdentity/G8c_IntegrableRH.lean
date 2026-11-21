import PrimePairNB.TIdentity.G7d_QcontBound

/-!
# under RH, `Γ Q` is integrable on `Re z = σ ∈ (1/2, 1)`

Uses `analyticAt_Qcont_of_RH`, `continuous_Gamma_line` and `integrable_Gamma_mul_of_bound` from
`Basic.lean` (shared with `G8b_IntegrableOneLt` and `G8d_ContourShift`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- **Under RH, `Γ Q` is integrable on `Re z = σ ∈ (1/2, 1)`** (step (1) of the identity for `T`:
`C_b = (2π)⁻¹ ∫ |Γ(b+iy) Q(b+iy)| dy < ∞`, as `Q` has no pole on `Re z = b`).

Proof sketch. The line misses `Σ`: `lem_Sigma_iv_proof` gives `Σ ∩ {Re > 1/2} = {1}`. So `Qcont`
is analytic, hence continuous, on the line (the `AnalyticOnNhd` clause of `lem_Sigma_i_ii_proof`,
which is about `Qcont`: see its proof, `analyticAt_Qcont_sub_sum`/`regular_of_not_mem_poleSetQ`).
For `|y| ≥ 4` use `norm_Qcont_le_log` (with `ε = σ - 1/2`) and
`norm_Gamma_mul_one_add_abs_im_pow_le` with `n = 2`: `log|y| (1+|y|)^{-2}` is integrable. On
`|y| ≤ 4` the integrand is continuous on a compact set. -/
theorem integrable_Gamma_mul_Qcont_of_RH (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ)
    (hσ1 : σ < 1) :
    Integrable fun y : ℝ => Gamma (σ + y * I) * Qcont (σ + y * I) := by
  have hcont : Continuous fun y : ℝ => Qcont (σ + y * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : 1 / 2 < ((σ : ℂ) + y * I).re := by simpa using hσ
    have hne : (σ : ℂ) + y * I ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    exact (analyticAt_Qcont_of_RH hRH hre hne).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  -- `|y| ≤ 4`: continuity on a compact set
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-4 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨by norm_num, by norm_num⟩)
  -- `|y| ≥ 4`: the growth bound for `Q`
  obtain ⟨C, hC⟩ := norm_Qcont_le_log hRH (ε := σ - 1 / 2) (by linarith)
  refine integrable_Gamma_mul_of_bound (by linarith) hcont (K := M + |C|) fun y => ?_
  have hy0 : 0 ≤ |y| := abs_nonneg y
  rcases le_or_gt |y| 4 with hy | hy
  · have h1 := hM y ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
    nlinarith [abs_nonneg C]
  · have h1 := hC (σ + y * I) (by simp) (by simp; linarith)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at h1
    have hlog0 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
    have hlog1 : Real.log |y| ≤ 1 + |y| := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < |y|)
      linarith
    have h2 : C * Real.log |y| ≤ |C| * (1 + |y|) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
        (mul_le_mul_of_nonneg_left hlog1 (abs_nonneg C))
    nlinarith [abs_nonneg C]

end TIdentity

end GoldbachBoundaries
