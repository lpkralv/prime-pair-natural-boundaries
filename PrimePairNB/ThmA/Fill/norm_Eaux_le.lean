import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.exists_Eaux

/-!
# `norm_Eaux_le`

Growth of `E` on vertical strips under RH: `‖E(z)‖ ≪ 1 + log|Im z|` for
`1/2 + ε ≤ Re z ≤ σ₁`, `|Im z| ≥ 2`.

Route. On `U± = {Re > 1/2, ±Im > 0}` (convex), `E' = -Qcont + 1/(z-1)` (identity theorem from
`Re > 1`, where `E = P + Log(z-1)`). For `|y| ≥ 4` the mean value inequality on the horizontal
segment `[x+iy, σ₂+iy]` (`σ₂ = max σ₁ 2`) with `norm_Qcont_le_log`, plus `|P(σ₂+iy)| ≤ ∑ p^{-σ₂}`
and `|Log(σ₂ - 1 + iy)| ≤ log σ₂ + log|y| + π`. For `|y| ≤ 4`, compactness.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

open GoldbachBoundaries.TIdentity in
/-- `‖log w‖ ≤ |log ‖w‖| + π`. -/
theorem lines_norm_log_le (w : ℂ) : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |arg w| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log ‖w‖| + Real.pi := by gcongr; exact abs_arg_le_pi w

/-- On `Re z > 1`, `E' = -Qcont + 1/(z-1)`. -/
theorem lines_hasDerivAt_Eaux_of_one_lt (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 < z.re) :
    HasDerivAt Eaux (-Qcont z + (z - 1)⁻¹) z := by
  have hspec := Eaux_spec hRH
  have hev : (fun w => P w + Complex.log (w - 1)) =ᶠ[𝓝 z] Eaux := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact (hspec.2 w hw).symm
  have hslit : z - 1 ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; linarith
  have hlog : HasDerivAt (fun w => Complex.log (w - 1)) (1 / (z - 1)) z := by
    simpa using ((hasDerivAt_id z).sub_const 1).clog hslit
  have hP := hasDerivAt_P (z := z) hz
  rw [GoldbachBoundaries.TIdentity.Qcont_eq_Q_of_one_lt hz]
  have := (hP.add hlog).congr_of_eventuallyEq hev.symm
  simpa [one_div] using this

/-- Identity theorem: on a convex `U ⊆ {Re > 1/2} ∖ {1}` meeting `Re > 1`,
`E' = -Qcont + 1/(z-1)`. -/
theorem lines_deriv_Eaux_eqOn (hRH : RiemannHypothesis) {U : Set ℂ} (hUc : Convex ℝ U)
    (hU : U ⊆ halfPlane (1 / 2)) (hU1 : (1 : ℂ) ∉ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hz₀re : 1 < z₀.re) :
    EqOn (deriv Eaux) (fun z => -Qcont z + (z - 1)⁻¹) U := by
  have hE := (Eaux_spec hRH).1
  have hne : ∀ z ∈ U, z ≠ 1 := fun z hz h => hU1 (h ▸ hz)
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := z₀) ?_ ?_
    hUc.isPreconnected hz₀ ?_
  · exact (hE.deriv).mono hU
  · intro z hz
    have h1 : AnalyticAt ℂ Qcont z :=
      GoldbachBoundaries.TIdentity.analyticAt_Qcont_of_RH hRH (hU hz) (hne z hz)
    have h2 : AnalyticAt ℂ (fun z : ℂ => (z - 1)⁻¹) z :=
      (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hne z hz))
    exact h1.neg.add h2
  · filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀re] with w hw
    exact (lines_hasDerivAt_Eaux_of_one_lt hRH hw).deriv

/-- `E' = -Qcont + 1/(z-1)` on `Re z > 1/2`, `Im z ≠ 0`. -/
theorem lines_deriv_Eaux (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) (him : z.im ≠ 0) :
    deriv Eaux z = -Qcont z + (z - 1)⁻¹ := by
  rcases lt_or_gt_of_ne him with h | h
  · refine lines_deriv_Eaux_eqOn hRH (U := {w : ℂ | 1 / 2 < w.re} ∩ {w : ℂ | w.im < 0})
      ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_lt _))
      (fun w hw => hw.1) (fun h1 => by simp at h1) (z₀ := 2 - I) ⟨by simp; norm_num, by simp⟩
      (by simp) ⟨hz, h⟩
  · refine lines_deriv_Eaux_eqOn hRH (U := {w : ℂ | 1 / 2 < w.re} ∩ {w : ℂ | 0 < w.im})
      ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _))
      (fun w hw => hw.1) (fun h1 => by simp at h1) (z₀ := 2 + I) ⟨by simp; norm_num, by simp⟩
      (by simp) ⟨hz, h⟩

/-- `‖P(σ + iy)‖ ≤ ∑_p ‖p^{-σ}‖` for `σ > 1`. -/
theorem lines_norm_P_le {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    ‖P ((σ : ℂ) + y * I)‖ ≤ ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-(σ : ℂ))‖ := by
  have hre : 1 < ((σ : ℂ) + y * I).re := by simpa using hσ
  have heq : ∀ p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + y * I))‖ =
      ‖((p : ℕ) : ℂ) ^ (-(σ : ℂ))‖ := by
    intro p
    have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.norm_natCast_cpow_of_pos p.2.pos]
    simp
  unfold P
  calc ‖∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-((σ : ℂ) + y * I))‖
      ≤ ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + y * I))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_P_terms hre)
    _ = _ := tsum_congr heq

end GroupE

/-- **Growth of `E` on vertical strips** (the growth bound for `Q`, adapted to `E`). Under RH.

Sketch. For `Re z ≥ σ₂ := max σ₁ 2`, `Eaux z = P z + Log(z-1)` (`Eaux_spec`), and
`|P| ≤ P(2)`, `|Log(z-1)| ≤ log|z-1| + π ≪ 1 + log|Im z|` for `Re z ∈ [2, σ₂]`. For
`1/2 + ε ≤ Re z ≤ σ₂`, `Eaux(x+iy) = Eaux(σ₂+iy) - ∫_x^{σ₂} Eaux'(u+iy) du` with
`Eaux' = -Qcont + 1/(z-1)` (`Eaux_spec`, identity theorem) and `|Qcont| ≤ C log|y|` for `|y| ≥ 4`
(`norm_Qcont_le_log`, `TIdentity/G7d_QcontBound.lean`); `2 ≤ |y| ≤ 4` is a compact set. -/
theorem norm_Eaux_le (hRH : RiemannHypothesis) {ε σ₁ : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ z : ℂ, 1 / 2 + ε ≤ z.re → z.re ≤ σ₁ → 2 ≤ |z.im| →
      ‖Eaux z‖ ≤ C * (1 + Real.log |z.im|) := by
  have hE := (Eaux_spec hRH).1
  set σ₂ : ℝ := max σ₁ 2 with hσ₂
  have hσ₂2 : 2 ≤ σ₂ := le_max_right _ _
  have hσ₁₂ : σ₁ ≤ σ₂ := le_max_left _ _
  -- the bound on `Qcont`
  obtain ⟨C₀, hC₀⟩ := GoldbachBoundaries.TIdentity.norm_Qcont_le_log hRH hε
  set C₁ : ℝ := max C₀ 0
  set B : ℝ := ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-(σ₂ : ℂ))‖
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  -- compact part
  obtain ⟨M, hM⟩ := (isCompact_Icc.reProdIm (isCompact_Icc (a := (-4 : ℝ)) (b := 4)) :
      IsCompact (Icc (1 / 2 + ε) σ₁ ×ℂ Icc (-4 : ℝ) 4)).exists_bound_of_continuousOn
      (f := Eaux) (hE.continuousOn.mono fun w hw => by
        simp only [mem_reProdIm, mem_Icc] at hw
        show 1 / 2 < w.re
        linarith [hw.1.1])
  set K : ℝ := B + Real.log σ₂ + Real.pi + (σ₂ - 1 / 2)
  set L : ℝ := 1 + C₁ * (σ₂ - 1 / 2)
  refine ⟨max (max M 0) (max K L), fun z hz1 hz2 hz3 => ?_⟩
  have hlog0 : 0 ≤ Real.log |z.im| := Real.log_nonneg (by linarith)
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  have hD : 0 ≤ σ₂ - 1 / 2 := by linarith
  rcases le_or_gt |z.im| 4 with hy | hy
  · -- compact part
    have hmem : z ∈ Icc (1 / 2 + ε) σ₁ ×ℂ Icc (-4 : ℝ) 4 := by
      simp only [mem_reProdIm, mem_Icc]
      exact ⟨⟨hz1, hz2⟩, abs_le.mp hy⟩
    calc ‖Eaux z‖ ≤ M := hM z hmem
      _ ≤ max (max M 0) (max K L) * 1 := by
          rw [mul_one]; exact le_trans (le_max_left _ _) (le_max_left _ _)
      _ ≤ max (max M 0) (max K L) * (1 + Real.log |z.im|) := by
          apply mul_le_mul_of_nonneg_left (by linarith)
          exact le_trans (le_max_right _ _) (le_max_left _ _)
  · -- mean value inequality on the horizontal segment
    set y := z.im
    set z₂ : ℂ := (σ₂ : ℂ) + y * I with hz₂
    have hz₂re : z₂.re = σ₂ := by simp [z₂]
    have hz₂im : z₂.im = y := by simp [z₂]
    have hyne : y ≠ 0 := fun h => by rw [h] at hy; simp at hy; linarith
    -- points of the segment
    have hseg : ∀ w ∈ segment ℝ z z₂, z.re ≤ w.re ∧ w.re ≤ σ₂ ∧ w.im = y := by
      intro w hw
      rw [segment_eq_image'] at hw
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hw
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
        hz₂re, hz₂im, zero_mul, sub_zero, add_zero]
      refine ⟨?_, ?_, by ring⟩
      · nlinarith
      · nlinarith
    have hdiff : ∀ w ∈ segment ℝ z z₂, DifferentiableAt ℂ Eaux w := fun w hw =>
      (hE w (show 1 / 2 < w.re by linarith [(hseg w hw).1])).differentiableAt
    have hbound : ∀ w ∈ segment ℝ z z₂, ‖deriv Eaux w‖ ≤ C₁ * Real.log |y| + 1 := by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := hseg w hw
      rw [GroupE.lines_deriv_Eaux hRH (by linarith) (by rw [h3]; exact hyne)]
      have hQ : ‖Qcont w‖ ≤ C₁ * Real.log |y| := by
        have := hC₀ w (by linarith) (by rw [h3]; exact hy.le)
        rw [h3] at this
        exact this.trans (by gcongr; exact le_max_left _ _)
      have hinv : ‖(w - 1)⁻¹‖ ≤ 1 := by
        rw [norm_inv]
        apply inv_le_one_of_one_le₀
        calc (1 : ℝ) ≤ |y| := by linarith
          _ = |(w - 1).im| := by simp [h3]
          _ ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
      calc ‖-Qcont w + (w - 1)⁻¹‖ ≤ ‖-Qcont w‖ + ‖(w - 1)⁻¹‖ := norm_add_le _ _
        _ ≤ C₁ * Real.log |y| + 1 := by rw [norm_neg]; linarith
    have hmvt := (convex_segment z z₂).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (right_mem_segment ℝ z z₂) (left_mem_segment ℝ z z₂)
    have hdist : ‖z - z₂‖ = σ₂ - z.re := by
      have : z - z₂ = ((z.re - σ₂ : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [z₂, y]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    rw [hdist] at hmvt
    -- the value at `σ₂ + iy`
    have hz₂val : Eaux z₂ = P z₂ + Complex.log (z₂ - 1) :=
      (Eaux_spec hRH).2 z₂ (show 1 < z₂.re by rw [hz₂re]; linarith)
    have hPz₂ : ‖P z₂‖ ≤ B := GroupE.lines_norm_P_le (by linarith) y
    have hlogz₂ : ‖Complex.log (z₂ - 1)‖ ≤ Real.log σ₂ + Real.log |y| + Real.pi := by
      refine (GroupE.lines_norm_log_le _).trans ?_
      have hnorm_ge : |y| ≤ ‖z₂ - 1‖ := by
        calc |y| = |(z₂ - 1).im| := by simp [hz₂im]
          _ ≤ ‖z₂ - 1‖ := Complex.abs_im_le_norm _
      have hnorm_le : ‖z₂ - 1‖ ≤ σ₂ * |y| := by
        calc ‖z₂ - 1‖ ≤ |(z₂ - 1).re| + |(z₂ - 1).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = (σ₂ - 1) + |y| := by
              simp only [Complex.sub_re, Complex.sub_im, hz₂re, hz₂im, Complex.one_re,
                Complex.one_im, sub_zero]
              rw [abs_of_nonneg (by linarith)]
          _ ≤ σ₂ * |y| := by nlinarith
      have hpos : 0 < ‖z₂ - 1‖ := by linarith
      rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
      have := Real.log_le_log hpos hnorm_le
      rw [Real.log_mul (by positivity) (by positivity)] at this
      linarith
    have hEz₂ : ‖Eaux z₂‖ ≤ B + Real.log σ₂ + Real.log |y| + Real.pi := by
      rw [hz₂val]
      calc ‖P z₂ + Complex.log (z₂ - 1)‖ ≤ ‖P z₂‖ + ‖Complex.log (z₂ - 1)‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hfinal : ‖Eaux z‖ ≤ K + L * Real.log |y| := by
      have h1 : ‖Eaux z‖ ≤ ‖Eaux z₂‖ + ‖Eaux z - Eaux z₂‖ := by
        have := norm_sub_norm_le (Eaux z) (Eaux z₂)
        linarith
      have hsx : σ₂ - z.re ≤ σ₂ - 1 / 2 := by linarith
      have hsx0 : 0 ≤ σ₂ - z.re := by linarith
      have h2 : (C₁ * Real.log |y| + 1) * (σ₂ - z.re) ≤
          (C₁ * Real.log |y| + 1) * (σ₂ - 1 / 2) := by
        apply mul_le_mul_of_nonneg_left hsx; positivity
      have hlog0' : 0 ≤ Real.log |y| := hlog0
      simp only [K, L]
      nlinarith
    have hK : 0 ≤ K := by
      have : 0 ≤ Real.log σ₂ := Real.log_nonneg (by linarith)
      simp only [K]; linarith [Real.pi_pos]
    have hL : 0 ≤ L := by simp only [L]; positivity
    set A := max (max M 0) (max K L)
    have hKA : K ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
    have hLA : L ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
    calc ‖Eaux z‖ ≤ K + L * Real.log |y| := hfinal
      _ ≤ A + A * Real.log |y| := by gcongr
      _ = A * (1 + Real.log |z.im|) := by ring

end GoldbachBoundaries.ThmA
