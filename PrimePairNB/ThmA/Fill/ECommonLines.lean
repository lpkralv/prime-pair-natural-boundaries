import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.ECommonDom
import PrimePairNB.ThmA.Fill.norm_Eaux_le
import PrimePairNB.ThmA.Fill.Pv_eq_Eb_add
import PrimePairNB.ThmA.Fill.exists_Eaux

/-!
# vertical-line tools and `E_b` on vertical lines

The main statement is `integrable_Gamma_Eb_line` (used by `F0_split`). Helpers live in the namespace `GoldbachBoundaries.ThmA.GroupE`.

Helpers (prefix `lines_`):
* `lines_wb_re`: `Re w_b = b`.
* `lines_div_slantDir_mem_slitPlane`: `w ≠ 0`, `Re w ≥ 0` ⇒ `w/v ∈ slitPlane`.
* `lines_differentiableAt_Eb`: `E_b` is holomorphic at `z` when `Re z > b` (or more generally
  `Re z > 1/2` and `(z - w_b)/v ∈ slitPlane`).
* `lines_norm_Eaux_strip`: `‖E z‖ ≤ K (1 + |Im z|)` on `a ≤ Re z ≤ a'`, `a > 1/2` (RH).
* `lines_norm_Eb_le`: `‖E_b z‖ ≤ K (1 + |Im z| + |log (Im z - Im w_b)|)` on `b ≤ Re z ≤ c`,
  `Im z ≠ Im w_b` (RH).
* `lines_norm_integrand_le`: the uniform bound `‖Γ E_b t^{-z}‖ ≤ C · logDom(Im z)` on the strip.
* `lines_aestronglyMeasurable`: measurability of `y ↦ Γ E_b t^{-z}` on `Re z = σ > 1/2`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

theorem lines_wb_re (κ b : ℝ) : (wb κ b).re = b := by
  simp [wb, slantDir]

/-- `w/v ∈ slitPlane` when `w ≠ 0` and `Re w ≥ 0` (the cut `-[0,∞)v` has `Re < 0` off `0`). -/
theorem lines_div_slantDir_mem_slitPlane (κ : ℝ) {w : ℂ} (hw : w ≠ 0) (hre : 0 ≤ w.re) :
    w / slantDir κ ∈ slitPlane := by
  have hv := lines_slantDir_ne_zero κ
  by_contra h
  rw [mem_slitPlane_iff, not_or, not_lt, not_not] at h
  set q := w / slantDir κ with hq
  have hqre : q = (q.re : ℂ) := Complex.ext (by simp) (by simp [h.2])
  have hwq : w = (q.re : ℂ) * slantDir κ := by rw [← hqre, hq]; field_simp
  have hwre : w.re = q.re := by rw [hwq]; simp [slantDir]
  have hq0 : q.re = 0 := le_antisymm h.1 (hwre ▸ hre)
  exact hw (by rw [hwq, hq0]; simp)

/-- For `Re z > b`, `(z - w_b)/v ∈ slitPlane`. -/
theorem lines_mem_slitPlane_of_re_gt {κ b : ℝ} {z : ℂ} (hz : b < z.re) :
    (z - wb κ b) / slantDir κ ∈ slitPlane := by
  have hre : (z - wb κ b).re = z.re - b := by simp [lines_wb_re]
  refine lines_div_slantDir_mem_slitPlane κ (fun h => ?_) (by rw [hre]; linarith)
  have := congrArg Complex.re h
  simp only [hre, Complex.zero_re] at this
  linarith

/-- `E_b` is holomorphic at `z` when `Re z > 1/2` and `(z - w_b)/v ∈ slitPlane` (RH). -/
theorem lines_differentiableAt_Eb (hRH : RiemannHypothesis) {κ b : ℝ} {z : ℂ} (hz : 1 / 2 < z.re)
    (hslit : (z - wb κ b) / slantDir κ ∈ slitPlane) : DifferentiableAt ℂ (Eb κ b) z := by
  have hE : DifferentiableAt ℂ Eaux z := ((Eaux_spec hRH).1 z hz).differentiableAt
  have hlog : DifferentiableAt ℂ (fun z => Complex.log ((z - wb κ b) / slantDir κ)) z :=
    ((differentiableAt_id.sub_const _).div_const _).clog hslit
  exact hE.sub (hlog.add_const _)

/-- `E` grows at most linearly on vertical strips `a ≤ Re z ≤ a'`, `a > 1/2` (RH). -/
theorem lines_norm_Eaux_strip (hRH : RiemannHypothesis) {a a' : ℝ} (ha : 1 / 2 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ a' → ‖Eaux z‖ ≤ K * (1 + |z.im|) := by
  obtain ⟨C, hC⟩ := norm_Eaux_le hRH (ε := a - 1 / 2) (σ₁ := a') (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_Icc.reProdIm (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) :
      IsCompact (Icc a a' ×ℂ Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
      (f := Eaux) ((Eaux_spec hRH).1.continuousOn.mono fun w hw => by
        simp only [mem_reProdIm, mem_Icc] at hw
        show 1 / 2 < w.re
        linarith [hw.1.1])
  refine ⟨max |C| (max M 0), le_max_of_le_right (le_max_right _ _), fun z hz1 hz2 => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
  rcases le_or_gt |z.im| 2 with hy | hy
  · have hmem : z ∈ Icc a a' ×ℂ Icc (-2 : ℝ) 2 := by
      simp only [mem_reProdIm, mem_Icc]
      exact ⟨⟨hz1, hz2⟩, abs_le.mp hy⟩
    calc ‖Eaux z‖ ≤ M := hM z hmem
      _ ≤ max |C| (max M 0) := le_max_of_le_right (le_max_left _ _)
      _ ≤ max |C| (max M 0) * (1 + |z.im|) :=
          le_mul_of_one_le_right (le_max_of_le_right (le_max_right _ _)) h1
  · have hlog0 : 0 ≤ Real.log |z.im| := Real.log_nonneg (by linarith)
    have hlog : Real.log |z.im| ≤ |z.im| := by
      have := Real.log_le_sub_one_of_pos (show 0 < |z.im| by linarith)
      linarith
    calc ‖Eaux z‖ ≤ C * (1 + Real.log |z.im|) := hC z (by linarith) hz2 hy.le
      _ ≤ |C| * (1 + Real.log |z.im|) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self C); linarith
      _ ≤ max |C| (max M 0) * (1 + |z.im|) := by
          apply mul_le_mul (le_max_left _ _) (by linarith) (by linarith)
            (le_max_of_le_right (le_max_right _ _))

/-- `|log x| ≤ M + d + |log d|` for `0 < d ≤ x ≤ M + d`, `M ≥ 0`. -/
theorem lines_abs_log_le {x d M : ℝ} (hd : 0 < d) (hdx : d ≤ x) (hxM : x ≤ M + d) :
    |Real.log x| ≤ M + d + |Real.log d| := by
  have hx : 0 < x := lt_of_lt_of_le hd hdx
  rcases le_or_gt 1 x with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_sub_one_of_pos hx
    linarith [abs_nonneg (Real.log d)]
  · rw [abs_of_neg (Real.log_neg hx h1)]
    have h2 := Real.log_le_log hd hdx
    have h3 : 0 ≤ M := by linarith
    linarith [neg_abs_le (Real.log d)]

/-- `E_b` on the strip `b ≤ Re z ≤ c` off the horizontal line through `w_b`:
`‖E_b z‖ ≤ K (1 + |Im z| + |log (Im z - Im w_b)|)` (RH). -/
theorem lines_norm_Eb_le (hRH : RiemannHypothesis) {κ b c : ℝ} (hb : 1 / 2 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c → z.im ≠ (wb κ b).im →
      ‖Eb κ b z‖ ≤ K * (1 + |z.im| + |Real.log (z.im - (wb κ b).im)|) := by
  obtain ⟨KE, hKE0, hKE⟩ := lines_norm_Eaux_strip hRH (a := b) (a' := c) hb
  set y₀ := (wb κ b).im
  set v := slantDir κ
  have hv : v ≠ 0 := lines_slantDir_ne_zero κ
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set K : ℝ := KE + 1 + |c - b| + |y₀| + |Real.log ‖v‖| + Real.pi + ‖Complex.log v‖
  have hK0 : 0 ≤ K := by
    simp only [K]; positivity
  refine ⟨K, hK0, fun z hz1 hz2 hz3 => ?_⟩
  set y := z.im
  set d := |y - y₀|
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hz3)
  set w := z - wb κ b
  have hwre : w.re = z.re - b := by simp [w, lines_wb_re]
  have hwim : w.im = y - y₀ := by simp [w, y, y₀]
  have hdw : d ≤ ‖w‖ := by
    calc d = |w.im| := by rw [hwim]
      _ ≤ ‖w‖ := Complex.abs_im_le_norm _
  have hwM : ‖w‖ ≤ |c - b| + d := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ |c - b| + d := by
          rw [hwim, hwre, abs_of_nonneg (by linarith)]
          gcongr
          exact le_trans (by linarith) (le_abs_self _)
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hd hdw
  have hlogw : |Real.log ‖w‖| ≤ |c - b| + d + |Real.log d| := lines_abs_log_le hd hdw hwM
  have hlogd : |Real.log d| = |Real.log (y - y₀)| := by rw [Real.log_abs]
  have hdy : d ≤ |y| + |y₀| := by
    calc d = |y - y₀| := rfl
      _ ≤ |y| + |y₀| := abs_sub _ _
  have hlogq : ‖Complex.log (w / v)‖ ≤ |Real.log ‖w‖| + |Real.log ‖v‖| + Real.pi := by
    refine (lines_norm_log_le _).trans ?_
    rw [norm_div, Real.log_div hwpos.ne' hvn.ne']
    linarith [abs_sub (Real.log ‖w‖) (Real.log ‖v‖)]
  have hEz : ‖Eaux z‖ ≤ KE * (1 + |y|) := hKE z hz1 hz2
  have hmain : ‖Eb κ b z‖ ≤ ‖Eaux z‖ + ‖Complex.log (w / v)‖ + ‖Complex.log v‖ := by
    unfold Eb
    calc ‖Eaux z - (Complex.log ((z - wb κ b) / slantDir κ) + Complex.log (slantDir κ))‖
        ≤ ‖Eaux z‖ + ‖Complex.log ((z - wb κ b) / slantDir κ) + Complex.log (slantDir κ)‖ :=
          norm_sub_le _ _
      _ ≤ ‖Eaux z‖ + (‖Complex.log (w / v)‖ + ‖Complex.log v‖) := by
          gcongr; exact norm_add_le _ _
      _ = _ := by ring
  set L := |Real.log (y - y₀)|
  have hL : 0 ≤ L := abs_nonneg _
  have hy : 0 ≤ |y| := abs_nonneg _
  -- collect
  have hsum : ‖Eb κ b z‖ ≤ (KE + 1) * |y| + L +
      (KE + |c - b| + |y₀| + |Real.log ‖v‖| + Real.pi + ‖Complex.log v‖) := by
    nlinarith
  have hc0 : 0 ≤ |c - b| + |y₀| + |Real.log ‖v‖| + Real.pi + ‖Complex.log v‖ := by positivity
  calc ‖Eb κ b z‖ ≤ (KE + 1) * |y| + L +
      (KE + |c - b| + |y₀| + |Real.log ‖v‖| + Real.pi + ‖Complex.log v‖) := hsum
    _ ≤ K * 1 + K * |y| + K * L := by
        have h1 : KE + 1 ≤ K := by simp only [K]; linarith
        have h2 : (1 : ℝ) ≤ K := by simp only [K]; linarith
        have h3 : KE + |c - b| + |y₀| + |Real.log ‖v‖| + Real.pi + ‖Complex.log v‖ ≤ K := by
          simp only [K]; linarith
        nlinarith
    _ = K * (1 + |z.im| + |Real.log (z.im - (wb κ b).im)|) := by ring

/-- The uniform bound on the strip `b ≤ Re z ≤ c`, for `Im z ≠ Im w_b`:
`‖Γ(z) E_b(z) t^{-z}‖ ≤ C (1+|y|)^{-3} (1 + |y| + |log (y - Im w_b)|)` (RH). -/
theorem lines_norm_integrand_le (hRH : RiemannHypothesis) {κ b c t : ℝ} (hb : 1 / 2 < b)
    (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc b c, ∀ y : ℝ, y ≠ (wb κ b).im →
      ‖Gamma ((σ : ℂ) + y * I) * Eb κ b ((σ : ℂ) + y * I) * (t : ℂ) ^ (-((σ : ℂ) + y * I))‖ ≤
        C * (((1 + |y|) ^ 3)⁻¹ * (1 + |y| + |Real.log (y - (wb κ b).im)|)) := by
  obtain ⟨CΓ, hCΓ⟩ := GoldbachBoundaries.TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le
    (a := b) (a' := c) (by linarith) 3
  obtain ⟨K, hK0, hK⟩ := lines_norm_Eb_le hRH (κ := κ) (c := c) hb
  set T : ℝ := t ^ (-b) + t ^ (-c)
  set C₀ : ℝ := max CΓ 0
  refine ⟨C₀ * K * T, by positivity, fun σ hσ y hy => ?_⟩
  set z : ℂ := (σ : ℂ) + y * I
  have hzre : z.re = σ := by simp [z]
  have hzim : z.im = y := by simp [z]
  have hpos : 0 < (1 + |y|) ^ 3 := by positivity
  have hG : ‖Gamma z‖ ≤ C₀ * ((1 + |y|) ^ 3)⁻¹ := by
    have := hCΓ z (by rw [hzre]; exact hσ.1) (by rw [hzre]; exact hσ.2)
    rw [hzim] at this
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact this.trans (le_max_left _ _)
  have hEb := hK z (by rw [hzre]; exact hσ.1) (by rw [hzre]; exact hσ.2) (by rw [hzim]; exact hy)
  rw [hzim] at hEb
  have htz : ‖(t : ℂ) ^ (-z)‖ ≤ T := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp only [Complex.neg_re, hzre]
    rcases le_or_gt 1 t with h1 | h1
    · have : t ^ (-σ) ≤ t ^ (-b) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hσ.1])
      linarith [Real.rpow_nonneg ht.le (-c)]
    · have : t ^ (-σ) ≤ t ^ (-c) :=
        Real.rpow_le_rpow_of_exponent_ge ht h1.le (by linarith [hσ.2])
      linarith [Real.rpow_nonneg ht.le (-b)]
  set D := ((1 + |y|) ^ 3)⁻¹
  set E := 1 + |y| + |Real.log (y - (wb κ b).im)|
  have hD : 0 ≤ D := by positivity
  have hE : 0 ≤ E := by positivity
  calc ‖Gamma z * Eb κ b z * (t : ℂ) ^ (-z)‖ = ‖Gamma z‖ * ‖Eb κ b z‖ * ‖(t : ℂ) ^ (-z)‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (C₀ * D) * (K * E) * T := by gcongr
    _ = C₀ * K * T * (D * E) := by ring

/-- Measurability of `y ↦ Γ(σ+iy) E_b(σ+iy) t^{-(σ+iy)}` for `σ > 1/2` (RH). -/
theorem lines_aestronglyMeasurable (hRH : RiemannHypothesis) {κ b σ t : ℝ} (hσ : 1 / 2 < σ)
    (ht : 0 < t) :
    AEStronglyMeasurable (fun y : ℝ =>
      Gamma ((σ : ℂ) + y * I) * Eb κ b ((σ : ℂ) + y * I) * (t : ℂ) ^ (-((σ : ℂ) + y * I))) := by
  have hline : Continuous fun y : ℝ => (σ : ℂ) + y * I := by fun_prop
  have hΓ : Measurable fun y : ℝ => Gamma ((σ : ℂ) + y * I) :=
    (GoldbachBoundaries.TIdentity.continuous_Gamma_line (by linarith)).measurable
  have hE : Continuous fun y : ℝ => Eaux ((σ : ℂ) + y * I) :=
    (Eaux_spec hRH).1.continuousOn.comp_continuous hline fun y => by
      show 1 / 2 < ((σ : ℂ) + y * I).re
      simpa using hσ
  have hlog : Measurable fun y : ℝ => Complex.log (((σ : ℂ) + y * I - wb κ b) / slantDir κ) :=
    Complex.measurable_log.comp (by fun_prop : Continuous fun y : ℝ =>
      ((σ : ℂ) + y * I - wb κ b) / slantDir κ).measurable
  have hEb : Measurable fun y : ℝ => Eb κ b ((σ : ℂ) + y * I) := by
    unfold Eb
    exact hE.measurable.sub (hlog.add measurable_const)
  have hcpow : Continuous fun y : ℝ => (t : ℂ) ^ (-((σ : ℂ) + y * I)) :=
    continuous_const.cpow (by fun_prop) fun _ => Or.inl (by exact_mod_cast ht)
  exact ((hΓ.mul hEb).mul hcpow.measurable).aestronglyMeasurable

/-- `Γ E_b t^{-z}` is integrable on every vertical line `Re z = σ ≥ b` (under RH; at `σ = b` the
integrand has the integrable singularity `log |y - Im w_b|`). -/
theorem integrable_Gamma_Eb_line (hRH : RiemannHypothesis) {κ b σ t : ℝ}
    (hb : b ∈ Ioo (1 / 2 : ℝ) 1) (hσ : b ≤ σ) (ht : 0 < t) :
    Integrable fun y : ℝ =>
      Gamma (σ + y * I) * Eb κ b (σ + y * I) * (t : ℂ) ^ (-((σ : ℂ) + y * I)) := by
  obtain ⟨C, -, hC⟩ := lines_norm_integrand_le hRH (κ := κ) (c := σ) hb.1 ht
  refine Integrable.mono' ((dom_integrable_logDom (wb κ b).im).const_mul C)
    (lines_aestronglyMeasurable hRH (lt_of_lt_of_le hb.1 hσ) ht) ?_
  filter_upwards [Measure.ae_ne volume (wb κ b).im] with y hy
  exact hC σ ⟨hσ, le_rfl⟩ y hy

end GroupE

end GoldbachBoundaries.ThmA
