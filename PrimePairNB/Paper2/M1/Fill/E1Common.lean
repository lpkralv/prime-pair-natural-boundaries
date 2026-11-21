import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.TIdentity.G8d_ContourShift
import PrimePairNB.Paper2.M1.Fill.exists_goodHeight
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.hasResidue_Qcont_Rcoef
import PrimePairNB.Paper2.M1.Fill.norm_KerS_mul_pow_le
import PrimePairNB.Paper2.M1.Fill.norm_Qcont_le_growth
import PrimePairNB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles

/-!
# Shared helpers for the contour shifts

Real proofs of the bound `E1_norm_gs_le_far`, the generic shift of the integrand
`g_s(w) = K_s(w) Q(w) Q(s - w)` between two vertical lines (`E1_shift`), the two pole shapes (left points
`a ∈ Σ_Q` and right points `s - b`), and the bookkeeping of `F_δ` sums. The contour-shift files in this directory
are thin wrappers around these.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The integrand `g_s(w) = K_s(w) Q(w) Q(s - w)`. -/
abbrev E1g (s : ℂ) : ℂ → ℂ := fun w => KerS s w * Qcont w * Qcont (s - w)

/-! ## Analyticity -/

lemma E1_analyticAt_Qcont {z : ℂ} (hz : 0 < z.re) (hp : z ∉ PoleSetQ) : AnalyticAt ℂ Qcont z := by
  simpa using analyticAt_Qcont_sub_sum hz ∅
    (fun n _ hn => regular_of_not_mem_poleSetQ hz hp hn)

lemma E1_differentiableAt_KerS_w {s w : ℂ} (hw : 0 < w.re) (hsw : 0 < (s - w).re) :
    DifferentiableAt ℂ (fun w => KerS s w) w := by
  unfold KerS
  have h1 := TIdentity.differentiableAt_Gamma_of_re_pos hw
  have h2 : DifferentiableAt ℂ (fun w => Gamma (s - w)) w :=
    (TIdentity.differentiableAt_Gamma_of_re_pos hsw).comp w (by fun_prop)
  exact (h1.mul h2).div_const _

lemma E1_differentiableAt_g {s w : ℂ} (hw : 0 < w.re) (hsw : 0 < (s - w).re) (hwP : w ∉ PoleSetQ)
    (hswP : s - w ∉ PoleSetQ) : DifferentiableAt ℂ (E1g s) w := by
  have h1 := E1_differentiableAt_KerS_w hw hsw
  have h2 := (E1_analyticAt_Qcont hw hwP).differentiableAt
  have h3 : DifferentiableAt ℂ (fun w => Qcont (s - w)) w :=
    (E1_analyticAt_Qcont hsw hswP).differentiableAt.comp w (by fun_prop)
  exact (h1.mul h2).mul h3

/-- The principal part at a pole of order at most one, multiplied by a function differentiable at the pole. -/
lemma E1_pole {f φ : ℂ → ℂ} {p r : ℂ} (hm : MeromorphicAt f p) (hr : HasResidue f p r)
    (hφ : DifferentiableAt ℂ φ p) :
    (fun z => φ z * f z - φ p * r / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hsub : MeromorphicAt (fun z : ℂ => z - p) p := (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hh : MeromorphicAt (fun z => (z - p) * f z) p := hsub.mul hm
  have h0 : 0 ≤ meromorphicOrderAt (fun z => (z - p) * f z) p :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hh).1 ⟨r, hr⟩
  obtain ⟨G, hG, hGe⟩ := hh.meromorphicOrderAt_nonneg_iff.1 h0
  have hGp : G p = r := by
    have h1 : Tendsto G (𝓝[≠] p) (𝓝 (G p)) := hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto G (𝓝[≠] p) (𝓝 r) := (tendsto_congr' hGe).1 hr
    exact tendsto_nhds_unique h1 h2
  have hd : DifferentiableAt ℂ (fun z => φ z * G z) p := hφ.mul hG.differentiableAt
  have hB : (dslope (fun z => φ z * G z) p) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    ((continuousAt_dslope_same.mpr hd).tendsto.isBigO_one ℂ).mono nhdsWithin_le_nhds
  refine hB.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin, hGe] with z hz hzG
  have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
  rw [dslope_of_ne _ hz, slope_def_field, hGp, ← hzG]
  field_simp

/-! ## Integrability and horizontal sides from a `(1 + |y|)^{-2}` bound far out -/

lemma E1_integrable_of_bound {g : ℝ → ℂ} (hg : Continuous g) {C Y : ℝ}
    (hb : ∀ y : ℝ, Y ≤ |y| → ‖g y‖ ≤ C / (1 + |y|) ^ 2) : Integrable g := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -|Y|) (b := |Y|)).exists_bound_of_continuousOn
    hg.continuousOn
  set M : ℝ := max C 0 + max B 0 * (1 + |Y|) ^ 2 with hM
  refine Integrable.mono'
    ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul M)
    hg.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + |y| := by positivity
  have hrpow : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg hpos.le]
    norm_cast
  rw [hrpow, ← div_eq_mul_inv]
  have hBn : 0 ≤ max B 0 * (1 + |Y|) ^ 2 := by positivity
  by_cases hy : Y ≤ |y|
  · calc ‖g y‖ ≤ C / (1 + |y|) ^ 2 := hb y hy
      _ ≤ max C 0 / (1 + |y|) ^ 2 := by gcongr; exact le_max_left _ _
      _ ≤ M / (1 + |y|) ^ 2 := by gcongr; rw [hM]; linarith
  · push Not at hy
    have hyY : |y| ≤ |Y| := le_trans hy.le (le_abs_self Y)
    have hmem : y ∈ Icc (-|Y|) |Y| := abs_le.mp hyY
    have h1 : ‖g y‖ ≤ max B 0 := le_trans (hB y hmem) (le_max_left _ _)
    rw [le_div_iff₀ (by positivity)]
    calc ‖g y‖ * (1 + |y|) ^ 2 ≤ max B 0 * (1 + |Y|) ^ 2 := by
          gcongr
      _ ≤ M := by rw [hM]; linarith [le_max_right C 0]

lemma E1_tendsto_inv_sq_abs {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) (K : ℝ) :
    Tendsto (fun y : ℝ => K / (1 + |y|) ^ 2) l (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => (1 + |y|) ^ 2) l atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp (tendsto_atTop_add_const_left _ 1 hl)
  simpa [div_eq_mul_inv] using h1.inv_tendsto_atTop.const_mul K

lemma E1_tendsto_horiz {f : ℂ → ℂ} {c₁ c₂ C Y : ℝ}
    (hb : ∀ x ∈ Icc c₁ c₂, ∀ y : ℝ, Y ≤ |y| → ‖f (x + y * I)‖ ≤ C / (1 + |y|) ^ 2)
    (hc : c₁ ≤ c₂) {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) :
    Tendsto (fun y : ℝ => ∫ x in c₁..c₂, f (x + y * I)) l (𝓝 0) := by
  have hev : ∀ᶠ y : ℝ in l, ‖∫ x in c₁..c₂, f (x + y * I)‖ ≤ C / (1 + |y|) ^ 2 * |c₂ - c₁| := by
    filter_upwards [hl.eventually (eventually_ge_atTop Y)] with y hy
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hc] at hx
    exact hb x ⟨hx.1.le, hx.2⟩ y hy
  refine squeeze_zero_norm' hev ?_
  simpa using (E1_tendsto_inv_sq_abs hl C).mul_const |c₂ - c₁|

/-! ## The integrand far from the real axis -/

/-- The bound on the integrand far from the real axis. -/
lemma E1_norm_gs_le_far (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ : ℝ} (hδ : 0 < δ) {c₁ c₂ σ₁ σ₂ τ₀ : ℝ}
    (hc₁ : Binf + 2 * δ ≤ c₁) (hσ₁ : c₂ + Binf + 2 * δ ≤ σ₁) :
    ∃ C Y : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → |s.im| ≤ τ₀ → ∀ w : ℂ, c₁ ≤ w.re → w.re ≤ c₂ →
      Y ≤ |w.im| → w ∉ PoleSetQ ∧ s - w ∉ PoleSetQ ∧
        ‖KerS s w * Qcont w * Qcont (s - w)‖ ≤ C / (1 + |w.im|) ^ 2 := by
  obtain ⟨H, hH⟩ := exists_goodHeight δ hδ
  obtain ⟨CQ, hCQ⟩ := norm_Qcont_le_growth hZ1 hZ2 hZ3 δ hδ
  have hB := half_le_Binf hZ1
  obtain ⟨CK, hCK⟩ := norm_KerS_mul_pow_le (x₁ := c₁) (x₂ := c₂) (σ₁ := σ₁) (σ₂ := σ₂) (τ₀ := τ₀)
    (by linarith) (by linarith) 4
  refine ⟨CK * |CQ| ^ 2 * (1 + |τ₀|), H + |τ₀|, ?_⟩
  intro s hs1 hs2 hsi w hw1 hw2 hwY
  have hH2 : 2 ≤ H := hH.1
  have hτ : 0 ≤ |τ₀| := abs_nonneg τ₀
  have hsi' : |s.im| ≤ |τ₀| := le_trans hsi (le_abs_self τ₀)
  have hyH : H ≤ |w.im| := by linarith
  obtain ⟨hwP, hQw⟩ := hCQ H hH w (by linarith) hyH
  have hswre : Binf + 2 * δ ≤ (s - w).re := by simp only [sub_re]; linarith
  have hswim1 : |(s - w).im| ≤ |s.im| + |w.im| := by
    simp only [sub_im]; exact abs_sub _ _
  have hswim2 : |w.im| - |s.im| ≤ |(s - w).im| := by
    simp only [sub_im]
    have := abs_sub_abs_le_abs_sub w.im s.im
    rw [abs_sub_comm] at this; linarith
  obtain ⟨hswP, hQsw⟩ := hCQ H hH (s - w) hswre (by linarith)
  refine ⟨hwP, hswP, ?_⟩
  have hK := hCK s hs1 hs2 hsi w hw1 hw2
  set y := |w.im| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have hlogw0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogw : Real.log y ≤ 1 + y := by
    have := Real.log_le_sub_one_of_pos (show 0 < y by linarith); linarith
  have hsw0 : 0 < |(s - w).im| := by linarith
  have hlogsw : Real.log |(s - w).im| ≤ (1 + |τ₀|) * (1 + y) := by
    have := Real.log_le_sub_one_of_pos hsw0
    nlinarith
  have hlogsw0 : 0 ≤ Real.log |(s - w).im| := Real.log_nonneg (by linarith)
  have hQw' : ‖Qcont w‖ ≤ |CQ| * (1 + y) :=
    le_trans hQw (le_trans (mul_le_mul_of_nonneg_right (le_abs_self CQ) hlogw0)
      (mul_le_mul_of_nonneg_left hlogw (abs_nonneg _)))
  have hQsw' : ‖Qcont (s - w)‖ ≤ |CQ| * ((1 + |τ₀|) * (1 + y)) :=
    le_trans hQsw (le_trans (mul_le_mul_of_nonneg_right (le_abs_self CQ) hlogsw0)
      (mul_le_mul_of_nonneg_left hlogsw (abs_nonneg _)))
  have hpos : 0 < 1 + y := by linarith
  rw [le_div_iff₀ (by positivity), norm_mul, norm_mul]
  calc ‖KerS s w‖ * ‖Qcont w‖ * ‖Qcont (s - w)‖ * (1 + y) ^ 2
      ≤ ‖KerS s w‖ * (|CQ| * (1 + y)) * (|CQ| * ((1 + |τ₀|) * (1 + y))) * (1 + y) ^ 2 := by
        gcongr
    _ = (‖KerS s w‖ * (1 + y) ^ 4) * (|CQ| ^ 2 * (1 + |τ₀|)) := by ring
    _ ≤ CK * (|CQ| ^ 2 * (1 + |τ₀|)) := by gcongr
    _ = CK * |CQ| ^ 2 * (1 + |τ₀|) := by ring

/-! ## The shift of `g_s` between two lines -/

/-- Moving the line of `I_c` from `c₂` to `c₁ ≤ c₂` past the finitely many poles `S` of `g_s` in the strip. The
horizontal sides and the integrability on both lines come from `E1_norm_gs_le_far`. -/
lemma E1_shift (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ : ℝ} (hδ : 0 < δ) {c₁ c₂ : ℝ}
    (hc₁ : Binf + 2 * δ ≤ c₁) (hc : c₁ ≤ c₂) {s : ℂ} (hσ : c₂ + Binf + 2 * δ ≤ s.re)
    (S : Finset ℂ) (A : ℂ → ℂ) (hS : ∀ p ∈ S, c₁ < p.re ∧ p.re < c₂)
    (hf : DifferentiableOn ℂ (E1g s) (Icc c₁ c₂ ×ℂ univ \ (S : Set ℂ)))
    (hpole : ∀ p ∈ S, (E1g s - fun w => A p / (w - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    IcQ Qcont c₂ s = ∑ p ∈ S, A p + IcQ Qcont c₁ s := by
  obtain ⟨C, Y, hCY⟩ := E1_norm_gs_le_far (σ₂ := s.re) (τ₀ := |s.im|) hZ1 hZ2 hZ3 hδ hc₁ hσ
  have hb : ∀ x ∈ Icc c₁ c₂, ∀ y : ℝ, Y ≤ |y| → ‖E1g s (x + y * I)‖ ≤ C / (1 + |y|) ^ 2 := by
    intro x hx y hy
    have := (hCY s le_rfl le_rfl le_rfl (x + y * I) (by simpa using hx.1) (by simpa using hx.2)
      (by simpa using hy)).2.2
    simpa using this
  have hline : ∀ x : ℝ, (x = c₁ ∨ x = c₂) → Integrable (fun y : ℝ => E1g s (x + y * I)) := by
    intro x hx
    have hxI : x ∈ Icc c₁ c₂ := by rcases hx with rfl | rfl <;> simp [hc]
    have hcont : Continuous (fun y : ℝ => E1g s (x + y * I)) := by
      refine hf.continuousOn.comp_continuous (by fun_prop) fun y => ⟨?_, ?_⟩
      · rw [mem_reProdIm]; simpa using hxI
      · intro hS'
        have h := hS _ hS'
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
          add_zero] at h
        rcases hx with rfl | rfl <;> simp at h
    exact E1_integrable_of_bound hcont fun y hy => hb x hxI y hy
  unfold IcQ
  exact verticalIntegral'_eq_add_sum_of_simplePoles S A hc hS hf hpole
    (E1_tendsto_horiz hb hc tendsto_abs_atBot_atTop) (E1_tendsto_horiz hb hc tendsto_abs_atTop_atTop)
    (hline c₁ (Or.inl rfl)) (hline c₂ (Or.inr rfl))

/-! ## The two pole shapes of `g_s` -/

/-- At a left point `p ∈ Σ_Q` (with `s - p` regular), `g_s` has a pole of order `≤ 1` with residue
`R_p K_s(p) Q(s - p)`. -/
lemma E1_pole_left {s p : ℂ} (hp : p ∈ PoleSetQ) (hsp : 0 < (s - p).re) (hspP : s - p ∉ PoleSetQ) :
    (E1g s - fun w => Rcoef p * KerS s p * Qcont (s - p) / (w - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hp0 : 0 < p.re := re_pos_of_mem_poleSetQ hp
  have hφ : DifferentiableAt ℂ (fun w => KerS s w * Qcont (s - w)) p :=
    (E1_differentiableAt_KerS_w hp0 hsp).mul
      ((E1_analyticAt_Qcont hsp hspP).differentiableAt.comp p (by fun_prop))
  have h := E1_pole (meromorphicAt_Qcont hp0) (hasResidue_Qcont_Rcoef hp) hφ
  refine h.congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  simp only [Pi.sub_apply, E1g]
  ring

/-- At a right point `p` (`s - p ∈ Σ_Q`, `p` regular), `g_s` has a pole of order `≤ 1` with residue
`-R_{s-p} K_s(s - p) Q(p)` (the derivative of `w ↦ s - w` is `-1`). -/
lemma E1_pole_right {s p : ℂ} (hb : s - p ∈ PoleSetQ) (hp0 : 0 < p.re) (hpP : p ∉ PoleSetQ) :
    (E1g s - fun w => -(Rcoef (s - p) * KerS s (s - p) * Qcont p) / (w - p)) =O[𝓝[≠] p]
      (1 : ℂ → ℂ) := by
  have hb0 : 0 < (s - p).re := re_pos_of_mem_poleSetQ hb
  have hφ : DifferentiableAt ℂ (fun w => KerS s w * Qcont w) p :=
    (E1_differentiableAt_KerS_w hp0 hb0).mul (E1_analyticAt_Qcont hp0 hpP).differentiableAt
  have hm : MeromorphicAt (fun w => Qcont (s - w)) p := by
    have h1 : MeromorphicAt Qcont ((fun w => s - w) p) := meromorphicAt_Qcont hb0
    exact h1.comp_analyticAt (by fun_prop : AnalyticAt ℂ (fun w => s - w) p)
  have hr : HasResidue (fun w => Qcont (s - w)) p (-Rcoef (s - p)) := by
    have h1 := ((hasResidue_Qcont_Rcoef hb).comp_add_const s).comp_const_mul
      (k := -1) (by norm_num)
    have e1 : (s - p - s) / (-1 : ℂ) = p := by ring
    have e2 : Rcoef (s - p) / (-1 : ℂ) = -Rcoef (s - p) := by ring
    rw [e1, e2] at h1
    refine h1.congr (Eventually.of_forall fun w => ?_)
    simp only
    ring_nf
  have h := E1_pole hm hr hφ
  refine h.congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  simp only [Pi.sub_apply, E1g, KerS_sub_symm]
  ring

end GoldbachBoundaries.Paper2.M1
