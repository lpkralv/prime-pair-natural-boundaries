import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.hasDerivAt_Pth
import PrimePairNB.HInf.Fill.interpPt_mem_of_separating
import PrimePairNB.HInf.Fill.norm_Pth_le

/-!
# `norm_pairIntegrand_le`

The bound is proved uniformly in `v` over a compact set (`sheet_norm_uniform`), because `Dth_analyticOn` needs it there.
Tails: (K2) gives `(1 + |y|)^{-2}`, `norm_Pth_le` gives two logarithms, each at most a constant times `(1 + |y|)^{1/8}`.
The rest is a continuous function on a compact set inside the domain of holomorphy.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

theorem sheet_slant_re (κ X h : ℝ) : (slantDir κ * ((X : ℂ) + (h : ℂ) * I)).re = X - κ * h := by
  simp [slantDir]

theorem sheet_slant_im (κ X h : ℝ) : (slantDir κ * ((X : ℂ) + (h : ℂ) * I)).im = κ * X + h := by
  simp [slantDir]
  ring

theorem sheet_interp_continuous {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) :
    Continuous (fun p : ℝ × ℝ => interpPt Γ₀ Γ₁ p.1 p.2) := by
  unfold interpPt
  exact continuous_const.mul
    ((Complex.continuous_ofReal.comp
      (((continuous_const.sub continuous_fst).mul (Γ₀.cont.comp continuous_snd)).add
        (continuous_fst.mul (Γ₁.cont.comp continuous_snd)))).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul_const I))

theorem sheet_Pth_continuousOn (κ : ℝ) : ContinuousOn (Pth κ) (Uth κ) :=
  fun _ hz => (hasDerivAt_Pth hz).continuousAt.continuousWithinAt

/-- On the common tails the interpolated point is on the line of the interpolated intercept. -/
theorem sheet_interp_tail {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (l : ℝ) {h : ℝ} (h₀ : Γ₀.T ≤ |h|) (h₁ : Γ₁.T ≤ |h|) :
    (interpPt Γ₀ Γ₁ l h).re = (1 - l) * Γ₀.c + l * Γ₁.c ∧
      (interpPt Γ₀ Γ₁ l h).im = κ * ((1 - l) * Γ₀.c + l * Γ₁.c) + (1 + κ ^ 2) * h := by
  unfold interpPt
  rw [sheet_slant_re, sheet_slant_im, Γ₀.tail h h₀, Γ₁.tail h h₁]
  constructor <;> ring

theorem sheet_log_le {A u : ℝ} (hA : 1 ≤ A) (hu : 1 ≤ u) :
    Real.log (A * u) ≤ 8 * A * u ^ (1 / 8 : ℝ) := by
  have hA0 : 0 ≤ A := by linarith
  have hu0 : 0 ≤ u := by linarith
  have h := Real.log_le_rpow_div (x := A * u) (mul_nonneg hA0 hu0) (ε := 1 / 8) (by norm_num)
  rw [Real.mul_rpow hA0 hu0] at h
  have hA' : A ^ (1 / 8 : ℝ) ≤ A := by
    calc A ^ (1 / 8 : ℝ) ≤ A ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
      _ = A := Real.rpow_one A
  have hup : 0 ≤ u ^ (1 / 8 : ℝ) := Real.rpow_nonneg hu0 _
  calc Real.log (A * u) ≤ A ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ) / (1 / 8) := h
    _ = 8 * (A ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ)) := by ring
    _ ≤ 8 * (A * u ^ (1 / 8 : ℝ)) := by gcongr
    _ = 8 * A * u ^ (1 / 8 : ℝ) := by ring

theorem sheet_decay_real {u w A : ℝ} (hu : 1 ≤ u) (hw : 0 < w) (hA : 0 < A) (hwu : w ≤ A * u) :
    u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ) / u ^ 2 ≤ A ^ (3 / 2 : ℝ) * w ^ (-(3 / 2) : ℝ) := by
  have hu0 : 0 < u := by linarith
  have h1 : u ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ) / u ^ 2 = u ^ (-(7 / 4) : ℝ) := by
    rw [← Real.rpow_add hu0, ← Real.rpow_natCast u 2, ← Real.rpow_sub hu0]
    norm_num
  have h2 : u ^ (-(7 / 4) : ℝ) ≤ u ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu (by norm_num)
  have h3 : w ^ (3 / 2 : ℝ) ≤ A ^ (3 / 2 : ℝ) * u ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow hA.le hu0.le]
    exact Real.rpow_le_rpow hw.le hwu (by norm_num)
  have hwp : 0 < w ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hw _
  have hup : 0 < u ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hu0 _
  rw [h1]
  refine h2.trans ?_
  rw [Real.rpow_neg hu0.le, Real.rpow_neg hw.le, ← div_eq_mul_inv, inv_eq_one_div]
  rw [div_le_div_iff₀ hup hwp]
  linarith

/-- The real inequality of the tails. -/
theorem sheet_tail_real {kn p₁ p₂ Mk C B S h y iv : ℝ} (hp₁0 : 0 ≤ p₁) (hp₂0 : 0 ≤ p₂)
    (hk : kn ≤ Mk / (1 + |y|) ^ 2) (hp₁ : p₁ ≤ C * Real.log (|y| + 2))
    (hp₂ : p₂ ≤ C * Real.log (|iv - y| + 2)) (hB : 0 ≤ B) (hiv : |iv| ≤ B) (hS : 0 ≤ S)
    (hhy : |h| ≤ |y| + S) :
    kn * p₁ * p₂ ≤ (|Mk| * |C| * |C| * (16 * (8 * (B + 2)))) * (1 + S) ^ (3 / 2 : ℝ) *
      (1 + |h|) ^ (-(3 / 2) : ℝ) := by
  set u : ℝ := 1 + |y| with hu
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hu0 : 0 < u := by linarith
  set e : ℝ := u ^ (1 / 8 : ℝ) with he
  have he0 : 0 ≤ e := Real.rpow_nonneg hu0.le _
  have hlog₁ : Real.log (|y| + 2) ≤ 8 * 2 * e := by
    refine le_trans (Real.log_le_log (by linarith) ?_) (sheet_log_le (A := 2) (by norm_num) hu1)
    rw [hu]; linarith
  have hiv' : |iv - y| ≤ B + |y| := (abs_sub iv y).trans (by linarith)
  have hlog₂ : Real.log (|iv - y| + 2) ≤ 8 * (B + 2) * e := by
    refine le_trans (Real.log_le_log (by positivity) ?_)
      (sheet_log_le (A := B + 2) (by linarith) hu1)
    rw [hu]; nlinarith
  have hl₁0 : 0 ≤ Real.log (|y| + 2) := Real.log_nonneg (by linarith)
  have hl₂0 : 0 ≤ Real.log (|iv - y| + 2) := Real.log_nonneg (by linarith [abs_nonneg (iv - y)])
  have hp₁' : p₁ ≤ |C| * (8 * 2 * e) :=
    hp₁.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) hl₁0).trans
      (mul_le_mul_of_nonneg_left hlog₁ (abs_nonneg C)))
  have hp₂' : p₂ ≤ |C| * (8 * (B + 2) * e) :=
    hp₂.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) hl₂0).trans
      (mul_le_mul_of_nonneg_left hlog₂ (abs_nonneg C)))
  have hk' : kn ≤ |Mk| / u ^ 2 :=
    hk.trans (div_le_div_of_nonneg_right (le_abs_self Mk) (by positivity))
  have hprod : kn * p₁ * p₂ ≤ (|Mk| / u ^ 2) * (|C| * (8 * 2 * e)) * (|C| * (8 * (B + 2) * e)) := by
    have h1 : kn * p₁ ≤ (|Mk| / u ^ 2) * (|C| * (8 * 2 * e)) :=
      mul_le_mul hk' hp₁' hp₁0 (by positivity)
    exact mul_le_mul h1 hp₂' hp₂0 (by positivity)
  have hdecay := sheet_decay_real (u := u) (w := 1 + |h|) (A := 1 + S) hu1
    (by positivity) (by positivity) (by rw [hu]; nlinarith [abs_nonneg h])
  rw [← he] at hdecay
  have hQ : 0 ≤ |Mk| * |C| * |C| * (16 * (8 * (B + 2))) := by positivity
  calc kn * p₁ * p₂ ≤ (|Mk| / u ^ 2) * (|C| * (8 * 2 * e)) * (|C| * (8 * (B + 2) * e)) := hprod
    _ = (|Mk| * |C| * |C| * (16 * (8 * (B + 2)))) * (e * e / u ^ 2) := by ring
    _ ≤ (|Mk| * |C| * |C| * (16 * (8 * (B + 2)))) *
        ((1 + S) ^ (3 / 2 : ℝ) * (1 + |h|) ^ (-(3 / 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay hQ
    _ = _ := by ring

/-- `norm_pairIntegrand_le`, uniformly for `v` in a compact subset of `𝒱`. -/
theorem sheet_norm_uniform (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {K : Set ℂ} (hKc : IsCompact K) (hKV : K ⊆ Vt top)
    {Γ₀ Γ₁ : SlantGraph κ} {ε₀ η : ℝ} (hε₀ : 0 < ε₀) (hη : 0 < η)
    (hre : ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ε₀ ≤ (interpPt Γ₀ Γ₁ l h).re ∧ (interpPt Γ₀ Γ₁ l h).re ≤ v.re - ε₀)
    (hU : ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      interpPt Γ₀ Γ₁ l h ∈ Uth κ ∧ v - interpPt Γ₀ Γ₁ l h ∈ Uth κ)
    (hc : ∀ v ∈ K, Binf + 2 * η ≤ Γ₀.c ∧ Binf + 2 * η ≤ Γ₁.c ∧
      Binf + 2 * η ≤ v.re - Γ₀.c ∧ Binf + 2 * η ≤ v.re - Γ₁.c) :
    ∃ M : ℝ, ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ‖pairIntegrand k κ v (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨T, C, hP⟩ := norm_Pth_le hZ1 hZ2 hZ3 κ hη
  obtain ⟨Mk, hMk⟩ := hK.decay K hKc hKV ε₀ hε₀
  obtain ⟨B₀, hB₀⟩ := hKc.isBounded.exists_norm_le
  set B : ℝ := max B₀ 0 with hBdef
  have hB : 0 ≤ B := le_max_right _ _
  have hvB : ∀ v ∈ K, |v.im| ≤ B := fun v hv =>
    (Complex.abs_im_le_norm v).trans ((hB₀ v hv).trans (le_max_left _ _))
  set S : ℝ := |κ| * max |Γ₀.c| |Γ₁.c| with hSdef
  have hS : 0 ≤ S := by positivity
  set H : ℝ := max Γ₀.T 0 + max Γ₁.T 0 + |T| + S + B with hHdef
  have hH0 : 0 ≤ H := by positivity
  -- the compact part
  set A : Set (ℂ × ℝ × ℝ) := K ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (-H) H) with hA
  have hAc : IsCompact A := hKc.prod (isCompact_Icc.prod isCompact_Icc)
  have hzc : Continuous (fun p : ℂ × ℝ × ℝ => interpPt Γ₀ Γ₁ p.2.1 p.2.2) :=
    (sheet_interp_continuous Γ₀ Γ₁).comp continuous_snd
  have hcont : ContinuousOn
      (fun p : ℂ × ℝ × ℝ => pairIntegrand k κ p.1 (interpPt Γ₀ Γ₁ p.2.1 p.2.2)) A := by
    unfold pairIntegrand
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · refine hK.holo.continuousOn.comp
        (f := fun p : ℂ × ℝ × ℝ => (interpPt Γ₀ Γ₁ p.2.1 p.2.2, p.1))
        (hzc.prodMk continuous_fst).continuousOn ?_
      rintro ⟨v, l, h⟩ ⟨hv, hl, -⟩
      have := hre v hv l hl h
      exact ⟨hKV hv, by linarith [this.1], by linarith [this.2]⟩
    · refine (sheet_Pth_continuousOn κ).comp hzc.continuousOn ?_
      rintro ⟨v, l, h⟩ ⟨hv, hl, -⟩
      exact (hU v hv l hl h).1
    · refine (sheet_Pth_continuousOn κ).comp (continuous_fst.sub hzc).continuousOn ?_
      rintro ⟨v, l, h⟩ ⟨hv, hl, -⟩
      exact (hU v hv l hl h).2
  obtain ⟨Mc, hMc⟩ := hAc.exists_bound_of_continuousOn hcont
  refine ⟨|Mk| * |C| * |C| * (16 * (8 * (B + 2))) * (1 + S) ^ (3 / 2 : ℝ) +
    |Mc| * (1 + H) ^ (3 / 2 : ℝ), ?_⟩
  intro v hv l hl h
  have hl0 : 0 ≤ l := hl.1
  have hl1 : l ≤ 1 := hl.2
  have hdecpos : 0 ≤ (1 + |h|) ^ (-(3 / 2) : ℝ) := by positivity
  have hQ : 0 ≤ |Mk| * |C| * |C| * (16 * (8 * (B + 2))) * (1 + S) ^ (3 / 2 : ℝ) := by positivity
  have hQ' : 0 ≤ |Mc| * (1 + H) ^ (3 / 2 : ℝ) := by positivity
  by_cases hhH : |h| ≤ H
  · -- compact part
    have hmem : ((v, l, h) : ℂ × ℝ × ℝ) ∈ A := ⟨hv, hl, abs_le.mp hhH⟩
    have hb := (hMc _ hmem).trans (le_abs_self Mc)
    have hone : 1 ≤ (1 + H) ^ (3 / 2 : ℝ) * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
      have hh0 : 0 < 1 + |h| := by positivity
      rw [Real.rpow_neg hh0.le, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact Real.rpow_le_rpow hh0.le (by linarith) (by norm_num)
    calc ‖pairIntegrand k κ v (interpPt Γ₀ Γ₁ l h)‖ ≤ |Mc| := hb
      _ ≤ |Mc| * ((1 + H) ^ (3 / 2 : ℝ) * (1 + |h|) ^ (-(3 / 2) : ℝ)) :=
        le_mul_of_one_le_right (abs_nonneg _) hone
      _ = (|Mc| * (1 + H) ^ (3 / 2 : ℝ)) * (1 + |h|) ^ (-(3 / 2) : ℝ) := by ring
      _ ≤ _ := by
        rw [add_mul]
        exact le_add_of_nonneg_left (mul_nonneg hQ hdecpos)
  · -- tails
    have hhH' : H < |h| := lt_of_not_ge hhH
    have hT₀ : Γ₀.T ≤ |h| := by
      have := le_max_left Γ₀.T 0
      have := le_max_right Γ₁.T 0
      have := abs_nonneg T
      linarith
    have hT₁ : Γ₁.T ≤ |h| := by
      have := le_max_left Γ₁.T 0
      have := le_max_right Γ₀.T 0
      have := abs_nonneg T
      linarith
    set z := interpPt Γ₀ Γ₁ l h with hz
    obtain ⟨hzre, hzim⟩ := sheet_interp_tail Γ₀ Γ₁ l hT₀ hT₁
    rw [← hz] at hzre hzim
    set cl : ℝ := (1 - l) * Γ₀.c + l * Γ₁.c with hcl
    obtain ⟨hc₀, hc₁, hc₂, hc₃⟩ := hc v hv
    have hclmin : Binf + 2 * η ≤ cl := by
      rw [hcl]
      nlinarith [mul_le_mul_of_nonneg_left hc₀ (sub_nonneg.mpr hl1),
        mul_le_mul_of_nonneg_left hc₁ hl0]
    have hclmax : Binf + 2 * η ≤ v.re - cl := by
      have e1 := mul_le_mul_of_nonneg_left hc₂ (sub_nonneg.mpr hl1)
      have e2 := mul_le_mul_of_nonneg_left hc₃ hl0
      rw [hcl]
      nlinarith
    have hclabs : |cl| ≤ max |Γ₀.c| |Γ₁.c| := by
      rw [hcl]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hl1), abs_of_nonneg hl0]
      have e1 := mul_le_mul_of_nonneg_left (le_max_left |Γ₀.c| |Γ₁.c|) (sub_nonneg.mpr hl1)
      have e2 := mul_le_mul_of_nonneg_left (le_max_right |Γ₀.c| |Γ₁.c|) hl0
      nlinarith
    have hκcl : |κ * cl| ≤ S := by
      rw [abs_mul, hSdef]
      exact mul_le_mul_of_nonneg_left hclabs (abs_nonneg κ)
    have hh_le : |(1 + κ ^ 2) * h| = (1 + κ ^ 2) * |h| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have hyabs : |h| ≤ |z.im| + S := by
      have e1 : (1 + κ ^ 2) * h = z.im - κ * cl := by rw [hzim]; ring
      have e2 : |(1 + κ ^ 2) * h| ≤ |z.im| + |κ * cl| := by
        rw [e1]; exact abs_sub _ _
      rw [hh_le] at e2
      nlinarith [abs_nonneg h, sq_nonneg κ]
    have hiv := hvB v hv
    have hTabs := le_abs_self T
    have hy1 : T ≤ |z.im| := by
      have := le_max_right Γ₀.T 0
      have := le_max_right Γ₁.T 0
      linarith
    have hyv : T ≤ |(v - z).im| := by
      have e0 : z.im = v.im - (v - z).im := by simp
      have e1 : |z.im| ≤ |v.im| + |(v - z).im| := by
        rw [e0]; exact abs_sub _ _
      have := le_max_right Γ₀.T 0
      have := le_max_right Γ₁.T 0
      linarith
    have hP₁ := (hP z (by rw [hzre]; exact hclmin) hy1).2
    have hP₂ := (hP (v - z) (by simpa [hzre] using hclmax) hyv).2
    have hzrng := hre v hv l hl h
    rw [← hz] at hzrng
    have hkz : ‖k z v‖ ≤ Mk / (1 + |z.im|) ^ 2 := by
      have := hMk v hv z.re z.im hzrng.1 hzrng.2
      rwa [Complex.re_add_im] at this
    have hP₂' : ‖Pth κ (v - z)‖ ≤ C * Real.log (|v.im - z.im| + 2) := by
      simpa using hP₂
    have hmain := sheet_tail_real (norm_nonneg (Pth κ z))
      (norm_nonneg (Pth κ (v - z))) hkz hP₁ hP₂' hB hiv hS hyabs
    unfold pairIntegrand
    rw [norm_mul, norm_mul, add_mul]
    exact hmain.trans (le_add_of_nonneg_right (mul_nonneg hQ' hdecpos))

/-- `P^θ(z) P^θ(v-z) 𝒦(z,v)` decays uniformly along all interpolations of two separating graphs. -/
theorem norm_pairIntegrand_le (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf top) {Γ₀ Γ₁ : SlantGraph κ}
    (h₀ : IsSeparating v Γ₀) (h₁ : IsSeparating v Γ₁) :
    ∃ M : ℝ, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ‖pairIntegrand k κ v (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨ε₁, hε₁, hmem⟩ := interpPt_mem_of_separating h₀ h₁
  set η : ℝ := min (min (Γ₀.c - Binf) (Γ₁.c - Binf))
    (min (v.re - Binf - Γ₀.c) (v.re - Binf - Γ₁.c)) / 2 with hηdef
  have hη : 0 < η := by
    have a₀ := h₀.tail_c
    have a₁ := h₁.tail_c
    apply half_pos
    simp only [lt_min_iff, sub_pos]
    exact ⟨⟨a₀.1, a₁.1⟩, ⟨by linarith [a₀.2], by linarith [a₁.2]⟩⟩
  have hη2 : 2 * η = min (min (Γ₀.c - Binf) (Γ₁.c - Binf))
      (min (v.re - Binf - Γ₀.c) (v.re - Binf - Γ₁.c)) := by rw [hηdef]; ring
  have m₁ := min_le_left (min (Γ₀.c - Binf) (Γ₁.c - Binf)) (min (v.re - Binf - Γ₀.c) (v.re - Binf - Γ₁.c))
  have m₂ := min_le_right (min (Γ₀.c - Binf) (Γ₁.c - Binf)) (min (v.re - Binf - Γ₀.c) (v.re - Binf - Γ₁.c))
  have m₃ := min_le_left (Γ₀.c - Binf) (Γ₁.c - Binf)
  have m₄ := min_le_right (Γ₀.c - Binf) (Γ₁.c - Binf)
  have m₅ := min_le_left (v.re - Binf - Γ₀.c) (v.re - Binf - Γ₁.c)
  have m₆ := min_le_right (v.re - Binf - Γ₀.c) (v.re - Binf - Γ₁.c)
  obtain ⟨M, hM⟩ := sheet_norm_uniform hZ1 hZ2 hZ3 hK (K := {v}) isCompact_singleton
    (singleton_subset_iff.mpr hv.1) (Γ₀ := Γ₀) (Γ₁ := Γ₁) hε₁ hη
    (by
      rintro _ rfl l hl h
      exact ⟨(hmem l hl h).2.2.1, (hmem l hl h).2.2.2⟩)
    (by
      rintro _ rfl l hl h
      exact ⟨(hmem l hl h).1, (hmem l hl h).2.1⟩)
    (by
      rintro _ rfl
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩)
  exact ⟨M, hM v rfl⟩

end GoldbachBoundaries.HInf.Fill

