import PrimePairNB.HInf.MixDefs
import PrimePairNB.HInf.Fill.isPinchKernel_G
import PrimePairNB.HInf.Fill.local_model_sheet

/-! Contour estimates for one logarithmic and one meromorphic prime factor. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

lemma sheet_Qcont_analyticAt {κ : ℝ} {z : ℂ} (hz : z ∈ Uth κ) : AnalyticAt ℂ Qcont z :=
  M1.E1_analyticAt_Qcont hz.1 (Fill.Uth_subset κ hz).2

lemma sheet_Qcont_continuousOn (κ : ℝ) : ContinuousOn Qcont (Uth κ) :=
  fun _ hz => (sheet_Qcont_analyticAt hz).continuousAt.continuousWithinAt

lemma sheet_Qcont_differentiableOn (κ : ℝ) : DifferentiableOn ℂ Qcont (Uth κ) :=
  fun _ hz => (sheet_Qcont_analyticAt hz).differentiableAt.differentiableWithinAt

lemma sheet_Pth_continuousOn (κ : ℝ) : ContinuousOn (Pth κ) (Uth κ) :=
  fun _ hz => (Fill.hasDerivAt_Pth hz).continuousAt.continuousWithinAt

lemma norm_PQ_le (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (κ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ T C : ℝ, ∀ z : ℂ, Binf + 2 * η ≤ z.re → T ≤ |z.im| →
      z ∈ Uth κ ∧ ‖Pth κ z‖ ≤ C * Real.log (|z.im| + 2) ∧
        ‖Qcont z‖ ≤ C * Real.log (|z.im| + 2) := by
  obtain ⟨T, C, hP⟩ := Fill.norm_Pth_le hZ1 hZ2 hZ3 κ hη
  obtain ⟨B, hB⟩ := M1.norm_Qcont_le_growth hZ1 hZ2 hZ3 η hη
  obtain ⟨H, hH⟩ := M1.exists_goodHeight η hη
  refine ⟨max T H, max C (max B 0), fun z hre ht => ?_⟩
  have hp := hP z hre ((le_max_left _ _).trans ht)
  have hq := (hB H hH z hre ((le_max_right _ _).trans ht)).2
  have hlog : 0 ≤ Real.log (|z.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  refine ⟨hp.1, hp.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog), ?_⟩
  have hz2 : 2 ≤ |z.im| := hH.1.trans ((le_max_right _ _).trans ht)
  calc
    ‖Qcont z‖ ≤ B * Real.log |z.im| := hq
    _ ≤ max B 0 * Real.log |z.im| := mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith))
    _ ≤ max B 0 * Real.log (|z.im| + 2) := mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) (by linarith)) (le_max_right _ _)
    _ ≤ max C (max B 0) * Real.log (|z.im| + 2) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hlog

theorem sheet_norm_uniform (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ} {K : Set ℂ} (hKc : IsCompact K) (hKV : K ⊆ Vt ⊤)
    {Γ₀ Γ₁ : SlantGraph κ} {ε₀ η : ℝ} (hε₀ : 0 < ε₀) (hη : 0 < η)
    (hre : ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ε₀ ≤ (interpPt Γ₀ Γ₁ l h).re ∧ (interpPt Γ₀ Γ₁ l h).re ≤ v.re - ε₀)
    (hU : ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      interpPt Γ₀ Γ₁ l h ∈ Uth κ ∧ v - interpPt Γ₀ Γ₁ l h ∈ Uth κ)
    (hc : ∀ v ∈ K, Binf + 2 * η ≤ Γ₀.c ∧ Binf + 2 * η ≤ Γ₁.c ∧
      Binf + 2 * η ≤ v.re - Γ₀.c ∧ Binf + 2 * η ≤ v.re - Γ₁.c) :
    ∃ M : ℝ, ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ‖pairIntegrandMix κ v (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨T, C, hP⟩ := norm_PQ_le hZ1 hZ2 hZ3 κ hη
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
      (fun p : ℂ × ℝ × ℝ => pairIntegrandMix κ p.1 (interpPt Γ₀ Γ₁ p.2.1 p.2.2)) A := by
    unfold pairIntegrandMix
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
    · refine (sheet_Qcont_continuousOn κ).comp (continuous_fst.sub hzc).continuousOn ?_
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
    calc ‖pairIntegrandMix κ v (interpPt Γ₀ Γ₁ l h)‖ ≤ |Mc| := hb
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
    have hP₁ := (hP z (by rw [hzre]; exact hclmin) hy1).2.1
    have hP₂ := (hP (v - z) (by simpa [hzre] using hclmax) hyv).2.2
    have hzrng := hre v hv l hl h
    rw [← hz] at hzrng
    have hkz : ‖kerG z v‖ ≤ Mk / (1 + |z.im|) ^ 2 := by
      have := hMk v hv z.re z.im hzrng.1 hzrng.2
      rwa [Complex.re_add_im] at this
    have hP₂' : ‖Qcont (v - z)‖ ≤ C * Real.log (|v.im - z.im| + 2) := by
      simpa using hP₂
    have hmain := sheet_tail_real (norm_nonneg (Pth κ z))
      (norm_nonneg (Qcont (v - z))) hkz hP₁ hP₂' hB hiv hS hyabs
    unfold pairIntegrandMix
    rw [norm_mul, norm_mul, add_mul]
    exact hmain.trans (le_add_of_nonneg_right (mul_nonneg hQ' hdecpos))

/-- `P^θ(z) P^θ(v-z) 𝒦(z,v)` decays uniformly along all interpolations of two separating graphs. -/
theorem norm_pairIntegrand_le (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf ⊤) {Γ₀ Γ₁ : SlantGraph κ}
    (h₀ : IsSeparating v Γ₀) (h₁ : IsSeparating v Γ₁) :
    ∃ M : ℝ, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ‖pairIntegrandMix κ v (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
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

theorem sheet_Pth_differentiableOn (κ : ℝ) : DifferentiableOn ℂ (Pth κ) (Uth κ) :=
  fun _ hz => (hasDerivAt_Pth hz).differentiableAt.differentiableWithinAt

/-- The integrand is holomorphic in `z`. -/
theorem sheet_pairIntegrand_differentiableOn (hK : IsPinchKernel kerG ⊤ G) (κ : ℝ) {v : ℂ} (hv : v ∈ Vt ⊤) :
    DifferentiableOn ℂ (pairIntegrandMix κ v)
      (Uth κ ∩ ((fun z => v - z) ⁻¹' Uth κ ∩ {z : ℂ | z.re < v.re})) := by
  unfold pairIntegrandMix
  refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
  · refine hK.holo.comp (f := fun z : ℂ => (z, v)) (by fun_prop) ?_
    rintro z ⟨hz, -, hzv⟩
    exact ⟨hv, hz.1, hzv⟩
  · exact (sheet_Pth_differentiableOn κ).mono inter_subset_left
  · refine (sheet_Qcont_differentiableOn κ).comp (f := fun z : ℂ => v - z) (by fun_prop) ?_
    rintro z ⟨-, hz, -⟩
    exact hz

/-- The value does not depend on the separating graph. -/
theorem graphInt_eq_of_separating (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf ⊤) {Γ₀ Γ₁ : SlantGraph κ}
    (h₀ : IsSeparating v Γ₀) (h₁ : IsSeparating v Γ₁) :
    graphInt Γ₀ (pairIntegrandMix κ v) = graphInt Γ₁ (pairIntegrandMix κ v) := by
  obtain ⟨ε₁, hε₁, hmem⟩ := interpPt_mem_of_separating h₀ h₁
  refine graphInt_eq_of_homotopy Γ₀ Γ₁
    (U := Uth κ ∩ ((fun z => v - z) ⁻¹' Uth κ ∩ {z : ℂ | z.re < v.re})) ?_
    (sheet_pairIntegrand_differentiableOn hK κ hv.1) ?_ (norm_pairIntegrand_le hZ1 hZ2 hZ3 hK hv h₀ h₁)
  · refine (isOpen_Uth κ).inter (((isOpen_Uth κ).preimage (by fun_prop)).inter ?_)
    exact isOpen_lt Complex.continuous_re continuous_const
  · intro l hl h
    obtain ⟨a, b, -, c⟩ := hmem l hl h
    exact ⟨a, b, by
      show (interpPt Γ₀ Γ₁ l h).re < v.re
      linarith⟩

/-- `D^θ(v)` is the integral over any separating graph. -/
theorem Dth_eq_graphInt (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hK : IsPinchKernel kerG ⊤ G) {κ : ℝ} {v : ℂ} (hv : v ∈ VInf ⊤) {Γ : SlantGraph κ} (hΓ : IsSeparating v Γ) :
    DthMix κ v = graphInt Γ (pairIntegrandMix κ v) := by
  have hex : ∃ Γ : SlantGraph κ, IsSeparating v Γ := ⟨Γ, hΓ⟩
  unfold DthMix
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact graphInt_eq_of_separating hZ1 hZ2 hZ3 hK hv hex.choose_spec hΓ

end GoldbachBoundaries.HInf.MixProof
