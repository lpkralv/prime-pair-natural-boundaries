import PrimePairNB.HInf.Fill.norm_pairIntegrand_le
import PrimePairNB.HInf.Fill.norm_Pth_le
import PrimePairNB.HInf.Fill.hasDerivAt_Pth

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma outer_Pth_continuousOn (κ : ℝ) : ContinuousOn (Pth κ) (Uth κ) :=
  fun _ hz => (Fill.hasDerivAt_Pth hz).continuousAt.continuousWithinAt

/-- `norm_pairIntegrand_le`, uniformly for `v` in a compact subset of `𝒱`. -/
theorem outer_contour_norm_uniform (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} {K : Set ℂ} (hKc : IsCompact K) (hKV : K ⊆ Vt top)
    {E : Set ℝ} (hE : IsClosed E) {Γ₀ Γ₁ : SlantGraph κ} {ε₀ η : ℝ} (hε₀ : 0 < ε₀) (hη : 0 < η)
    (hre : ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h ∈ E,
      ε₀ ≤ (interpPt Γ₀ Γ₁ l h).re ∧ (interpPt Γ₀ Γ₁ l h).re ≤ v.re - ε₀)
    (hU : ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h ∈ E,
      interpPt Γ₀ Γ₁ l h ∈ Uth κ ∧ v - interpPt Γ₀ Γ₁ l h ∈ Uth κ)
    (hc : ∀ v ∈ K, Binf + 2 * η ≤ Γ₀.c ∧ Binf + 2 * η ≤ Γ₁.c ∧
      Binf + 2 * η ≤ v.re - Γ₀.c ∧ Binf + 2 * η ≤ v.re - Γ₁.c) :
    ∃ M : ℝ, ∀ v ∈ K, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h ∈ E,
      ‖pairIntegrand k κ v (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨T, C, hP⟩ := Fill.norm_Pth_le hZ1 hZ2 hZ3 κ hη
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
  set A : Set (ℂ × ℝ × ℝ) := K ×ˢ (Icc (0 : ℝ) 1 ×ˢ (Icc (-H) H ∩ E)) with hA
  have hAc : IsCompact A := hKc.prod (isCompact_Icc.prod (isCompact_Icc.inter_right hE))
  have hzc : Continuous (fun p : ℂ × ℝ × ℝ => interpPt Γ₀ Γ₁ p.2.1 p.2.2) :=
    (sheet_interp_continuous Γ₀ Γ₁).comp continuous_snd
  have hcont : ContinuousOn
      (fun p : ℂ × ℝ × ℝ => pairIntegrand k κ p.1 (interpPt Γ₀ Γ₁ p.2.1 p.2.2)) A := by
    unfold pairIntegrand
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · refine hK.holo.continuousOn.comp
        (f := fun p : ℂ × ℝ × ℝ => (interpPt Γ₀ Γ₁ p.2.1 p.2.2, p.1))
        (hzc.prodMk continuous_fst).continuousOn ?_
      rintro ⟨v, l, h⟩ ⟨hv, hl, hh⟩
      have := hre v hv l hl h hh.2
      exact ⟨hKV hv, by linarith [this.1], by linarith [this.2]⟩
    · refine (outer_Pth_continuousOn κ).comp hzc.continuousOn ?_
      rintro ⟨v, l, h⟩ ⟨hv, hl, hh⟩
      exact (hU v hv l hl h hh.2).1
    · refine (outer_Pth_continuousOn κ).comp (continuous_fst.sub hzc).continuousOn ?_
      rintro ⟨v, l, h⟩ ⟨hv, hl, hh⟩
      exact (hU v hv l hl h hh.2).2
  obtain ⟨Mc, hMc⟩ := hAc.exists_bound_of_continuousOn hcont
  refine ⟨|Mk| * |C| * |C| * (16 * (8 * (B + 2))) * (1 + S) ^ (3 / 2 : ℝ) +
    |Mc| * (1 + H) ^ (3 / 2 : ℝ), ?_⟩
  intro v hv l hl h hhE
  have hl0 : 0 ≤ l := hl.1
  have hl1 : l ≤ 1 := hl.2
  have hdecpos : 0 ≤ (1 + |h|) ^ (-(3 / 2) : ℝ) := by positivity
  have hQ : 0 ≤ |Mk| * |C| * |C| * (16 * (8 * (B + 2))) * (1 + S) ^ (3 / 2 : ℝ) := by positivity
  have hQ' : 0 ≤ |Mc| * (1 + H) ^ (3 / 2 : ℝ) := by positivity
  by_cases hhH : |h| ≤ H
  · -- compact part
    have hmem : ((v, l, h) : ℂ × ℝ × ℝ) ∈ A := ⟨hv, hl, abs_le.mp hhH, hhE⟩
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
    have hzrng := hre v hv l hl h hhE
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

end GoldbachBoundaries.HInf.Fill
