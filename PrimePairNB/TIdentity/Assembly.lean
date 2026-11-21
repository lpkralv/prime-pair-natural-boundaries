import PrimePairNB.TIdentity.G8c_IntegrableRH
import PrimePairNB.TIdentity.G8d_ContourShift
import PrimePairNB.TIdentity.G9a_FwBasic
import PrimePairNB.TIdentity.G9d_MellinInversion
import PrimePairNB.TIdentity.G9e_SplitQ
import PrimePairNB.TIdentity.G9f_SplitT
import PrimePairNB.TIdentity.G9g_HolomorphyIoc
import PrimePairNB.TIdentity.G9h_HolomorphyIoi

/-!
# The identity for `T` and the pole description of `T`: assembly

Proofs of the two targets from the lemma files in this folder (see `Basic.lean` for the file
map): the trivial estimate on `Re z = b`, step (1) `|h(t)| ≤ C_b t^{-b}` (`norm_hErr_le`),
holomorphy of `R` on `ℍ` (`differentiableOn_Rr`, where RH enters), then `thm_T_identity_proof` and
`cor_T_poles_proof`; the second has the statement of `cor_T_poles` in
`Statements.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-! ## The trivial estimate on `Re z = b` -/

/-- **The trivial estimate on `Re z = b`** (paper, step (1): `|h(t)| ≤ C_b t^{-b}`, with
`C_b = (2π)⁻¹ ∫ |Γ(b+iy)Q(b+iy)| dy`). -/
theorem norm_verticalIntegral'_kernelQ_le (hRH : RiemannHypothesis) {b : ℝ} (hb : 1 / 2 < b)
    (hb1 : b < 1) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖VerticalIntegral' (kernelQ t) b‖ ≤ C * t ^ (-b) := by
  have hint := integrable_Gamma_mul_Qcont_of_RH hRH hb hb1
  set g : ℝ → ℂ := fun y => Gamma (b + y * I) * Qcont (b + y * I) with hg
  refine ⟨(1 / (2 * Real.pi)) * ∫ y, ‖g y‖, fun t ht => ?_⟩
  have hnorm : ∀ y : ℝ, ‖kernelQ t (b + y * I)‖ = t ^ (-b) * ‖g y‖ := by
    intro y
    simp only [kernelQ, norm_mul, hg]
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    simp
  have hI : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  calc ‖VerticalIntegral' (kernelQ t) b‖
      = ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ * ‖∫ y : ℝ, kernelQ t (b + y * I)‖ := by
        simp only [VerticalIntegral', VerticalIntegral, norm_smul]; ring
    _ ≤ 1 / (2 * Real.pi) * ∫ y : ℝ, ‖kernelQ t (b + y * I)‖ := by
        rw [hI]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = 1 / (2 * Real.pi) * (t ^ (-b) * ∫ y : ℝ, ‖g y‖) := by
        rw [integral_congr_ae (Eventually.of_forall hnorm), integral_const_mul]
    _ = 1 / (2 * Real.pi) * (∫ y, ‖g y‖) * t ^ (-b) := by ring

/-! ## Assembly (real proofs) -/

theorem Fw_nonneg (t : ℝ) : 0 ≤ Fw t :=
  tsum_nonneg fun p => mul_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le))
    (Real.exp_pos _).le

theorem continuousOn_hErr : ContinuousOn hErr (Ioi 0) :=
  Fw_continuousOn_and_le_exp.1.sub
    (continuousOn_const.div continuousOn_id fun _ ht => (ne_of_gt (mem_Ioi.mp ht)))

theorem differentiable_e1 : Differentiable ℂ e1 := by
  obtain ⟨hc, C, hC⟩ := Fw_continuousOn_and_le_exp
  refine differentiable_integral_Ioi_cpow (C := C) ?_ fun t ht => ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (hc.mono fun t ht => lt_trans one_pos (mem_Ioi.mp ht))).aestronglyMeasurable measurableSet_Ioi
  · rw [Complex.norm_real, Real.norm_of_nonneg (Fw_nonneg t)]
    exact hC t (le_of_lt ht)

theorem differentiable_E2 : Differentiable ℂ E2 := by
  obtain ⟨hc, C, hC⟩ := Fw_continuousOn_and_le_exp
  refine differentiable_integral_Ioi_cpow (C := C ^ 2) ?_ fun t ht => ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      ((hc.mono fun t ht => lt_trans one_pos (mem_Ioi.mp ht)).pow 2)).aestronglyMeasurable
      measurableSet_Ioi
  · have ht1 : 1 ≤ t := le_of_lt ht
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : Fw t ^ 2 ≤ (C * Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (Fw_nonneg t) (hC t ht1) 2
    have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : (C * Real.exp (-t)) ^ 2 = C ^ 2 * Real.exp (-t) * Real.exp (-t) := by ring
    calc Fw t ^ 2 ≤ C ^ 2 * Real.exp (-t) * Real.exp (-t) := h3 ▸ h1
      _ ≤ C ^ 2 * Real.exp (-t) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ = C ^ 2 * Real.exp (-t) := mul_one _

/-- **Step (1) of the identity for `T`:** under RH, `|h(t)| ≤ C_b t^{-b}` for `t > 0`, `b ∈ (1/2, 1)`. -/
theorem norm_hErr_le (hRH : RiemannHypothesis) {b : ℝ} (hb : 1 / 2 < b) (hb1 : b < 1) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → |hErr t| ≤ C * t ^ (-b) := by
  obtain ⟨C, hC⟩ := norm_verticalIntegral'_kernelQ_le hRH hb hb1
  refine ⟨C, fun t ht => ?_⟩
  have h1 := Fw_eq_verticalIntegral' (c := 2) (by norm_num) ht
  have h2 := verticalIntegral'_kernelQ_shift hRH hb hb1 (by norm_num : (1 : ℝ) < 2) ht
  have heq : ((hErr t : ℝ) : ℂ) = VerticalIntegral' (kernelQ t) b := by
    simp only [hErr]
    push_cast
    rw [h1, h2]
    ring
  have := hC t ht
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-- `R` is holomorphic on `ℍ` under RH (paper, step (3), with `⋃_b {σ > 2b} = ℍ`). -/
theorem differentiableOn_Rr (hRH : RiemannHypothesis) : DifferentiableOn ℂ Rr HH := by
  intro s hs
  have hs1 : 1 < s.re := hs
  set b : ℝ := min ((1 + s.re) / 4) (3 / 4) with hbdef
  have hb : 1 / 2 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h2b : 2 * b < s.re := by
    have : b ≤ (1 + s.re) / 4 := min_le_left _ _
    linarith
  obtain ⟨C, hC⟩ := norm_hErr_le hRH hb hb1
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ))
      (volume.restrict (Ioc 0 1)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_hErr.mono Ioc_subset_Ioi_self).pow 2)).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖((hErr t ^ 2 : ℝ) : ℂ)‖ ≤ C ^ 2 * t ^ (-(2 * b)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : |hErr t| ^ 2 ≤ (C * t ^ (-b)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC t ht0) 2
    rw [sq_abs] at h1
    calc hErr t ^ 2 ≤ (C * t ^ (-b)) ^ 2 := h1
      _ = C ^ 2 * t ^ (-(2 * b)) := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ (-b)) 2, ← Real.rpow_mul ht0.le]
        ring_nf
  have hD := differentiableOn_integral_Ioc_cpow hmeas hbound
  exact (hD.differentiableAt ((isOpen_halfPlane _).mem_nhds h2b)).differentiableWithinAt

end TIdentity

open TIdentity

/-- **The identity for `T`** (statement as in `Statements.lean`). Proved from the Mellin
splittings, the holomorphy lemmas, and `differentiableOn_Rr` (where RH enters). -/
theorem thm_T_identity_proof (hRH : RiemannHypothesis) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H HH ∧
      ∀ s : ℂ, 2 < s.re →
        T s = 2 * Q (s - 1) / (s - 1) - 1 / (Complex.Gamma s * (s - 2)) + H s := by
  refine ⟨fun s => (E2 s - 2 * e1 (s - 1) + Rr s) * (Gamma s)⁻¹, ?_, ?_⟩
  · have he : Differentiable ℂ fun s : ℂ => e1 (s - 1) :=
      differentiable_e1.comp (differentiable_id.sub_const 1)
    exact (((differentiable_E2.differentiableOn).sub
      ((he.const_mul 2).differentiableOn)).add (differentiableOn_Rr hRH)).mul
      differentiable_one_div_Gamma.differentiableOn
  · intro s hs
    have hs1 : 1 < (s - 1).re := by simp; linarith
    have hS1 := Gamma_mul_Q_eq_split hs1
    have hS2 := Gamma_mul_T_eq_split hs
    have hs10 : s - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hs20 : s - 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hΓ : Gamma s = (s - 1) * Gamma (s - 1) := by
      have := Gamma_add_one (s - 1) hs10
      rwa [sub_add_cancel] at this
    have hΓ1 : Gamma (s - 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hΓs : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
    have hm : m1 (s - 1) = Gamma (s - 1) * Q (s - 1) - 1 / (s - 2) - e1 (s - 1) := by
      rw [show s - 1 - 1 = s - 2 by ring] at hS1
      linear_combination -hS1
    have hT : T s = (Gamma s)⁻¹ * (Gamma s * T s) := by field_simp
    show T s = 2 * Q (s - 1) / (s - 1) - 1 / (Gamma s * (s - 2)) +
      (E2 s - 2 * e1 (s - 1) + Rr s) * (Gamma s)⁻¹
    rw [hT, hS2, hm, hΓ]
    field_simp
    ring

/-- `PoleSetQ` shifted by `1` lies in the catalogue (unconditional). -/
theorem one_add_mem_catalogue_of_mem_poleSetQ {a : ℂ} (ha : a ∈ PoleSetQ) : 1 + a ∈ catalogue := by
  rcases ha with (rfl | ⟨k, hk, hsf, rfl⟩) | ⟨n, hn, hsf, ρ, hρ, rfl⟩
  · exact Or.inl (Or.inl (by norm_num))
  · exact Or.inl (Or.inr ⟨k, hk, hsf, rfl⟩)
  · exact Or.inr ⟨n, hn, hsf, ρ, hρ, rfl⟩

/-- The other half: `α ∈ 𝒞 → α - 1 ∈ Σ`. -/
theorem sub_one_mem_poleSetQ_of_mem_catalogue {α : ℂ} (hα : α ∈ catalogue) : α - 1 ∈ PoleSetQ := by
  rcases hα with (rfl | ⟨k, hk, hsf, rfl⟩) | ⟨n, hn, hsf, ρ, hρ, rfl⟩
  · exact Or.inl (Or.inl (by norm_num))
  · exact Or.inl (Or.inr ⟨k, hk, hsf, by ring⟩)
  · exact Or.inr ⟨n, hn, hsf, ρ, hρ, by ring⟩

/-- Product of a function with a residue and a function continuous at the point. -/
theorem HasResidue.mul_continuousAt' {f g : ℂ → ℂ} {a c : ℂ} (hf : HasResidue f a c)
    (hg : ContinuousAt g a) : HasResidue (fun z => f z * g z) a (c * g a) := by
  unfold HasResidue at *
  exact (hf.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)).congr fun z => by ring

/-- The residue of `1/(Γ(s)(s - 2))` at `s = 2` is `1/Γ(2) = 1`. -/
theorem hasResidue_one_div_Gamma_mul_sub_two :
    HasResidue (fun s => 1 / (Gamma s * (s - 2))) 2 1 := by
  have hG2 : Gamma 2 = 1 := by
    have h := Gamma_add_one 1 one_ne_zero
    rw [Gamma_one, mul_one, one_add_one_eq_two] at h
    exact h
  have hc : Tendsto (fun s => (Gamma s)⁻¹) (𝓝[≠] (2 : ℂ)) (𝓝 1) := by
    have := (differentiable_one_div_Gamma.continuous.tendsto (2 : ℂ)).mono_left
      (nhdsWithin_le_nhds (s := {(2 : ℂ)}ᶜ))
    simpa [hG2] using this
  unfold HasResidue
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 2 ≠ 0 := sub_ne_zero.mpr hs
  rw [one_div, mul_inv, ← mul_assoc, mul_comm (s - 2), mul_assoc, mul_inv_cancel₀ hs', mul_one]

/-- **The pole description of `T`** (statement as in `Statements.lean`). Proved from
`thm_T_identity_proof` and `lem_Sigma_i_ii_proof`: the continuation is
`F(s) = 2 Q(s-1)/(s-1) - 1/(Γ(s)(s-2)) + H(s)`, with residue `2 Res_{α-1} Q / (α - 1)` at `α ∈ 𝒞`,
minus `1` at `α = 2`. -/
theorem cor_T_poles_proof (hRH : RiemannHypothesis) :
    ∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ catalogue) ∧
      (∀ α ∈ catalogue, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ catalogue, HasResidue F α (res α)) ∧ HasCatalogueValues res ∧
        ∀ α ∈ catalogue, res α ≠ 0 := by
  obtain ⟨H, hH, hid⟩ := thm_T_identity_proof hRH
  obtain ⟨Qc, hmero, heq, hanal, -, res, hres, hvals, hne⟩ := lem_Sigma_i_ii_proof hRH
  set F : ℂ → ℂ := fun s => 2 * Qc (s - 1) / (s - 1) - 1 / (Gamma s * (s - 2)) + H s with hF
  have hHan : AnalyticOnNhd ℂ H HH := hH.analyticOnNhd (isOpen_halfPlane 1)
  have hGinv : ∀ s, AnalyticAt ℂ (fun s => (Gamma s)⁻¹) s :=
    fun s => differentiable_one_div_Gamma.analyticAt s
  have hterm2 : (fun s : ℂ => 1 / (Gamma s * (s - 2))) = fun s => (Gamma s)⁻¹ * (s - 2)⁻¹ := by
    funext s; rw [one_div, mul_inv]
  have hsub : ∀ s : ℂ, AnalyticAt ℂ (fun s : ℂ => s - 1) s := fun s => by fun_prop
  have hre0 : ∀ s ∈ HH, s - 1 ∈ halfPlane 0 := fun s hs => by
    have : 1 < s.re := hs
    show 0 < (s - 1).re
    simp; linarith
  have hmero2 : ∀ s, MeromorphicAt (fun s : ℂ => 1 / (Gamma s * (s - 2))) s := by
    intro s; rw [hterm2]
    exact (hGinv s).meromorphicAt.mul (analyticAt_id.sub analyticAt_const).meromorphicAt.inv
  have hmeroF : MeromorphicOn F HH := by
    intro s hs
    have h1 : MeromorphicAt (fun s => Qc (s - 1)) s :=
      MeromorphicAt.comp_analyticAt (f := Qc) (g := fun s : ℂ => s - 1) (hmero (s - 1) (hre0 s hs))
        (hsub s)
    exact (((analyticAt_const.meromorphicAt.mul h1).div (hsub s).meromorphicAt).sub (hmero2 s)).add
      (hHan s hs).meromorphicAt
  have hcatHH : ∀ α ∈ catalogue, α ∈ HH := fun α hα => by
    have := re_pos_of_mem_poleSetQ (sub_one_mem_poleSetQ_of_mem_catalogue hα)
    show 1 < α.re
    simp at this; linarith
  have h2cat : (2 : ℂ) ∈ catalogue := Or.inl (Or.inl rfl)
  -- the residue function
  set resF : ℂ → ℂ := fun α => 2 * res (α - 1) / (α - 1) - (if α = 2 then 1 else 0) with hresF
  have hResF : ∀ α ∈ catalogue, HasResidue F α (resF α) := by
    intro α hα
    have ha := sub_one_mem_poleSetQ_of_mem_catalogue hα
    have ha0 : α - 1 ≠ 0 := fun h => by
      have := re_pos_of_mem_poleSetQ ha; rw [h] at this; simp at this
    have h1 : HasResidue (fun s => Qc (s - 1)) α (res (α - 1)) := by
      have := (hres _ ha).comp_sub_const 1
      rwa [sub_add_cancel] at this
    have hcont : ContinuousAt (fun s : ℂ => 2 / (s - 1)) α :=
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) ha0)
    have h1' : HasResidue (fun s => 2 * Qc (s - 1) / (s - 1)) α (2 * res (α - 1) / (α - 1)) := by
      have := h1.mul_continuousAt' hcont
      convert this using 1
      · funext s; ring
      · ring
    have h2 : HasResidue (fun s => 1 / (Gamma s * (s - 2))) α (if α = 2 then 1 else 0) := by
      split_ifs with h
      · subst h; exact hasResidue_one_div_Gamma_mul_sub_two
      · rw [hterm2]
        exact hasResidue_zero_of_analyticAt
          ((hGinv α).mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h)))
    exact (h1'.sub h2).add_analyticAt (hHan α (hcatHH α hα))
  have hres2 : resF 2 = 1 := by
    simp only [hresF, ite_true]
    norm_num [hvals.1]
  have hk2 : ∀ k : ℕ, 2 ≤ k → (1 + 1 / (k : ℂ)) ≠ 2 := by
    intro k hk h
    have h1 : (1 : ℂ) / k = 1 := by linear_combination h
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [div_eq_one_iff_eq hk0] at h1
    have : k = 1 := by exact_mod_cast h1.symm
    omega
  have hρ2 : ∀ n : ℕ, 1 ≤ n → ∀ ρ ∈ NontrivialZeros, (1 + ρ / (n : ℂ)) ≠ 2 := by
    intro n hn ρ hρ h
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have h1 : ρ = n := by
      have : ρ / n = 1 := by linear_combination h
      rwa [div_eq_one_iff_eq hn0] at this
    have := hρ.2.2
    rw [h1] at this
    simp at this
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hresF_ne : ∀ α ∈ catalogue, resF α ≠ 0 := by
    intro α hα
    by_cases h : α = 2
    · rw [h, hres2]; exact one_ne_zero
    · have ha := sub_one_mem_poleSetQ_of_mem_catalogue hα
      have ha0 : α - 1 ≠ 0 := fun h' => by
        have := re_pos_of_mem_poleSetQ ha; rw [h'] at this; simp at this
      simp only [hresF, h, ↓reduceIte, sub_zero]
      exact div_ne_zero (mul_ne_zero two_ne_zero (hne _ ha)) ha0
  refine ⟨F, hmeroF, ?_, ?_, ?_, resF, hResF, ⟨hres2, ?_, ?_⟩, hresF_ne⟩
  · -- agreement with the series on `σ > 2`
    intro s hs
    have hs2 : 2 < s.re := hs
    have hs1 : s - 1 ∈ halfPlane 1 := by
      show 1 < (s - 1).re
      simp; linarith
    simp only [hF]
    rw [hid s hs2, heq hs1]
  · -- analytic off the catalogue
    rintro s ⟨hs, hsc⟩
    have hs1 : 1 < s.re := hs
    have hsP : s - 1 ∉ PoleSetQ := fun h => hsc (by simpa using one_add_mem_catalogue_of_mem_poleSetQ h)
    have hQ : AnalyticAt ℂ (fun s => Qc (s - 1)) s :=
      AnalyticAt.comp (g := Qc) (f := fun s : ℂ => s - 1) (hanal _ ⟨hre0 s hs, hsP⟩) (hsub s)
    have hs1' : s - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hs2' : s ≠ 2 := fun h => hsc (h ▸ h2cat)
    have ht2 : AnalyticAt ℂ (fun s : ℂ => 1 / (Gamma s * (s - 2))) s := by
      rw [hterm2]
      exact (hGinv s).mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs2'))
    exact (((analyticAt_const.mul hQ).div (hsub s) hs1').sub ht2).add (hHan s hs)
  · -- simple poles on the catalogue
    intro α hα
    rw [(hResF α hα).meromorphicOrderAt_eq_neg_one (hmeroF α (hcatHH α hα)) (hresF_ne α hα)]
    rfl
  · -- residue `2μ(k)` at `1 + 1/k`
    intro k hk hsq
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simp only [hresF, hk2 k hk, ↓reduceIte, add_sub_cancel_left, hvals.2.1 k hk hsq, sub_zero]
    field_simp
  · -- residue `-2μ(n)m(ρ)/ρ` at `1 + ρ/n`
    intro n hn hsq ρ hρ
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hρ0 : ρ ≠ 0 := fun h => by have := hρ.2.1; rw [h] at this; simp at this
    simp only [hresF, hρ2 n hn ρ hρ, ↓reduceIte, add_sub_cancel_left, hvals.2.2 n hn hsq ρ hρ,
      sub_zero]
    field_simp

end GoldbachBoundaries
