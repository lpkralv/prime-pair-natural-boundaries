import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.graphInt_line
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

private def velocity {κ : ℝ} (Γ : SlantGraph κ) (h : ℝ) : ℂ :=
  slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I)

private def connector {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (f : ℂ → ℂ) (h : ℝ) : ℂ :=
  (slantDir κ * ((Γ₁.ξ h - Γ₀.ξ h : ℝ) : ℂ)) *
    ∫ l in (0 : ℝ)..1, f (interpPt Γ₀ Γ₁ l h)

private theorem interp_continuous {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) :
    Continuous (fun p : ℝ × ℝ => interpPt Γ₀ Γ₁ p.2 p.1) := by
  unfold interpPt
  exact continuous_const.mul
    ((Complex.continuous_ofReal.comp
      (((continuous_const.sub continuous_snd).mul (Γ₀.cont.comp continuous_fst)).add
        (continuous_snd.mul (Γ₁.cont.comp continuous_fst)))).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul_const I))

/-- The horizontal displacement is uniformly bounded: on the common tails it
is the constant difference of the two line intercepts. -/
private theorem graph_gap_bounded {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |Γ₁.ξ h - Γ₀.ξ h| ≤ C := by
  let T := max (max Γ₀.T Γ₁.T) 0
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (Γ₁.cont.sub Γ₀.cont).continuousOn
  refine ⟨max (max B 0) |Γ₁.c - Γ₀.c|,
    (le_max_right B 0).trans (le_max_left _ _), ?_⟩
  intro h
  by_cases hh : |h| ≤ T
  · simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hB h (abs_le.mp hh)).trans
      ((le_max_left B 0).trans (le_max_left _ _))
  · have hT : T ≤ |h| := le_of_lt (lt_of_not_ge hh)
    rw [Γ₀.tail h ((le_max_left Γ₀.T Γ₁.T).trans ((le_max_left _ _).trans hT)),
      Γ₁.tail h ((le_max_right Γ₀.T Γ₁.T).trans ((le_max_left _ _).trans hT))]
    simpa only [add_sub_add_right_eq_sub] using le_max_right (max B 0) |Γ₁.c - Γ₀.c|

private theorem decay_integrable : Integrable (fun h : ℝ => (1 + |h|) ^ (-(3 / 2) : ℝ)) := by
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num))

private theorem graph_integrable {κ : ℝ} (Γ : SlantGraph κ) {f : ℂ → ℂ}
    (hcont : Continuous (fun h => f (Γ.pt h))) {M : ℝ}
    (hdec : ∀ h : ℝ, ‖f (Γ.pt h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ)) :
    Integrable (fun h : ℝ => f (Γ.pt h) * velocity Γ h) := by
  obtain ⟨L, hL⟩ := Γ.lip
  have hm : AEStronglyMeasurable (fun h => f (Γ.pt h) * velocity Γ h) volume :=
    hcont.aestronglyMeasurable.mul
    (((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_deriv Γ.ξ volume)).add_const I).const_mul (slantDir κ))
  apply (decay_integrable.const_mul (M * (‖slantDir κ‖ * (max L 0 + 1)))).mono' hm
  filter_upwards [(show ∀ᵐ h : ℝ, h ∉ Γ.brk from ae_iff.mpr (by simpa using Γ.brk.finite_toSet.measure_zero volume))] with h hh
  have hv : ‖velocity Γ h‖ ≤ ‖slantDir κ‖ * (max L 0 + 1) := by
    unfold velocity
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_add_le _ _).trans
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_I]
    exact add_le_add ((hL h hh).trans (le_max_left L 0)) (le_refl 1)
  change ‖f (Γ.pt h) * velocity Γ h‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (M * (1 + |h|) ^ (-(3 / 2) : ℝ)) * (‖slantDir κ‖ * (max L 0 + 1)) :=
      mul_le_mul (hdec h) hv (norm_nonneg _) ((norm_nonneg _).trans (hdec h))
    _ = _ := by ring

/-- FTC off the union of break sets gives the finite-height contour identity.
The sole analytic input here is the derivative of the connector. -/
private theorem finite_contour_identity {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (f : ℂ → ℂ)
    (hc : Continuous (connector Γ₀ Γ₁ f))
    (hd : ∀ h : ℝ, h ∉ Γ₀.brk → h ∉ Γ₁.brk →
      HasDerivAt (connector Γ₀ Γ₁ f)
        (f (Γ₁.pt h) * velocity Γ₁ h - f (Γ₀.pt h) * velocity Γ₀ h) h)
    (hi₀ : Integrable (fun h : ℝ => f (Γ₀.pt h) * velocity Γ₀ h))
    (hi₁ : Integrable (fun h : ℝ => f (Γ₁.pt h) * velocity Γ₁ h)) (T : ℝ) :
    (∫ h in -T..T, f (Γ₁.pt h) * velocity Γ₁ h - f (Γ₀.pt h) * velocity Γ₀ h) =
      connector Γ₀ Γ₁ f T - connector Γ₀ Γ₁ f (-T) := by
  apply integral_eq_of_hasDerivAt_off_countable _ _
    (s := (Γ₀.brk ∪ Γ₁.brk : Finset ℝ)) (Finset.finite_toSet _).countable hc.continuousOn
  · intro h hh
    have hn : h ∉ Γ₀.brk ∧ h ∉ Γ₁.brk := by simpa using hh.2
    exact hd h hn.1 hn.2
  · exact (hi₁.sub hi₀).intervalIntegrable

private def clamp (l : ℝ) : ℝ := max 0 (min 1 l)

private theorem clamp_mem (l : ℝ) : clamp l ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem clamp_eq {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) : clamp l = l := by
  simp [clamp, min_eq_right hl.2, max_eq_right hl.1]

private theorem swept_continuous {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U)
    (hmem : ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ, interpPt Γ₀ Γ₁ l h ∈ U) :
    Continuous (fun p : ℝ × ℝ => f (interpPt Γ₀ Γ₁ (clamp p.2) p.1)) := by
  apply ContinuousOn.comp_continuous hf
  · exact (interp_continuous Γ₀ Γ₁).comp
      (continuous_fst.prodMk (continuous_const.max (continuous_const.min continuous_snd)))
  · exact fun p => hmem _ (clamp_mem _) _

private theorem connector_continuous {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {U : Set ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U)
    (hmem : ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ, interpPt Γ₀ Γ₁ l h ∈ U) :
    Continuous (connector Γ₀ Γ₁ f) := by
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun h l => f (interpPt Γ₀ Γ₁ (clamp l) h))
    (swept_continuous Γ₀ Γ₁ hf hmem) (0 : ℝ) 1
  have he (h : ℝ) : (∫ l in (0 : ℝ)..1, f (interpPt Γ₀ Γ₁ (clamp l) h)) =
      ∫ l in (0 : ℝ)..1, f (interpPt Γ₀ Γ₁ l h) := by
    apply intervalIntegral.integral_congr
    intro l hl
    simp only [clamp_eq (by simpa using hl)]
  simp_rw [he] at hc
  exact (continuous_const.mul (Complex.continuous_ofReal.comp (Γ₁.cont.sub Γ₀.cont))).mul hc

private theorem connector_bound {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {f : ℂ → ℂ} {M C : ℝ}
    (hC : 0 ≤ C) (hgap : ∀ h : ℝ, |Γ₁.ξ h - Γ₀.ξ h| ≤ C)
    (hdec : ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ‖f (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ)) (h : ℝ) :
    ‖connector Γ₀ Γ₁ f h‖ ≤ (‖slantDir κ‖ * C * M) * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
  have hi : ‖∫ l in (0 : ℝ)..1, f (interpPt Γ₀ Γ₁ l h)‖ ≤
      M * (1 + |h|) ^ (-(3 / 2) : ℝ) := by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (fun l hl => hdec l (by simpa using (uIoc_subset_uIcc hl)) h)
  unfold connector
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (‖slantDir κ‖ * C) * (M * (1 + |h|) ^ (-(3 / 2) : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hgap h) (norm_nonneg _)) hi
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC)
    _ = _ := by ring

/-- Once the connector derivative is known, FTC on `[-T,T]` and the decay of
the endpoint connectors imply equality of the full Bochner integrals. -/
private theorem infinite_contour_identity {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {f : ℂ → ℂ}
    (hc : Continuous (connector Γ₀ Γ₁ f))
    (hd : ∀ h : ℝ, h ∉ Γ₀.brk → h ∉ Γ₁.brk →
      HasDerivAt (connector Γ₀ Γ₁ f)
        (f (Γ₁.pt h) * velocity Γ₁ h - f (Γ₀.pt h) * velocity Γ₀ h) h)
    (hi₀ : Integrable (fun h : ℝ => f (Γ₀.pt h) * velocity Γ₀ h))
    (hi₁ : Integrable (fun h : ℝ => f (Γ₁.pt h) * velocity Γ₁ h))
    (hdec : ∃ M : ℝ, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ‖f (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ)) :
    graphInt Γ₀ f = graphInt Γ₁ f := by
  obtain ⟨M, hM⟩ := hdec
  obtain ⟨C, hC, hgap⟩ := graph_gap_bounded Γ₀ Γ₁
  have hb := connector_bound Γ₀ Γ₁ hC hgap hM
  have ht : Tendsto (connector Γ₀ Γ₁ f) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun h => hb h)
    convert ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_abs_atTop_atTop)).const_mul (‖slantDir κ‖ * C * M) using 1 <;> simp
  have hbot : Tendsto (connector Γ₀ Γ₁ f) atBot (𝓝 0) := by
    apply squeeze_zero_norm (fun h => hb h)
    convert ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
      (tendsto_atTop_add_const_left atBot 1 tendsto_abs_atBot_atTop)).const_mul (‖slantDir κ‖ * C * M) using 1 <;> simp
  have hlim := intervalIntegral_tendsto_integral (hi₁.sub hi₀)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hz : (∫ h : ℝ, f (Γ₁.pt h) * velocity Γ₁ h - f (Γ₀.pt h) * velocity Γ₀ h) = 0 := by
    apply tendsto_nhds_unique hlim
    simpa only [sub_zero, Pi.sub_apply, id_eq] using (ht.sub (hbot.comp tendsto_neg_atTop_atBot)).congr
      (fun T => (finite_contour_identity Γ₀ Γ₁ f hc hd hi₀ hi₁ T).symm)
  rw [integral_sub hi₁ hi₀, sub_eq_zero] at hz
  unfold graphInt
  exact congrArg (fun z : ℂ => (1 / (2 * (Real.pi : ℂ) * I)) * z) hz.symm

private def interpVelocity {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (h l : ℝ) : ℂ :=
  slantDir κ * (((((1 - l) * deriv Γ₀.ξ h + l * deriv Γ₁.ξ h) : ℝ) : ℂ) + I)

private theorem interp_hasDerivAt {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {h : ℝ}
    (hh₀ : h ∉ Γ₀.brk) (hh₁ : h ∉ Γ₁.brk) (l : ℝ) :
    HasDerivAt (fun h => interpPt Γ₀ Γ₁ l h) (interpVelocity Γ₀ Γ₁ h l) h := by
  simpa only [interpPt, interpVelocity, Pi.add_apply, Complex.ofReal_one, one_mul, id_eq] using
    (((((Γ₀.diff h hh₀).hasDerivAt.const_mul (1 - l)).add
    ((Γ₁.diff h hh₁).hasDerivAt.const_mul l)).ofReal_comp).add
      ((hasDerivAt_id h).ofReal_comp.mul_const I)).const_mul (slantDir κ)

private theorem interpVelocity_bound {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {L₀ L₁ h l : ℝ}
    (hL₀ : |deriv Γ₀.ξ h| ≤ L₀) (hL₁ : |deriv Γ₁.ξ h| ≤ L₁)
    (hl : l ∈ Icc (0 : ℝ) 1) :
    ‖interpVelocity Γ₀ Γ₁ h l‖ ≤ ‖slantDir κ‖ * (|L₀| + |L₁| + 1) := by
  unfold interpVelocity
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_add_le _ _).trans
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_I]
  apply add_le_add _ (le_refl 1)
  calc
    _ ≤ |1 - l| * |deriv Γ₀.ξ h| + |l| * |deriv Γ₁.ξ h| := by
      simpa only [abs_mul] using abs_add_le ((1 - l) * deriv Γ₀.ξ h) (l * deriv Γ₁.ξ h)
    _ ≤ 1 * |L₀| + 1 * |L₁| := by
      apply add_le_add
      · apply mul_le_mul _ (hL₀.trans (le_abs_self _)) (abs_nonneg _) (by norm_num)
        rw [abs_of_nonneg (by linarith [hl.2] : 0 ≤ 1 - l)]
        linarith [hl.1]
      · apply mul_le_mul _ (hL₁.trans (le_abs_self _)) (abs_nonneg _) (by norm_num)
        simpa [abs_of_nonneg hl.1] using hl.2
    _ = _ := by ring

/-- Differentiate the joining segment in height, and identify the derivative
by FTC in the interpolation parameter. No second derivative of a graph is used. -/
private theorem connector_hasDerivAt {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hmem : ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ, interpPt Γ₀ Γ₁ l h ∈ U)
    {h : ℝ} (hh₀ : h ∉ Γ₀.brk) (hh₁ : h ∉ Γ₁.brk) :
    HasDerivAt (connector Γ₀ Γ₁ f)
      (f (Γ₁.pt h) * velocity Γ₁ h - f (Γ₀.pt h) * velocity Γ₀ h) h := by
  classical
  let A (x l : ℝ) := f (interpPt Γ₀ Γ₁ (clamp l) x)
  let A' (x l : ℝ) := deriv f (interpPt Γ₀ Γ₁ (clamp l) x) *
    interpVelocity Γ₀ Γ₁ x (clamp l)
  have hcA : Continuous (Function.uncurry A) := swept_continuous Γ₀ Γ₁ hf.continuousOn hmem
  have hcf' := swept_continuous Γ₀ Γ₁ (hf.deriv hU).continuousOn hmem
  obtain ⟨L₀, hL₀⟩ := Γ₀.lip
  obtain ⟨L₁, hL₁⟩ := Γ₁.lip
  obtain ⟨B, hB⟩ := ((isCompact_closedBall h 1).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    hcf'.continuousOn
  let s : Set ℝ := ball h 1 ∩ ((Γ₀.brk ∪ Γ₁.brk : Finset ℝ) : Set ℝ)ᶜ
  have hs : s ∈ 𝓝 h := by
    apply inter_mem (ball_mem_nhds h (by norm_num))
    apply (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds
    simpa using And.intro hh₀ hh₁
  have hdiff : ∀ x ∈ s, ∀ l : ℝ, HasDerivAt (fun x => A x l) (A' x l) x := by
    intro x hx l
    have hn : x ∉ Γ₀.brk ∧ x ∉ Γ₁.brk := by simpa using hx.2
    have hd := ((hf.differentiableAt (hU.mem_nhds (hmem _ (clamp_mem l) x))).hasDerivAt).scomp x
      (interp_hasDerivAt Γ₀ Γ₁ hn.1 hn.2 (clamp l))
    simpa [A, A', Function.comp_def, smul_eq_mul, mul_comm] using hd
  have hcA' : Continuous (A' h) := by
    apply (hcf'.comp (continuous_const.prodMk continuous_id)).mul
    dsimp [interpVelocity, clamp]
    fun_prop
  have hbound : ∀ l ∈ Icc (0 : ℝ) 1, ∀ x ∈ s,
      ‖A' x l‖ ≤ max B 0 * (‖slantDir κ‖ * (|L₀| + |L₁| + 1)) := by
    intro l hl x hx
    have hn : x ∉ Γ₀.brk ∧ x ∉ Γ₁.brk := by simpa using hx.2
    dsimp [A']
    rw [clamp_eq hl, norm_mul]
    have hbx : ‖deriv f (interpPt Γ₀ Γ₁ l x)‖ ≤ max B 0 := by
      simpa only [clamp_eq hl] using
        (hB (x, l) ⟨ball_subset_closedBall hx.1, hl⟩).trans (le_max_left B 0)
    apply mul_le_mul hbx
      (interpVelocity_bound Γ₀ Γ₁ (hL₀ x hn.1) (hL₁ x hn.2) hl) (norm_nonneg _)
      (le_max_right _ _)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := A) (F' := A') (x₀ := h)
    (bound := fun _ => max B 0 * (‖slantDir κ‖ * (|L₀| + |L₁| + 1))) hs
    (Eventually.of_forall fun x => (hcA.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hcA.comp (continuous_const.prodMk continuous_id)).intervalIntegrable (a := 0) (b := 1))
    hcA'.aestronglyMeasurable
    (Eventually.of_forall fun l hl x hx => hbound l (by simpa using (uIoc_subset_uIcc hl)) x hx)
    intervalIntegrable_const
    (Eventually.of_forall fun l _ x hx => hdiff x hx l)
  let Δ : ℂ := slantDir κ * ((Γ₁.ξ h - Γ₀.ξ h : ℝ) : ℂ)
  let Δ' : ℂ := slantDir κ * ((deriv Γ₁.ξ h - deriv Γ₀.ξ h : ℝ) : ℂ)
  have hΔ : HasDerivAt (fun x => slantDir κ * ((Γ₁.ξ x - Γ₀.ξ x : ℝ) : ℂ)) Δ' h :=
    (((Γ₁.diff h hh₁).hasDerivAt.sub (Γ₀.diff h hh₀).hasDerivAt).ofReal_comp).const_mul _
  have hconn : HasDerivAt (connector Γ₀ Γ₁ f)
      (Δ' * (∫ l in (0 : ℝ)..1, A h l) + Δ * (∫ l in (0 : ℝ)..1, A' h l)) h := by
    have he : (fun x => ∫ l in (0 : ℝ)..1, A x l) =
        fun x => ∫ l in (0 : ℝ)..1, f (interpPt Γ₀ Γ₁ l x) := by
      funext x
      apply intervalIntegral.integral_congr
      intro l hl
      dsimp [A]
      rw [clamp_eq (by simpa using hl)]
    apply (hΔ.mul key.2).congr_of_eventuallyEq
    filter_upwards [] with x
    change connector Γ₀ Γ₁ f x = _
    change (slantDir κ * ((Γ₁.ξ x - Γ₀.ξ x : ℝ) : ℂ)) *
      (∫ l in (0 : ℝ)..1, f (interpPt Γ₀ Γ₁ l x)) =
      (slantDir κ * ((Γ₁.ξ x - Γ₀.ξ x : ℝ) : ℂ)) * (∫ l in (0 : ℝ)..1, A x l)
    rw [congrFun he x]
  have hparam (l : ℝ) (hl : l ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun l => f (interpPt Γ₀ Γ₁ l h) * interpVelocity Γ₀ Γ₁ h l)
        (Δ' * A h l + Δ * A' h l) l := by
    have hz : HasDerivAt (fun l => interpPt Γ₀ Γ₁ l h) Δ l := by
      convert ((((hasDerivAt_id l).const_sub 1).mul_const (Γ₀.ξ h)).add
        ((hasDerivAt_id l).mul_const (Γ₁.ξ h))).ofReal_comp.add_const ((h : ℂ) * I) |>.const_mul (slantDir κ) using 1 <;>
        dsimp [interpPt, Δ] <;> push_cast <;> ring
    have hz' : HasDerivAt (fun l => interpVelocity Γ₀ Γ₁ h l) Δ' l := by
      convert ((((hasDerivAt_id l).const_sub 1).mul_const (deriv Γ₀.ξ h)).add
        ((hasDerivAt_id l).mul_const (deriv Γ₁.ξ h))).ofReal_comp.add_const I |>.const_mul (slantDir κ) using 1 <;>
        dsimp [interpVelocity, Δ'] <;> push_cast <;> ring
    have hd := (((hf.differentiableAt (hU.mem_nhds (hmem l hl h))).hasDerivAt).scomp l hz).mul hz'
    convert hd using 1 <;> first
    | rfl
    | (funext x; rfl)
    | (simp only [A, A', clamp_eq hl, smul_eq_mul, Function.comp_def]; ring)
  have hiA : IntervalIntegrable (A h) volume 0 1 :=
    (hcA.comp ((show Continuous (fun _ : ℝ => h) from continuous_const).prodMk
      continuous_id)).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun l hl => hparam l (by simpa using hl))
    ((hiA.const_mul Δ').add (key.1.const_mul Δ))
  rw [intervalIntegral.integral_add (hiA.const_mul Δ') (key.1.const_mul Δ),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  have he' : Δ' * (∫ l in (0 : ℝ)..1, A h l) + Δ * (∫ l in (0 : ℝ)..1, A' h l) =
      f (Γ₁.pt h) * velocity Γ₁ h - f (Γ₀.pt h) * velocity Γ₀ h := by
    simpa [interpPt, interpVelocity, SlantGraph.pt, velocity] using he
  rw [he'] at hconn
  exact hconn

/-- **Homotopy of graphs.** If `f` is holomorphic on an open set containing every interpolated graph, with a uniform
decay along them, the two integrals agree. -/
theorem graphInt_eq_of_homotopy {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hmem : ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ, interpPt Γ₀ Γ₁ l h ∈ U)
    (hdec : ∃ M : ℝ, ∀ l ∈ Icc (0 : ℝ) 1, ∀ h : ℝ,
      ‖f (interpPt Γ₀ Γ₁ l h)‖ ≤ M * (1 + |h|) ^ (-(3 / 2) : ℝ)) :
    graphInt Γ₀ f = graphInt Γ₁ f := by
  have hmem₀ (h : ℝ) : Γ₀.pt h ∈ U := by
    simpa [interpPt, SlantGraph.pt] using hmem 0 (by constructor <;> norm_num) h
  have hmem₁ (h : ℝ) : Γ₁.pt h ∈ U := by
    simpa [interpPt, SlantGraph.pt] using hmem 1 (by constructor <;> norm_num) h
  have hpt (Γ : SlantGraph κ) : Continuous Γ.pt := by
    exact continuous_const.mul ((Complex.continuous_ofReal.comp Γ.cont).add
      (Complex.continuous_ofReal.mul_const I))
  obtain ⟨M, hM⟩ := hdec
  have hi₀ := graph_integrable Γ₀ (hf.continuousOn.comp_continuous (hpt Γ₀) hmem₀)
    (M := M) (fun h => by simpa [interpPt, SlantGraph.pt] using hM 0 (by constructor <;> norm_num) h)
  have hi₁ := graph_integrable Γ₁ (hf.continuousOn.comp_continuous (hpt Γ₁) hmem₁)
    (M := M) (fun h => by simpa [interpPt, SlantGraph.pt] using hM 1 (by constructor <;> norm_num) h)
  exact infinite_contour_identity Γ₀ Γ₁ (connector_continuous Γ₀ Γ₁ hf.continuousOn hmem)
    (fun h hh₀ hh₁ => connector_hasDerivAt Γ₀ Γ₁ hU hf hmem hh₀ hh₁) hi₀ hi₁ ⟨M, hM⟩

end GoldbachBoundaries.HInf.Fill

