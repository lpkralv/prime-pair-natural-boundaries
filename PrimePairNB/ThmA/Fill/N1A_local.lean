import PrimePairNB.ThmA.G18_LocalAccess
import PrimePairNB.ThmA.Fill.FCommon
import PrimePairNB.ThmA.Fill.PsegA_split
import PrimePairNB.ThmA.Fill.Qcont_pole_split
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn
import PrimePairNB.ThmA.Fill.logEnd

/- The regular-part calculation is adapted from `N1A_access`. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA
open FEndpoint in
/-- **Local form of `N₁` at a catalogue point** (the local model, both cases, the `N₁^♮` part).
Under RH (for the residue at `ρ/n`).

Sketch. `a = α - 1`, `c = Res_a Q = sigmaRes a`, `q` from `Qcont_pole_split`. Choose `R` with
`ball a R ∩ Σ = {a}`, `ball a R ⊆ {Re > 0}`; `u₁ ∈ (0, 1-b)` with `u₁|v| < R/2`; `d₁ > 0` the distance
from `{a + uv : u ∈ [u₁, 1-b]}` to `Σ` (`hseg`, compactness, local finiteness); `r` small. Split
`∫_0^{1-b} = ∫_0^{u₁} + ∫_{u₁}^{1-b}`. The second part and `A(s - w_b)` are holomorphic on
`ball α r` (as in `analyticAt_N1A`). On `[0,u₁]`, `PsegA_split` (with `ε = (s-α)/v`,
`(s - 1 + u'v - a)/v = ε + u'`) gives `PsegA = (hol in s) - c·Log(ε+u) + v∫_u^{1-b} q`; the first and
last terms give holomorphic contributions; the middle one is
`-c v ∫_0^{u₁} φ(ε,u) Log(ε+u) du`, `φ(ε,u) = Γ(1-uv)Γ(a + (ε+u)v)`, and `logEnd` turns it into
`c·v·segInt (φ ε) (-ε) 0 · Log ε + hol`. Finally `v·segInt (φ ε) (-ε) 0 = Γ(s)J_{1a}(s)` (substitute
`τ ↦ 1-τ` in `segInt`; `s - a - 1 = εv`), and `logAt v α s = Log ε`. -/
theorem N1A_local (hRH : RiemannHypothesis) {κ b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) {A : ℂ → ℂ}
    {α : ℂ} (hα1 : 1 < α.re) (ha : α - 1 ∈ PoleSetQ) (hA : AnalyticAt ℂ A (α - wb κ b))
    (hseg : ∀ u ∈ Ioc (0 : ℝ) (1 - b), α - 1 + (u : ℂ) * slantDir κ ∉ PoleSetQ) :
    ∃ r : ℝ, 0 < r ∧ ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball α r) ∧
      ∀ s ∈ ball α r, (s - α) / slantDir κ ∈ slitPlane →
        N1A κ b A s = sigmaRes (α - 1) * Gamma s * J 1 (α - 1) s * logAt (slantDir κ) α s + H s := by
  obtain ⟨hb0, hb1⟩ := hb
  let s₀ := α
  let t₀ : ℝ := 0
  have ht0 : 0 ≤ t₀ := le_rfl
  have ht1 : t₀ < 1 - b := by dsimp [t₀]; linarith
  have h1 : 1 < s₀.re := hα1
  have hseg_access : ∀ u ∈ Icc (0 : ℝ) (1 - b), u ≠ t₀ →
      s₀ - 1 + (u : ℂ) * slantDir κ ∉ PoleSetQ := by
    intro u hu hne
    apply hseg u ⟨lt_of_le_of_ne hu.1 (Ne.symm hne), hu.2⟩
  have hb1' : (0 : ℝ) ≤ 1 - b := by linarith
  set v := slantDir κ with hv
  have hv0 : v ≠ 0 := slantDir_ne_zero κ
  have hvre : v.re = 1 := by simp [hv, slantDir]
  have hvim : v.im = κ := by simp [hv, slantDir]
  have hvn1 : 1 ≤ ‖v‖ := by
    have := Complex.abs_re_le_norm v; rw [hvre] at this; simpa using this
  set K : ℝ := 1 + |κ| with hK
  have hK0 : 0 < K := by positivity
  have hvnK : ‖v‖ ≤ K := by
    have := Complex.norm_le_abs_re_add_abs_im v; rw [hvre, hvim] at this; simpa using this
  have hdivle : ∀ z : ℂ, ‖z / v‖ ≤ ‖z‖ := fun z => by
    rw [norm_div]; exact div_le_self (norm_nonneg _) hvn1
  set a := s₀ - 1 + (t₀ : ℂ) * v with ha_def
  set c := sigmaRes a with hc
  have hdiv : ∀ (s : ℂ) (x : ℝ), (s - 1 + (x : ℂ) * v - a) / v = (s - s₀) / v + ((x - t₀ : ℝ) : ℂ) := by
    intro s x; rw [ha_def]; field_simp; push_cast; ring
  have hre : ∀ (s : ℂ) (x : ℝ), (s - 1 + (x : ℂ) * v).re = s.re - 1 + x := by
    intro s x; simp [hv, slantDir]
  have hre1 : ∀ x : ℝ, (1 - (x : ℂ) * v).re = 1 - x := by
    intro x; simp [hv, slantDir]
  -- constants
  set ε₀ := min b (s₀.re - 1) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min hb0 (by linarith)
  have hε₀b : ε₀ ≤ b := min_le_left _ _
  have hε₀s : ε₀ ≤ s₀.re - 1 := min_le_right _ _
  set η := ε₀ / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  have hηK : η * K = ε₀ / 4 := by rw [hη]; field_simp
  set ρ := min η ((1 - b - t₀) / 2) with hρ
  have hρ0 : 0 < ρ := lt_min hη0 (by linarith)
  have hρη : ρ ≤ η := min_le_left _ _
  have hρb : ρ ≤ (1 - b - t₀) / 2 := min_le_right _ _
  /- The log part: `logEnd` on a thin rectangle. -/
  set U : Set ℂ := {w | -t₀ - η < w.re} ∩ {w | w.re < 1 - b - t₀ + η} ∩ {w | -η < w.im} ∩
    {w | w.im < η} with hU
  have hUo : IsOpen U :=
    (((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)).inter
      (isOpen_lt continuous_const continuous_im)).inter (isOpen_lt continuous_im continuous_const)
  have hUc : Convex ℝ U :=
    (((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
      (convex_halfSpace_im_gt _)).inter (convex_halfSpace_im_lt _)
  have hballU : ball (0 : ℂ) ρ ⊆ U := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    obtain ⟨hr1, hr2⟩ := abs_lt.mp (lt_of_le_of_lt (abs_re_le_norm w) hw)
    obtain ⟨hi1, hi2⟩ := abs_lt.mp (lt_of_le_of_lt (abs_im_le_norm w) hw)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp only [mem_ofPred_eq] <;> linarith
  have hsegU : ∀ u ∈ Icc (-t₀) (1 - b - t₀), (u : ℂ) ∈ U := by
    intro u hu
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp only [mem_ofPred_eq, ofReal_re, ofReal_im] <;>
      linarith [hu.1, hu.2]
  obtain ⟨φt, hφt⟩ : ∃ φt : ℂ → ℂ → ℂ, ∀ δ w,
      φt δ w = Gamma (1 - (w + t₀) * v) * Gamma (s₀ + δ * v - 1 + (w + t₀) * v) :=
    ⟨_, fun _ _ => rfl⟩
  have hφd : DifferentiableOn ℂ (Function.uncurry φt) (ball (0 : ℂ) ρ ×ˢ U) := by
    have huc : Function.uncurry φt = fun p : ℂ × ℂ =>
        Gamma (1 - (p.2 + t₀) * v) * Gamma (s₀ + p.1 * v - 1 + (p.2 + t₀) * v) :=
      funext fun p => hφt p.1 p.2
    rw [huc]
    rintro ⟨δ, w⟩ ⟨hδ, hw⟩
    rw [mem_ball_zero_iff] at hδ
    obtain ⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩ := hw
    simp only [mem_ofPred_eq] at hw1 hw2 hw3 hw4
    have e1 : ((w + t₀) * v).re = w.re + t₀ - w.im * κ := by
      simp only [hv, slantDir, mul_re, mul_im, add_re, add_im, one_re, one_im, ofReal_re, ofReal_im,
        I_re, I_im]
      ring
    have hwk : |w.im * κ| ≤ η * |κ| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (abs_lt.mpr ⟨hw3, hw4⟩).le (abs_nonneg _)
    have hwk' := abs_le.mp hwk
    have hdv : |(δ * v).re| ≤ ε₀ / 4 := by
      refine (abs_re_le_norm _).trans ?_
      rw [norm_mul]
      calc ‖δ‖ * ‖v‖ ≤ ρ * K := mul_le_mul hδ.le hvnK (norm_nonneg _) hρ0.le
        _ ≤ η * K := mul_le_mul_of_nonneg_right hρη hK0.le
        _ = ε₀ / 4 := hηK
    have hdv' := abs_le.mp hdv
    have hηK' : η + η * |κ| = ε₀ / 4 := by rw [← hηK, hK]; ring
    have h1' : 0 < (1 - (w + t₀) * v).re := by
      rw [sub_re, one_re, e1]; linarith
    have h2' : 0 < (s₀ + δ * v - 1 + (w + t₀) * v).re := by
      simp only [add_re, sub_re, one_re] at *
      rw [e1]; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    have d1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => 1 - (p.2 + t₀) * v) (δ, w) := by fun_prop
    have d2 : DifferentiableAt ℂ (fun p : ℂ × ℂ => s₀ + p.1 * v - 1 + (p.2 + t₀) * v) (δ, w) := by
      fun_prop
    exact (n1a_gamma_dcomp d1 h1').mul (n1a_gamma_dcomp d2 h2')
  obtain ⟨Flog, hFlogA, hFlog⟩ := logEnd (φ := φt) hρ0
    (by dsimp [t₀] at hρb; linarith : ρ < 1 - b) hUo hUc hballU
    (fun u hu => hsegU u (by simpa [t₀] using hu)) hφd
  /- The regular part of `Q` and a uniform neighbourhood of the segment. -/
  have ha' : a ∈ PoleSetQ := by simpa [ha_def, s₀, t₀] using ha
  obtain ⟨q, hqA, hqQ⟩ := Qcont_pole_split hRH ha'
  have hWo := n1a_isOpen_W hRH a
  set S₀ : Set ℂ := (fun x : ℝ => s₀ - 1 + (x : ℂ) * v) '' Icc 0 (1 - b) with hS₀
  have hS₀c : IsCompact S₀ := isCompact_Icc.image (by fun_prop)
  have hS₀W : S₀ ⊆ halfPlane 0 \ (PoleSetQ \ {a}) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨show (0 : ℝ) < _ by rw [hre]; linarith [hx.1], fun hP => ?_⟩
    by_cases hxt : x = t₀
    · subst hxt; exact hP.2 rfl
    · exact hseg_access x hx hxt hP.1
  obtain ⟨ε, hε0, hεW⟩ := hS₀c.exists_thickening_subset_open hWo hS₀W
  have hqT : ContinuousOn q (thickening ε S₀) := hqA.continuousOn.mono hεW
  have hqd : ∀ z ∈ thickening ε S₀, DifferentiableAt ℂ q z := fun z hz =>
    (hqA z (hεW hz)).differentiableAt
  have hmemT : ∀ (z : ℂ) (x : ℝ), x ∈ Icc (0 : ℝ) (1 - b) → ‖z - s₀‖ < ε →
      z - 1 + (x : ℂ) * v ∈ thickening ε S₀ := by
    intro z x hx hz
    rw [Metric.mem_thickening_iff]
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    convert hz using 2
    ring
  set β := ε / 4 with hβ
  have hβ0 : 0 < β := by positivity
  have hclampT : ∀ s : ℂ, ‖n1aClamp s₀ β s - s₀‖ < ε := fun s =>
    lt_of_le_of_lt (n1aClamp_norm s₀ hβ0.le s) (by linarith)
  obtain ⟨gq, hgq⟩ : ∃ gq : ℂ → ℝ → ℂ, ∀ s x,
      gq s x = q (n1aClamp s₀ β s - 1 + (n1aClampR 0 (1 - b) x : ℂ) * v) := ⟨_, fun _ _ => rfl⟩
  have hgq_cont : Continuous (Function.uncurry gq) := by
    have huc : Function.uncurry gq =
        q ∘ fun p : ℂ × ℝ => n1aClamp s₀ β p.1 - 1 + (n1aClampR 0 (1 - b) p.2 : ℂ) * v :=
      funext fun p => hgq p.1 p.2
    rw [huc]
    refine hqT.comp_continuous ?_ fun p => hmemT _ _ (n1aClampR_mem hb1' _) (hclampT _)
    exact (((continuous_n1aClamp s₀ β).comp continuous_fst).sub continuous_const).add
      ((continuous_ofReal.comp ((continuous_n1aClampR _ _).comp continuous_snd)).mul continuous_const)
  obtain ⟨Q2, hQ2⟩ : ∃ Q2 : ℂ → ℝ → ℂ, ∀ s u, Q2 s u = ∫ x in u..(1 - b), gq s x :=
    ⟨_, fun _ _ => rfl⟩
  have hQ2_cont : Continuous (Function.uncurry Q2) := by
    have huc : Function.uncurry Q2 = fun p : ℂ × ℝ => -∫ x in (1 - b)..p.2, gq p.1 x := by
      funext p
      show Q2 p.1 p.2 = _
      rw [hQ2]
      exact intervalIntegral.integral_symm _ _
    rw [huc]
    refine Continuous.neg ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun p : ℂ × ℝ => gq p.1) (a₀ := 1 - b)
      (hgq_cont.comp (by fun_prop : Continuous fun p : (ℂ × ℝ) × ℝ => (p.1.1, p.2))) continuous_snd
  /- The radius. -/
  obtain ⟨rA, hrA0, hAan⟩ := hA.exists_ball_analyticOnNhd
  set r := min (min ρ β) (min rA (s₀.re - 1)) with hr
  have hr0 : 0 < r := lt_min (lt_min hρ0 hβ0) (lt_min hrA0 (by linarith))
  have hrρ : r ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hrβ : r ≤ β := (min_le_left _ _).trans (min_le_right _ _)
  have hrA : r ≤ rA := (min_le_right _ _).trans (min_le_left _ _)
  have hrs : r ≤ s₀.re - 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hball_facts : ∀ s ∈ ball s₀ r, ‖s - s₀‖ < r ∧ 1 < s.re ∧ (s - s₀) / v ∈ ball (0 : ℂ) ρ ∧
      s ∈ ball s₀ β ∧ s - wb κ b ∈ ball (s₀ - wb κ b) rA ∧ ‖s - s₀‖ < ε := by
    intro s hs
    have hn : ‖s - s₀‖ < r := by rw [← dist_eq_norm]; exact hs
    have hre' := (abs_lt.mp (lt_of_le_of_lt (n1a_abs_re_le s s₀) hn)).1
    refine ⟨hn, by linarith, ?_, ball_subset_ball hrβ hs, ?_, by linarith⟩
    · rw [mem_ball_zero_iff]; exact lt_of_le_of_lt (hdivle _) (lt_of_lt_of_le hn hrρ)
    · rw [mem_ball, dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm]
      exact ball_subset_ball hrA hs
  have hLslit : ∀ s ∈ ball s₀ r, (s - 1 + ((1 - b : ℝ) : ℂ) * v - a) / v ∈ slitPlane := by
    intro s hs
    obtain ⟨-, -, hδ, -⟩ := hball_facts s hs
    rw [hdiv, mem_ball_zero_iff] at *
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    have := (abs_lt.mp (lt_of_le_of_lt (abs_re_le_norm _) hδ)).1
    simp only [add_re, ofReal_re]
    linarith
  /- The holomorphic part. -/
  have hQ2d : ∀ u : ℝ, DifferentiableOn ℂ (fun s => Q2 s u) (ball s₀ r) := by
    intro u
    have h := differentiableOn_intervalIntegral_of_continuousOn (isOpen_ball (x := s₀) (ε := r))
      (a := u) (b := 1 - b) (f := gq) hgq_cont.continuousOn ?_
    · simpa only [hQ2] using h
    intro x _ s hs
    obtain ⟨-, -, -, hsβ, -, hsε⟩ := hball_facts s hs
    have hev : (fun s => gq s x) =ᶠ[𝓝 s] fun s => q (s - 1 + (n1aClampR 0 (1 - b) x : ℂ) * v) := by
      filter_upwards [isOpen_ball.mem_nhds hsβ] with s' hs'
      rw [hgq, n1aClamp_of_mem_ball hs']
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.congr_of_eventuallyEq ?_ hev)
    have hd : DifferentiableAt ℂ (fun s => s - 1 + (n1aClampR 0 (1 - b) x : ℂ) * v) s := by fun_prop
    exact n1a_dcomp (hqd _ (hmemT s _ (n1aClampR_mem hb1' x) hsε)) hd rfl
  obtain ⟨fo, hfo⟩ : ∃ fo : ℂ → ℝ → ℂ, ∀ s u, fo s u = Gamma (1 - (u : ℂ) * v) *
      Gamma (s - 1 + (u : ℂ) * v) *
        (A (s - wb κ b) + c * Complex.log ((s - 1 + ((1 - b : ℝ) : ℂ) * v - a) / v) + v * Q2 s u) :=
    ⟨_, fun _ _ => rfl⟩
  have hfo_c : ContinuousOn (Function.uncurry fo) (ball s₀ r ×ˢ [[0, 1 - b]]) := by
    have huc : Function.uncurry fo = fun p : ℂ × ℝ => Gamma (1 - (p.2 : ℂ) * v) *
        Gamma (p.1 - 1 + (p.2 : ℂ) * v) * (A (p.1 - wb κ b) +
          c * Complex.log ((p.1 - 1 + ((1 - b : ℝ) : ℂ) * v - a) / v) + v * Q2 p.1 p.2) :=
      funext fun p => hfo p.1 p.2
    rw [huc]
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    rw [uIcc_of_le hb1'] at hu
    obtain ⟨-, hsre, -, -, hsA, -⟩ := hball_facts s hs
    refine ContinuousAt.continuousWithinAt ?_
    have g1 : 0 < (1 - (u : ℂ) * v).re := by rw [hre1]; linarith [hu.2]
    have g2 : 0 < (s - 1 + (u : ℂ) * v).re := by rw [hre]; linarith [hu.1]
    have c1 : ContinuousAt (fun p : ℂ × ℝ => 1 - (p.2 : ℂ) * v) (s, u) := by fun_prop
    have c2 : ContinuousAt (fun p : ℂ × ℝ => p.1 - 1 + (p.2 : ℂ) * v) (s, u) := by fun_prop
    have c3 : ContinuousAt (fun p : ℂ × ℝ => p.1 - wb κ b) (s, u) := by fun_prop
    have c4 : ContinuousAt (fun p : ℂ × ℝ => (p.1 - 1 + ((1 - b : ℝ) : ℂ) * v - a) / v) (s, u) := by
      fun_prop
    have c5 : ContinuousAt (fun p : ℂ × ℝ => Q2 p.1 p.2) (s, u) := hQ2_cont.continuousAt
    exact ((n1a_gamma_cont c1 g1).mul (n1a_gamma_cont c2 g2)).mul
      (((n1a_ccomp (hAan _ hsA).continuousAt c3 rfl).add
        (continuousAt_const.mul (c4.clog (hLslit s hs)))).add (continuousAt_const.mul c5))
  have hfo_d : ∀ u ∈ [[(0 : ℝ), 1 - b]], DifferentiableOn ℂ (fun s => fo s u) (ball s₀ r) := by
    intro u hu s hs
    rw [uIcc_of_le hb1'] at hu
    obtain ⟨-, hsre, -, -, hsA, -⟩ := hball_facts s hs
    have g2 : 0 < (s - 1 + (u : ℂ) * v).re := by rw [hre]; linarith [hu.1]
    have dQ : DifferentiableAt ℂ (fun s => Q2 s u) s :=
      (hQ2d u).differentiableAt (isOpen_ball.mem_nhds hs)
    have d2 : DifferentiableAt ℂ (fun s : ℂ => s - 1 + (u : ℂ) * v) s := by fun_prop
    have d3 : DifferentiableAt ℂ (fun s : ℂ => s - wb κ b) s := by fun_prop
    have d4 : DifferentiableAt ℂ (fun s : ℂ => (s - 1 + ((1 - b : ℝ) : ℂ) * v - a) / v) s := by
      fun_prop
    have hfu : (fun s => fo s u) = fun s => Gamma (1 - (u : ℂ) * v) * Gamma (s - 1 + (u : ℂ) * v) *
        (A (s - wb κ b) + c * Complex.log ((s - 1 + ((1 - b : ℝ) : ℂ) * v - a) / v) + v * Q2 s u) :=
      funext fun s => hfo s u
    rw [hfu]
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_const _).mul (n1a_gamma_dcomp d2 g2)).mul
      (((n1a_dcomp (hAan _ hsA).differentiableAt d3 rfl).add
        ((differentiableAt_const c).mul (d4.clog (hLslit s hs)))).add
        ((differentiableAt_const v).mul dQ))
  have hHd : DifferentiableOn ℂ (fun s => ∫ u in (0 : ℝ)..(1 - b), fo s u) (ball s₀ r) :=
    differentiableOn_intervalIntegral_of_continuousOn isOpen_ball hfo_c hfo_d
  /- The function. -/
  refine ⟨r, hr0, fun s => v * (∫ u in (0 : ℝ)..(1 - b), fo s u) - c * v * Flog ((s - s₀) / v), ?_, ?_⟩
  · refine DifferentiableOn.analyticOnNhd ?_ isOpen_ball
    intro s hs
    obtain ⟨-, -, hδ, -⟩ := hball_facts s hs
    have hdF : DifferentiableAt ℂ (fun s => Flog ((s - s₀) / v)) s :=
      n1a_dcomp (hFlogA _ hδ).differentiableAt (by fun_prop) rfl
    exact (((hHd s hs).const_mul v).sub (hdF.const_mul (c * v)).differentiableWithinAt)
  · intro s hs hδslit
    obtain ⟨hsn, hsre, hδ, hsβ, hsA, hsε⟩ := hball_facts s hs
    set δ := (s - s₀) / v with hδdef
    have hsδ : s₀ + δ * v = s := by rw [hδdef, div_mul_cancel₀ _ hv0]; ring
    -- `PsegA` on the upper side
    have hP : ∀ u ∈ Icc (0 : ℝ) (1 - b), PsegA κ b A s u = A (s - wb κ b) +
        c * (Complex.log ((s - 1 + ((1 - b : ℝ) : ℂ) * v - a) / v) -
          Complex.log (δ + ((u - t₀ : ℝ) : ℂ))) + v * Q2 s u := by
      intro u hu
      have hz : ∀ x ∈ Icc u (1 - b), x ∈ Icc (0 : ℝ) (1 - b) := fun x hx => ⟨hu.1.trans hx.1, hx.2⟩
      have hsplit := PsegA_split (κ := κ) (b := b) (A := A) (q := q) (c := c) (a := a) (s := s)
        (u := u) hu.2 hqQ ?_ ?_ ?_
      · rw [hsplit, hdiv s u]
        have hI : ∫ x in u..(1 - b), q (s - 1 + (x : ℂ) * v) = Q2 s u := by
          rw [hQ2]
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hu.2] at hx
          simp only [hgq, n1aClamp_of_mem_ball hsβ, n1aClampR_of_mem (hz x hx)]
        rw [hI]
      · intro x hx
        refine ⟨show (0 : ℝ) < _ by rw [hre]; linarith [hx.1, hu.1], fun hPQ => ?_⟩
        have hT := hεW (hmemT s x (hz x hx) hsε)
        have hne : s - 1 + (x : ℂ) * v ≠ a := by
          intro he
          have hsl : (s - 1 + (x : ℂ) * v - a) / v ∈ slitPlane := by
            rw [hdiv]
            exact slit_add_nonneg hδslit (by dsimp [t₀]; linarith [hx.1, hu.1])
          apply slitPlane_ne_zero hsl
          rw [he, sub_self, zero_div]
        exact hT.2 ⟨hPQ, hne⟩
      · exact hqT.mono (by rintro _ ⟨x, hx, rfl⟩; exact hmemT s x (hz x hx) hsε)
      · intro x hx
        rw [hdiv]
        exact slit_add_nonneg hδslit (by dsimp [t₀]; linarith [hx.1, hu.1])
    -- rewrite `N₁`
    have hN : N1A κ b A s = v * ∫ u in (0 : ℝ)..(1 - b), (fo s u - c * (Gamma (1 - (u : ℂ) * v) *
        Gamma (s - 1 + (u : ℂ) * v) * Complex.log (δ + ((u - t₀ : ℝ) : ℂ)))) := by
      simp only [N1A]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hb1'] at hu
      simp only []
      rw [hP u hu, hfo]
      ring
    have hint1 : IntervalIntegrable (fun u => fo s u) volume 0 (1 - b) := by
      refine ContinuousOn.intervalIntegrable ?_
      exact hfo_c.comp (by fun_prop : Continuous fun u : ℝ => (s, u)).continuousOn
        fun u hu => ⟨hs, hu⟩
    have hint2 : IntervalIntegrable (fun u : ℝ => c * (Gamma (1 - (u : ℂ) * v) *
        Gamma (s - 1 + (u : ℂ) * v) * Complex.log (δ + ((u - t₀ : ℝ) : ℂ)))) volume 0 (1 - b) := by
      refine ContinuousOn.intervalIntegrable fun u hu => ContinuousAt.continuousWithinAt ?_
      rw [uIcc_of_le hb1'] at hu
      have g1 : 0 < (1 - (u : ℂ) * v).re := by rw [hre1]; linarith [hu.2]
      have g2 : 0 < (s - 1 + (u : ℂ) * v).re := by rw [hre]; linarith [hu.1]
      have hsl : δ + ((u - t₀ : ℝ) : ℂ) ∈ slitPlane :=
        slit_add_nonneg hδslit (by simpa [t₀] using hu.1)
      have c1 : ContinuousAt (fun u : ℝ => 1 - (u : ℂ) * v) u := by fun_prop
      have c2 : ContinuousAt (fun u : ℝ => s - 1 + (u : ℂ) * v) u := by fun_prop
      have c3 : ContinuousAt (fun u : ℝ => δ + ((u - t₀ : ℝ) : ℂ)) u := by fun_prop
      exact continuousAt_const.mul (((n1a_gamma_cont c1 g1).mul
        (n1a_gamma_cont c2 g2)).mul (c3.clog hsl))
    have hshift : ∫ u in (0 : ℝ)..(1 - b), Gamma (1 - (u : ℂ) * v) * Gamma (s - 1 + (u : ℂ) * v) *
        Complex.log (δ + ((u - t₀ : ℝ) : ℂ)) =
        ∫ x in (-t₀)..(1 - b - t₀), φt δ (x : ℂ) * Complex.log (δ + (x : ℂ)) := by
      have h := intervalIntegral.integral_comp_sub_right
        (fun x : ℝ => φt δ (x : ℂ) * Complex.log (δ + (x : ℂ))) t₀ (a := 0) (b := 1 - b)
      simp only [zero_sub] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro u _
      have e1 : (((u - t₀ : ℝ) : ℂ) + t₀) = (u : ℂ) := by push_cast; ring
      simp only [hφt, e1, hsδ]
    have hlogeq := hFlog δ hδ hδslit
    have hcoef : v * segInt (φt δ) (-δ) 0 = Gamma s * J 1 (α - 1) s := by
      have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
      have hJ : Gamma s * J 1 (α - 1) s = (s - α) *
          ∫ τ in (0 : ℝ)..1, Gamma (1 + (τ : ℂ) * (s - α)) *
            Gamma (s - (1 + (τ : ℂ) * (s - α))) := by
        unfold J segInt Kern
        rw [intervalIntegral.integral_div]
        have he : s - (α - 1) - 1 = s - α := by ring
        rw [he]
        field_simp
      rw [hJ]
      unfold segInt
      have hfactor : v * (0 - -δ) = s - α := by
        dsimp [δ, s₀]
        field_simp
        ring
      rw [← mul_assoc, hfactor]
      congr 1
      have hreflect := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
        (fun τ : ℝ => φt δ (-δ + (τ : ℂ) * (0 - -δ))) 1
      norm_num only [sub_self, sub_zero] at hreflect
      rw [← hreflect]
      apply intervalIntegral.integral_congr
      intro τ _
      simp only [hφt, t₀, ofReal_zero, add_zero]
      congr 2
      · push_cast
        rw [show s - α = δ * v by rw [← hsδ]; dsimp [s₀]; ring]
        ring
      · push_cast
        rw [show s - α = δ * v by rw [← hsδ]; dsimp [s₀]; ring]
        rw [hsδ]
        ring
    rw [hN, intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_const_mul, hshift]
    simp only [t₀, neg_zero, sub_zero] at hlogeq ⊢
    rw [hlogeq]
    have hcα : c = sigmaRes (α - 1) := by simp [hc, ha_def, s₀, t₀]
    have hlogAt : logAt (slantDir κ) α s = Complex.log δ := rfl
    rw [hlogAt, ← hcα]
    linear_combination c * hcoef * Complex.log δ

end GoldbachBoundaries.ThmA
