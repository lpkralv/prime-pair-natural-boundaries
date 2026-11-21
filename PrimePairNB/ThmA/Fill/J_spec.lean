import PrimePairNB.ThmA.G15_Kernel
import PrimePairNB.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn

set_option maxHeartbeats 1000000

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

/-- **the kernel lemma (1), (3).** For `Re a, Re b > 0`, `J_{ab}` is holomorphic on
`σ > max(Re a, Re b)`, and `J'_{ab}(a+b) = K_{a+b}(a)`.

Sketch. On `σ > max(Re a, Re b)` the segment `[a, s-b]` lies in the strip `0 < Re w < σ` (endpoints
have real parts `Re a ∈ (0,σ)` and `σ - Re b ∈ (0,σ)`), where `(s,w) ↦ K_s(w)` is holomorphic
(`Γ` has no poles in `Re > 0`, `Γ(s) ≠ 0`). `J(s) = (s-a-b)∫_0^1 K_s(a + τ(s-a-b)) dτ`; holomorphy by
`differentiableOn_intervalIntegral_of_continuousOn`; at `s = a + b` the product rule gives `1 · K_{a+b}(a) + 0`. -/
theorem J_spec {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (J a b) {s | max a.re b.re < s.re} ∧
      HasDerivAt (J a b) (Kern (a + b) a) (a + b) := by
  let U : Set ℂ := {s | max a.re b.re < s.re}
  let w : ℂ → ℝ → ℂ := fun s t => a + (t : ℂ) * (s - b - a)
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hγ : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ Gamma z := by
    intro z hz
    apply differentiableAt_Gamma
    intro n he
    have := congrArg Complex.re he
    simp only [neg_re, natCast_re] at this
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hpos : ∀ s ∈ U, ∀ t ∈ [[(0 : ℝ), 1]],
      0 < (w s t).re ∧ 0 < (s - w s t).re ∧ 0 < s.re := by
    intro s hs t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hsa : a.re < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsb : b.re < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    dsimp [w]
    simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    constructor
    · have := mul_nonneg ht.1 (sub_pos.mpr hsb).le
      have := mul_nonneg (sub_nonneg.mpr ht.2) ha.le
      nlinarith
    constructor
    · have := mul_nonneg ht.1 hb.le
      have := mul_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr hsa).le
      nlinarith
    · linarith
  have hc : ContinuousOn (Function.uncurry (fun s t => Kern s (w s t)))
      (U ×ˢ [[(0 : ℝ), 1]]) := by
    rintro ⟨s,t⟩ ⟨hs,ht⟩
    obtain ⟨hw, hsw, hsp⟩ := hpos s hs t ht
    change ContinuousWithinAt (fun p : ℂ × ℝ => Gamma (w p.1 p.2) *
      Gamma (p.1 - w p.1 p.2) / Gamma p.1) (U ×ˢ [[(0 : ℝ), 1]]) (s, t)
    apply ContinuousAt.continuousWithinAt
    have hc1 : ContinuousAt (fun p : ℂ × ℝ => Gamma (w p.1 p.2)) (s,t) :=
      (hγ _ hw).continuousAt.comp (f := fun p : ℂ × ℝ => w p.1 p.2) (by dsimp [w]; fun_prop)
    have hc2 : ContinuousAt (fun p : ℂ × ℝ => Gamma (p.1 - w p.1 p.2)) (s,t) :=
      (hγ _ hsw).continuousAt.comp (f := fun p : ℂ × ℝ => p.1 - w p.1 p.2) (by dsimp [w]; fun_prop)
    have hc3 : ContinuousAt (fun p : ℂ × ℝ => Gamma p.1) (s,t) :=
      (hγ _ hsp).continuousAt.comp continuous_fst.continuousAt
    exact (hc1.mul hc2).div hc3 (Gamma_ne_zero_of_re_pos hsp)
  have hd : DifferentiableOn ℂ (fun s => ∫ t in (0 : ℝ)..1, Kern s (w s t)) U := by
    apply differentiableOn_intervalIntegral_of_continuousOn hU hc
    intro t ht s hs
    obtain ⟨hw, hsw, hsp⟩ := hpos s hs t ht
    change DifferentiableWithinAt ℂ (fun s => Gamma (w s t) * Gamma (s - w s t) / Gamma s) U s
    apply DifferentiableAt.differentiableWithinAt
    exact (((hγ _ hw).comp s (by dsimp [w]; fun_prop)).mul
      ((hγ _ hsw).comp s (by dsimp [w]; fun_prop))).div
      (hγ _ hsp) (Gamma_ne_zero_of_re_pos hsp)
  have he : J a b = fun s => (s - b - a) * ∫ t in (0 : ℝ)..1, Kern s (w s t) := rfl
  constructor
  · rw [he]
    exact (by fun_prop : DifferentiableOn ℂ (fun s : ℂ => s - b - a) U).mul hd
  · have hab : a + b ∈ U := by
      change max a.re b.re < (a + b).re
      simp only [add_re]
      exact max_lt (by linarith) (by linarith)
    have h := (((hasDerivAt_id (a + b)).sub_const b).sub_const a).mul
      (hd.differentiableAt (hU.mem_nhds hab)).hasDerivAt
    rw [he]
    convert h using 1 <;> simp [w, Pi.mul_def]

/-! ### Lemmas that use `J_spec` -/

section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

theorem X_differentiableOn {α : ℂ} (hα : α ∈ catalogue) : DifferentiableOn ℂ (X α) HH := by
  by_cases h2 : α = 2
  · have hd := (J_spec (a := 1) (b := 1) (by norm_num) (by norm_num)).1
    have hX : X α = J 1 1 := by funext s; simp [X, h2]
    rw [hX]
    refine hd.mono fun s hs => ?_
    have hs' : (1 : ℝ) < s.re := hs
    simpa using hs'
  · have ha := sub_one_mem_poleSetQ_of_mem_catalogue hα
    have ha0 := re_pos_of_mem_poleSetQ ha
    have ha1 : (α - 1).re ≤ 1 := by
      have := re_le_two_of_mem_catalogue hα
      simp only [sub_re, one_re]; linarith
    have hd := (J_spec (a := 1) (b := α - 1) (by norm_num) ha0).1
    have hX : X α = fun s => 2 * sigmaRes (α - 1) * J 1 (α - 1) s := by funext s; simp [X, h2]
    rw [hX]
    refine (hd.mono fun s hs => ?_).const_mul _
    have hs' : (1 : ℝ) < s.re := hs
    show max (1 : ℂ).re (α - 1).re < s.re
    simp only [one_re]
    exact max_lt hs' (by linarith)

theorem Mon_analyticOn {α : ℂ} (hα : α ∈ catalogue) : AnalyticOnNhd ℂ (Mon α) HH := by
  have h := (X_differentiableOn hα).analyticOnNhd (isOpen_halfPlane 1)
  intro z hz
  exact analyticAt_const.mul (h z hz)

theorem MSpan_analyticOn {m : ℂ → ℂ} (hm : m ∈ MSpan) : AnalyticOnNhd ℂ m HH := by
  induction hm using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    exact Mon_analyticOn hα
  | zero => exact fun z _ => analyticAt_const
  | add x y _ _ hx hy => exact fun z hz => (hx z hz).add (hy z hz)
  | neg x _ hx => exact fun z hz => (hx z hz).neg

end

end GoldbachBoundaries.ThmA
