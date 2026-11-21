import PrimePairNB.HInf.Defs

/-!
# `Jv_analyticOn`, `hasDerivAt_Jv`

The segment from `a` to `v - b` stays in `0 < Re z < Re v` for every `v ∈ 𝒱`, because `0 < Re a ≤ 1 < Re v` and
`0 < Re b ≤ 1 < Re v`. `ThmA.differentiableOn_intervalIntegral_of_continuousOn` then gives the integral.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `𝒱` is open. -/
lemma isOpen_Vt (top : EReal) : IsOpen (Vt top) := by
  have h1 : IsOpen {v : ℂ | 1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {v : ℂ | (v.re : EReal) < top} :=
    isOpen_lt (continuous_coe_real_ereal.comp Complex.continuous_re) continuous_const
  exact h1.inter h2

/-- The domain of (K1) is open. -/
lemma isOpen_domK (top : EReal) : IsOpen (domK top) := by
  have h1 : IsOpen {p : ℂ × ℂ | p.2 ∈ Vt top} := (isOpen_Vt top).preimage continuous_snd
  have h2 : IsOpen {p : ℂ × ℂ | 0 < p.1.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have h3 : IsOpen {p : ℂ × ℂ | p.1.re < p.2.re} :=
    isOpen_lt (Complex.continuous_re.comp continuous_fst) (Complex.continuous_re.comp continuous_snd)
  exact h1.inter (h2.inter h3)

private lemma conv_pos {A B t : ℝ} (hA : 0 < A) (hB : 0 < B) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 < (1 - t) * A + t * B := by
  rcases h0.eq_or_lt with rfl | ht
  · simpa using hA
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hA.le) (mul_pos ht hB)

/-- The segment from `a` to `v - b` lies in the strip of `v`. -/
lemma param_mem_domK {top : EReal} {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) {v : ℂ} (hv : v ∈ Vt top)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (a + (t : ℂ) * (v - a - b), v) ∈ domK top := by
  obtain ⟨ha0, ha1, -⟩ := M1.poleSetQ_re_bounds ha
  obtain ⟨hb0, hb1, -⟩ := M1.poleSetQ_re_bounds hb
  have hv1 := hv.1
  have hre : (a + (t : ℂ) * (v - a - b)).re = a.re + t * (v.re - a.re - b.re) := by
    simp
  refine ⟨hv, ?_, ?_⟩
  · have := conv_pos ha0 (show 0 < v.re - b.re by linarith) ht.1 ht.2
    simp only [hre]
    nlinarith
  · have := conv_pos (show 0 < v.re - a.re by linarith) hb0 ht.1 ht.2
    simp only [hre]
    nlinarith

/-- The integral in `J_{ab}` is holomorphic on `𝒱`. -/
lemma differentiableOn_integral {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D) {a b : ℂ}
    (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) :
    DifferentiableOn ℂ (fun v => ∫ t in (0 : ℝ)..1, k (a + (t : ℂ) * (v - a - b)) v) (Vt top) := by
  have hmem : ∀ v ∈ Vt top, ∀ t ∈ [[(0 : ℝ), 1]], (a + (t : ℂ) * (v - a - b), v) ∈ domK top := by
    intro v hv t ht
    exact param_mem_domK ha hb hv (by simpa using ht)
  apply GoldbachBoundaries.ThmA.differentiableOn_intervalIntegral_of_continuousOn (isOpen_Vt top)
  · rintro ⟨v, t⟩ ⟨hv, ht⟩
    exact ((hK.holo.differentiableAt ((isOpen_domK top).mem_nhds (hmem v hv t ht))).continuousAt.comp
      (f := fun p : ℂ × ℝ => (a + (p.2 : ℂ) * (p.1 - a - b), p.1))
      (show ContinuousAt (fun p : ℂ × ℝ => (a + (p.2 : ℂ) * (p.1 - a - b), p.1)) (v, t) by
        fun_prop)).continuousWithinAt
  · intro t ht v hv
    exact ((hK.holo.differentiableAt ((isOpen_domK top).mem_nhds (hmem v hv t ht))).comp v
      (f := fun x : ℂ => (a + (t : ℂ) * (x - a - b), x))
      (show DifferentiableAt ℂ (fun x : ℂ => (a + (t : ℂ) * (x - a - b), x)) v by
        fun_prop)).differentiableWithinAt

/-- **`J_{ab}` is single-valued holomorphic on all of `𝒱`**, unconditionally: real parts on the segment lie between
`Re a ≤ 1 < Re v` and `Re v - Re b ∈ [Re v - 1, Re v)`, so inside `(0, Re v)`.  -/
theorem Jv_analyticOn {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D) {a b : ℂ}
    (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) : AnalyticOnNhd ℂ (Jv k a b) (Vt top) := by
  have h : DifferentiableOn ℂ (Jv k a b) (Vt top) :=
    (by fun_prop : DifferentiableOn ℂ (fun v : ℂ => v - a - b) (Vt top)).mul
      (differentiableOn_integral hK ha hb)
  exact h.analyticOnNhd (isOpen_Vt top)

/-- `∂_v J_{ab}(a + b) = 𝒦(a, a + b)`.  -/
theorem hasDerivAt_Jv {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ} (hK : IsPinchKernel k top D) {a b : ℂ}
    (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) (hab : a + b ∈ Vt top) :
    HasDerivAt (Jv k a b) (k a (a + b)) (a + b) := by
  have hI := (differentiableOn_integral hK ha hb).differentiableAt ((isOpen_Vt top).mem_nhds hab)
  have h1 : HasDerivAt (fun v : ℂ => v - a - b) 1 (a + b) := ((hasDerivAt_id _).sub_const a).sub_const b
  have h2 := h1.mul hI.hasDerivAt
  have hv : k a (a + b) = 1 * (∫ t in (0 : ℝ)..1, k (a + (t : ℂ) * (a + b - a - b)) (a + b)) +
      (a + b - a - b) * deriv (fun v => ∫ t in (0 : ℝ)..1, k (a + (t : ℂ) * (v - a - b)) v) (a + b) := by
    simp
  rw [hv]
  exact h2

end GoldbachBoundaries.HInf.Fill

