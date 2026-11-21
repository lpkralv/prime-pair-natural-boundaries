import PrimePairNB.Paper2.M1.Fill.norm_KerS_mul_pow_le

/-!
# Helpers shared by the kernel lemmas

Continuity and integrability of `y ↦ K_s(c + iy)` on a line `0 < c < Re s`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `Γ` is continuous at every point of positive real part. -/
lemma continuousAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : ContinuousAt Gamma z :=
  (differentiableAt_Gamma _ fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).continuousAt

/-- `y ↦ K_s(c + iy)` is continuous for `0 < c < Re s`. -/
lemma continuous_KerS_line {s : ℂ} {c : ℝ} (hc : 0 < c) (hcs : c < s.re) :
    Continuous fun y : ℝ => KerS s (c + y * I) := by
  have h1 : Continuous fun y : ℝ => Gamma (s - (c + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp
      (f := fun y : ℝ => s - ((c : ℂ) + y * I)) (by fun_prop)
  unfold KerS
  exact ((TIdentity.continuous_Gamma_line hc).mul h1).div_const _

/-- The bound `‖K_s(c + iy)‖ ≤ C (1 + |y|)^{-2}` on a line, `0 < c < Re s`. -/
lemma exists_norm_KerS_line_le {s : ℂ} {c : ℝ} (hc : 0 < c) (hcs : c < s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, ‖KerS s (c + y * I)‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := norm_KerS_mul_pow_le (x₁ := c) (x₂ := c) (σ₁ := s.re) (σ₂ := s.re)
    (τ₀ := |s.im|) hc hcs 2
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC s le_rfl le_rfl le_rfl ((c : ℂ) + 0 * I)
    (by simp) (by simp))
  refine ⟨C, hC0, fun y => ?_⟩
  have h := hC s le_rfl le_rfl le_rfl ((c : ℂ) + y * I) (by simp) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at h
  have hpos : 0 < 1 + |y| := by positivity
  have hrpow : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg hpos.le]
    norm_cast
  rw [hrpow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h

/-- `y ↦ K_s(c + iy)` is integrable for `0 < c < Re s`. -/
lemma integrable_KerS_line {s : ℂ} {c : ℝ} (hc : 0 < c) (hcs : c < s.re) :
    Integrable fun y : ℝ => KerS s (c + y * I) := by
  obtain ⟨C, -, hC⟩ := exists_norm_KerS_line_le hc hcs
  exact Integrable.mono'
    ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul C)
    (continuous_KerS_line hc hcs).aestronglyMeasurable (Eventually.of_forall hC)

/-- The norm of a term of `Q` depends only on `Re z`. -/
lemma norm_Q_term_eq_re (p : Nat.Primes) (z : ℂ) :
    ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖ =
      ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(z.re : ℂ))‖ := by
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos p.prop.pos,
    norm_natCast_cpow_of_pos p.prop.pos]
  simp

end GoldbachBoundaries.Paper2.M1
