import PrimePairNB.Paper2.M4b.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Affine change of variable in a vertical integral** (general). For `a > 0` and `b ∈ ℂ`, `z = aw + b` maps the line
`Re w = c` onto `Re z = ac + Re b`; on the lines, `(ac + Re b + iy - b)/a = c + i(y - Im b)/a`. So with
`u = (y - Im b)/a`, `dy = a du`: `∫ a⁻¹ g((ac + Re b + iy - b)/a) dy = ∫ g(c + iu) du`
(`MeasureTheory.integral_comp_mul_left`, `integral_sub_right_eq_self`, `Integrable.comp_mul_left'`,
`Integrable.comp_sub_right`), and both sides of `VerticalIntegral'` carry the same factor `(2πi)⁻¹ · i`. -/
theorem verticalIntegral'_comp_affine (g : ℂ → ℂ) {a : ℝ} (ha : 0 < a) (b : ℂ) (c : ℝ) :
    (Integrable (fun y : ℝ => g (c + y * I)) ↔
      Integrable (fun y : ℝ => ((a : ℂ))⁻¹ * g ((((a * c + b.re : ℝ) : ℂ) + y * I - b) / a))) ∧
    VerticalIntegral' g c = VerticalIntegral' (fun z => ((a : ℂ))⁻¹ * g ((z - b) / a)) (a * c + b.re) := by
  let F : ℝ → ℂ := fun y => g (c + y * I)
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have heq : (fun y : ℝ => ((a : ℂ))⁻¹ *
      g ((((a * c + b.re : ℝ) : ℂ) + y * I - b) / a)) =
      fun y : ℝ => ((a : ℂ))⁻¹ * F ((y - b.im) / a) := by
    funext y
    congr 2
    apply Complex.ext <;> simp [div_re, div_im, normSq]
    field_simp
  rw [heq]
  constructor
  · rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero ha0))]
    constructor
    · intro h
      exact ((integrable_comp_div_iff F ha.ne').mpr h).comp_sub_right b.im
    · intro h
      apply (integrable_comp_div_iff F ha.ne').mp
      simpa only [add_sub_cancel_right] using h.comp_add_right b.im
  · unfold VerticalIntegral' VerticalIntegral
    simp only [smul_eq_mul]
    change _ = _ * (I * ∫ y : ℝ, ((a : ℂ))⁻¹ *
      g ((((a * c + b.re : ℝ) : ℂ) + y * I - b) / a))
    rw [heq, integral_const_mul, integral_sub_right_eq_self (fun y : ℝ => F (y / a)) b.im,
      Measure.integral_comp_div, abs_of_pos ha]
    simp only [Complex.real_smul]
    rw [← mul_assoc ((a : ℂ))⁻¹, inv_mul_cancel₀ ha0, one_mul]

end GoldbachBoundaries.Paper2.M4b
