import PrimePairNB.Paper2.M4b.Defs
import PrimePairNB.Paper2.M4b.Fill.verticalIntegral'_comp_affine
import PrimePairNB.Paper2.M1.Fill.KernelCommon
import PrimePairNB.Paper2.M1.Fill.one_add_cpow_neg_eq_verticalIntegral'

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Mellin inversion for `t^μ (1 + t^a)^{-ν}`** (general). Put `c_w = (c + Re μ)/a ∈ (0, Re ν)`. `one_add_cpow_neg_eq_verticalIntegral'` at `u = t^a > 0` gives `(1 + u)^{-ν} = (1/2πi)∫_{(c_w)} K_ν(w) u^{-w} dw` with the
integrand integrable. Multiply by `t^μ`: for `t > 0`, `t^μ (t^a)^{-w} = t^{μ - aw}` (`Complex.ofReal_pow`,
`Complex.cpow_natCast`, `Complex.cpow_mul` with `arg t = 0`). Then `verticalIntegral'_comp_affine` with scale `a` and
shift `-μ` moves the line to `a c_w - Re μ = c`, and `w = (z + μ)/a` turns `K_ν(w) t^{μ - aw}` into
`a · kMB a μ ν z · t^{-z}`. Integrability of `kMB` on the line: `integrable_KerS_line` (`0 < c_w < Re ν`) through
the same change of variable. -/
theorem mellinInv_kMB {a : ℕ} (ha : 0 < a) (μ ν : ℂ) {c : ℝ} (h1 : 0 < (c + μ.re) / a)
    (h2 : (c + μ.re) / a < ν.re) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => kMB a μ ν (c + y * I)) ∧
      (t : ℂ) ^ μ * (((1 + t ^ a : ℝ)) : ℂ) ^ (-ν) =
        VerticalIntegral' (fun z => kMB a μ ν z * (t : ℂ) ^ (-z)) c := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let d : ℝ := (c + μ.re) / a
  have hline : (a : ℝ) * d + (-μ).re = c := by
    dsimp [d]
    field_simp [haR.ne']
    ring
  have hK := integrable_KerS_line (s := ν) h1 h2
  have hchange := verticalIntegral'_comp_affine (KerS ν) haR (-μ) d
  have hInt : Integrable (fun y : ℝ => kMB a μ ν (c + y * I)) := by
    have h := hchange.1.mp hK
    rw [hline] at h
    simpa only [kMB, sub_neg_eq_add, ofReal_natCast] using h
  refine ⟨hInt, ?_⟩
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hpow : ∀ w : ℂ, (t : ℂ) ^ μ * (((t ^ a : ℝ) : ℂ) ^ (-w)) =
      (t : ℂ) ^ (μ - (a : ℂ) * w) := by
    intro w
    have hmul : (t : ℂ) ^ ((a : ℂ) * (-w)) = ((t : ℂ) ^ (a : ℂ)) ^ (-w) := by
      apply cpow_mul
      · simp only [log_im, arg_ofReal_of_nonneg ht.le, mul_im, natCast_re,
          natCast_im, mul_zero, zero_mul, add_zero]
        linarith [Real.pi_pos]
      · simp only [log_im, arg_ofReal_of_nonneg ht.le, mul_im, natCast_re,
          natCast_im, mul_zero, zero_mul, add_zero]
        exact Real.pi_pos.le
    rw [ofReal_pow, ← cpow_natCast, ← hmul, ← cpow_add _ _ htC]
    congr 1
    ring
  let g : ℂ → ℂ := fun w => (t : ℂ) ^ μ * (KerS ν w * ((t ^ a : ℝ) : ℂ) ^ (-w))
  have hfun : (fun z : ℂ => ((a : ℝ) : ℂ)⁻¹ * g ((z - -μ) / (a : ℝ))) =
      fun z => kMB a μ ν z * (t : ℂ) ^ (-z) := by
    funext z
    dsimp [g, kMB]
    simp only [sub_neg_eq_add]
    rw [mul_left_comm ((t : ℂ) ^ μ), hpow]
    have he : μ - (a : ℂ) * ((z + μ) / (a : ℂ)) = -z := by
      field_simp
      ring
    rw [he]
    ring
  have hchangeg := (verticalIntegral'_comp_affine g haR (-μ) d).2
  rw [hline, hfun] at hchangeg
  rw [← hchangeg]
  have hm := (one_add_cpow_neg_eq_verticalIntegral' (s := ν) h1 h2 (pow_pos ht a)).2
  rw [hm]
  unfold VerticalIntegral' VerticalIntegral
  simp only [g, smul_eq_mul]
  rw [integral_const_mul]
  ring

end GoldbachBoundaries.Paper2.M4b
