import PrimePairNB.Paper2.M1.Fill.KernelCommon
import PrimePairNB.Paper2.M1.Fill.mellin_one_add_cpow_neg

/-!
# `one_add_cpow_neg_eq_verticalIntegral'`

Mathlib's `mellinInv_mellin_eq` for `f(t) = (1+t)^{-s}`, whose Mellin transform on `0 < Re w < Re s` is
`K_s(w)` (`mellin_one_add_cpow_neg`); vertical integrability from `integrable_KerS_line`. The
normalization `mellinInv = VerticalIntegral'` follows the RH development's `Fw_eq_verticalIntegral'`
(`TIdentity/G9d_MellinInversion.lean`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Mellin inversion for `(1+t)^{-s}`**: for `t > 0` and `0 < c < Re s`,
`(1+t)^{-s} = (1/2πi) ∫_{(c)} K_s(w) t^{-w} dw`, the integral absolutely convergent (Mathlib's `mellin_inversion`,
with `mellin_one_add_cpow_neg` and `norm_KerS_mul_pow_le` for the vertical integrability). Uses:
`mellin_one_add_cpow_neg`, `norm_KerS_mul_pow_le`. -/
theorem one_add_cpow_neg_eq_verticalIntegral' {s : ℂ} {c t : ℝ} (hc : 0 < c)
    (hcs : c < s.re) (ht : 0 < t) :
    Integrable (fun y : ℝ => KerS s (c + y * I) * (t : ℂ) ^ (-(c + y * I))) ∧
      ((1 + t : ℝ) : ℂ) ^ (-s) = VerticalIntegral' (fun w => KerS s w * (t : ℂ) ^ (-w)) c := by
  have hK := integrable_KerS_line hc hcs
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (hK.norm.mul_const (t ^ (-c)))
      ((continuous_KerS_line hc hcs).mul (by
        exact Continuous.const_cpow (by fun_prop) (Or.inl htc))).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
    simp
  set f : ℝ → ℂ := fun u => ((1 + u : ℝ) : ℂ) ^ (-s) with hf
  have hmel : ∀ y : ℝ, mellin f (c + y * I) = KerS s (c + y * I) := by
    intro y
    have h := (mellin_one_add_cpow_neg (s := s) (w := c + y * I) (by simpa using hc)
      (by simpa using hcs)).2
    rw [← h, mellin]
    simp only [hf, smul_eq_mul]
  have hconv : MellinConvergent f (c : ℂ) := by
    have h := (mellin_one_add_cpow_neg (s := s) (w := (c : ℂ)) (by simpa using hc)
      (by simpa using hcs)).1
    unfold MellinConvergent
    simpa only [hf, smul_eq_mul] using h
  have hvi : VerticalIntegrable (mellin f) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact hK
  have hcont : ContinuousAt f t := by
    have h1 : (1 + t) ≠ 0 := by positivity
    exact (continuousAt_ofReal_cpow_const (1 + t) (-s) (Or.inr h1)).comp
      (f := fun u : ℝ => 1 + u) (by fun_prop)
  have hinv := mellinInv_mellin_eq c f ht hconv hvi hcont
  change f t = _
  rw [← hinv, mellinInv, VerticalIntegral', VerticalIntegral]
  simp_rw [hmel, smul_eq_mul, Complex.real_smul]
  have hcomm : (fun y : ℝ => (t : ℂ) ^ (-((c : ℂ) + y * I)) * KerS s (c + y * I)) =
      fun y : ℝ => KerS s (c + y * I) * (t : ℂ) ^ (-((c : ℂ) + y * I)) := by
    funext y; ring
  rw [hcomm, ← mul_assoc]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp
  push_cast
  ring_nf
  exact mul_inv_cancel₀ hpi

end GoldbachBoundaries.Paper2.M1
