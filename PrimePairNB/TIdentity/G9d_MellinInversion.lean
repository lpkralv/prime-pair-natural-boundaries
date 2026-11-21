import PrimePairNB.TIdentity.G8b_IntegrableOneLt
import PrimePairNB.TIdentity.G9a_FwBasic
import PrimePairNB.TIdentity.G9b_MellinFw

/-!
# `Fw_eq_verticalIntegral'`

Mellin inversion (`mellinInv_mellin_eq`) for `F`, then the normalization
`mellinInv c g t = (2π)⁻¹ ∫ t^{-(c+iy)} g(c+iy) dy = (2πi)⁻¹ · (i ∫ ...) = VerticalIntegral' ...`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- **Mellin inversion for `F`** (`F(t) = (2πi)⁻¹ ∫_{(c)} Γ(z)Q(z)t^{-z}dz`,
`c > 1`). Unconditional.

Proof sketch. `mellinInv_mellin_eq` (Mathlib, `Mathlib/Analysis/MellinInversion.lean`) with
`σ = c`: `MellinConvergent` from `mellin_Fw`; `VerticalIntegrable (mellin F) c` because
`mellin F = Γ Q = Γ Qcont` on `Re = c` (`mellin_Fw`, and `Qcont = Q` on `Re > 1`) and
`integrable_Gamma_mul_Qcont_of_one_lt`; continuity of `F` at `t` from
`Fw_continuousOn_and_le_exp`. Finally `mellinInv c g t = (2π)⁻¹ ∫ t^{-(c+iy)} g(c+iy) dy` equals
`VerticalIntegral' (kernelQ t) c = (2πi)⁻¹ · i · ∫ ...` (unfold, `Complex.ofReal` bookkeeping). -/
theorem Fw_eq_verticalIntegral' {c t : ℝ} (hc : 1 < c) (ht : 0 < t) :
    (Fw t : ℂ) = VerticalIntegral' (kernelQ t) c := by
  have hmel : ∀ y : ℝ, mellin (fun t => (Fw t : ℂ)) (c + y * I) =
      Gamma (c + y * I) * Qcont (c + y * I) := by
    intro y
    have hre : 1 < ((c : ℂ) + y * I).re := by simpa using hc
    rw [(mellin_Fw hre).2, Qcont_eq_Q_of_one_lt hre]
  have hconv : MellinConvergent (fun t => (Fw t : ℂ)) (c : ℂ) :=
    (mellin_Fw (by simpa using hc)).1
  have hvi : VerticalIntegrable (mellin (fun t => (Fw t : ℂ))) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_Gamma_mul_Qcont_of_one_lt hc
  have hcont : ContinuousAt (fun t => (Fw t : ℂ)) t :=
    continuous_ofReal.continuousAt.comp
      ((Fw_continuousOn_and_le_exp.1).continuousAt (Ioi_mem_nhds ht))
  rw [← mellinInv_mellin_eq c _ ht hconv hvi hcont, mellinInv, VerticalIntegral', VerticalIntegral]
  simp_rw [hmel, kernelQ, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp
  push_cast
  ring_nf
  exact mul_inv_cancel₀ hpi

end TIdentity

end GoldbachBoundaries
