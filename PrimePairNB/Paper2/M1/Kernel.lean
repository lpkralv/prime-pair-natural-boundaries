import PrimePairNB.Paper2.M1.BNumbers

/-!
# The Mellin–Barnes kernel

The paper bounds `K_s(w) = Γ(w)Γ(s-w)/Γ(s)` with Stirling (Z6, exponential decay). Every use here is against
`Q ≪ log`, so polynomial decay of any order suffices, and `norm_Gamma_mul_one_add_abs_im_pow_le` of the RH
development (`TIdentity/Basic.lean`, no Stirling) gives it. The lemmas of this directory therefore do not take (Z6).

Mathlib provides the Beta integral (`Complex.betaIntegral`, `Complex.Gamma_mul_Gamma_eq_betaIntegral`) and Mellin
inversion (`mellin_inversion`, `Mathlib/Analysis/MellinInversion.lean`); `Fw_eq_verticalIntegral'` of the RH
development (`TIdentity/G9d_MellinInversion.lean`) is a worked example of the inversion in this library's
`VerticalIntegral'` form. The lemmas `norm_KerS_mul_pow_le`, `mellin_one_add_cpow_neg`,
`one_add_cpow_neg_eq_verticalIntegral'`, `T_eq_verticalIntegral'_KerS` are proved in
`Fill/<name>.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The symmetry `K_s(s - w) = K_s(w)`. -/
lemma KerS_sub_symm (s w : ℂ) : KerS s (s - w) = KerS s w := by
  simp only [KerS, sub_sub_cancel]
  ring

end GoldbachBoundaries.Paper2.M1
