import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.BCommon
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.norm_negLogDerivZeta_le_strip
import PrimePairNB.Paper2.M1.Fill.norm_sigmaTail_two_le
import PrimePairNB.Paper2.M1.Fill.not_mem_poleSetQ_of_goodHeight

/-! `norm_Qcont_le_growth`. `Qcont = A + ∑_{k ≥ 2} μ(k) A(k ·)`; the strip bound
for `A` on `Re w ≤ 2`, `‖A(w)‖ ≤ vmConst` on `Re w ≥ 2`, the bounded tail, and `log |Im w| ≥ log 2 > 0`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Paper, Lemma 2.2 for `Qcont`** (Z1, Z2, Z3), with the constant chosen after `δ` and before `H`. Proof:
`Qcont_eq_sum_add_tail`, `norm_negLogDerivZeta_le_strip` (strip), `norm_negLogDerivZeta_le` (`Re w ≥ 2`),
`norm_sigmaTail_two_le` (tail), `log |Im w| ≥ log 2 > 0`. Uses: the four lemmas above, `half_le_Binf`. -/
theorem norm_Qcont_le_growth (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ H : ℝ, GoodHeight δ H → ∀ w : ℂ, Binf + 2 * δ ≤ w.re → H ≤ |w.im| →
      w ∉ PoleSetQ ∧ ‖Qcont w‖ ≤ C * Real.log |w.im| := by
  obtain ⟨Cs, hCs⟩ := norm_negLogDerivZeta_le_strip hZ1 hZ2 hZ3 δ hδ
  obtain ⟨Ct, hCt⟩ := norm_sigmaTail_two_le δ hδ
  have hB := half_le_Binf hZ1
  set K := max (vmConst + Ct) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max Cs 0 + K / Real.log 2, fun H hH w hw hwH =>
    ⟨not_mem_poleSetQ_of_goodHeight hZ1 hδ hH hw hwH, ?_⟩⟩
  have hy2 : 2 ≤ |w.im| := hH.1.trans hwH
  have hlog : Real.log 2 ≤ Real.log |w.im| := Real.log_le_log (by norm_num) hy2
  have hlog0 : 0 ≤ Real.log |w.im| := hlog2.le.trans hlog
  have hre0 : 0 < w.re := by linarith
  have hQ : Qcont w = negLogDerivZeta w + sigmaTail 2 w := by
    rw [Qcont_eq_sum_add_tail 2 hre0]
    simp [Finset.sum_range_succ, sigmaTerm, mu]
  have hvm := vmConst_nonneg
  have hA : ‖negLogDerivZeta w‖ ≤ max Cs 0 * Real.log |w.im| + vmConst := by
    rcases le_or_gt w.re 2 with h | h
    · have h1 := (hCs H hH w hw h hwH).2
      have h2 : Cs * Real.log |w.im| ≤ max Cs 0 * Real.log |w.im| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
      linarith
    · have h1 := norm_negLogDerivZeta_le h.le
      have h2 : (2 : ℝ) ^ (-w.re) ≤ 1 / 4 := by
        calc (2 : ℝ) ^ (-w.re) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 1 / 4 := by rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
      have h3 : vmConst * (4 * (2 : ℝ) ^ (-w.re)) ≤ vmConst := by nlinarith
      have h4 : 0 ≤ max Cs 0 * Real.log |w.im| := mul_nonneg (le_max_right _ _) hlog0
      linarith
  have hT := hCt w (by linarith)
  have hKl : K ≤ K / Real.log 2 * Real.log |w.im| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlog hK0
  calc ‖Qcont w‖ = ‖negLogDerivZeta w + sigmaTail 2 w‖ := by rw [hQ]
    _ ≤ ‖negLogDerivZeta w‖ + ‖sigmaTail 2 w‖ := norm_add_le _ _
    _ ≤ max Cs 0 * Real.log |w.im| + K := by linarith [le_max_left (vmConst + Ct) 0]
    _ ≤ max Cs 0 * Real.log |w.im| + K / Real.log 2 * Real.log |w.im| := by linarith
    _ = (max Cs 0 + K / Real.log 2) * Real.log |w.im| := by ring

end GoldbachBoundaries.Paper2.M1
