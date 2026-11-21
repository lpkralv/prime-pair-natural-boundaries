import PrimePairNB.Paper2.M2.Defs
import PrimePairNB.Paper2.M2.Fill.ncard_zeros_im_Icc_le
import PrimePairNB.Paper2.M2.Fill.norm_Rcoef_le_log
import PrimePairNB.Paper2.M2.Fill.poleSetQ_window_count
import PrimePairNB.Paper2.M2.Fill.zetaMult_le_log

/-!
# Sizes and counts of the residues of `Q` (Paper, Lemma 2.1)

(Z1), (Z2). The zeros in a unit window `|γ - t| ≤ 1` have total multiplicity `≪ log(|t| + 3)`: this is
`sum_zetaMult_window_le` (in `M1/Fill/sum_zetaMult_window_le.lean`, with the helpers `wsumB`,
`finite_zeros_im_pos_le`, `wsumB_pos_window_le`). Everything here is read off from it:

* `m(ρ) ≤ C log(|γ| + 3)` (a zero lies in its own window);
* a strip `t ≤ γ ≤ t + L` (`L ≥ 1` an integer) is covered by `L` windows of radius `1`, so it holds at most
  `C L log(|t| + L + 3)` distinct zeros (each has `m ≥ 1`, `one_le_zetaMult`);
* `|R_a| ≪_ε log(|Im a| + 3)` on `Re a ≥ ε`: for real `a` (`a = 1` or `1/k`) `|R_a| ≤ 1`; for non-real `a`,
  `Rcoef_eq_finsum` leaves at most `1/ε` terms `μ(k)/k · m(ka)`;
* the points of `Σ_Q` with `Re a ≥ ε` and `t ≤ Im a ≤ t + 1`: at most `1/ε + 1` real points, and for each
  `n < 1/ε` the points `ρ/n` come from zeros with `nt ≤ γ ≤ nt + n`.

The target `lem_Q_iii_proof` is at the end of this file (later files use it). The lemmas `zetaMult_le_log`,
`ncard_zeros_im_Icc_le`, `norm_Rcoef_le_log`, `poleSetQ_window_count` are proved in `Fill/<name>.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Target -/

/-- `lem_Q_iii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_Q_iii_proof (hZ1 : Z1) (hZ2 : Z2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ,
      (∀ a ∈ PoleSetQ, ε ≤ a.re → ‖Rcoef a‖ ≤ C * Real.log (|a.im| + 3)) ∧
      ∀ t : ℝ, {a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.Finite ∧
        ({a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.ncard : ℝ) ≤
          C * Real.log (|t| + 3) := by
  intro ε hε hε1
  obtain ⟨C₁, h₁⟩ := norm_Rcoef_le_log hZ1 hZ2 hε hε1
  obtain ⟨C₂, h₂⟩ := poleSetQ_window_count hZ1 hZ2 hε hε1
  refine ⟨max C₁ C₂, fun a ha hεa => ?_, fun t => ⟨(h₂ t).1, ?_⟩⟩
  · have hlog : 0 ≤ Real.log (|a.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg a.im])
    calc ‖Rcoef a‖ ≤ C₁ * Real.log (|a.im| + 3) := h₁ a ha hεa
      _ ≤ max C₁ C₂ * Real.log (|a.im| + 3) := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
  · have hlog : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
    calc _ ≤ C₂ * Real.log (|t| + 3) := (h₂ t).2
      _ ≤ max C₁ C₂ * Real.log (|t| + 3) := mul_le_mul_of_nonneg_right (le_max_right _ _) hlog

end GoldbachBoundaries.Paper2.M2
