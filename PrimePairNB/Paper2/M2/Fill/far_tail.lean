import PrimePairNB.Paper2.M2.Single
import PrimePairNB.ThmA.Fill.germ_unique
import PrimePairNB.Paper2.M2.Fill.norm_far_term_le
import PrimePairNB.Paper2.M2.Fill.ncard_far_shell_le
import PrimePairNB.Paper2.M2.Fill.summable_tsum_le_of_shells
import PrimePairNB.Paper2.M2.Fill.far_tail_numeric

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The tail estimate for the far pairs** (Z1, Z2, Z6, `B < 1`). Index the far pairs by the shell
`sh p = ⌊|Im p.1|⌋₊`; shell `j` is finite with at most `C log(j + 4) ≤ C(j + 2)` elements (`ncard_far_shell_le`; the
far pairs have `|Im p.1| > H`, so only shells with `j + 1 > H` are non-empty), each of size at most
`C₃(j + 2)⁴e^{-πj}` (`norm_far_term_le`; `|Im p.1| > H ≥ 2Y`). `summable_tsum_le_of_shells` with
`b j = [H < j + 1] A(j + 2)⁵e^{-πj}` and `far_tail_numeric` (take `H₀ ≥ 2Y + 2` as well). -/
theorem far_tail (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ ≤ Real.exp (-H) := by
  classical
  obtain ⟨C, hC⟩ := ncard_far_shell_le hZ1 hZ2 hB
  obtain ⟨T, hT⟩ := norm_far_term_le hZ1 hZ2 hZ6 hB hY
  let C' := max C 0
  let T' := max T 0
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hT0 : 0 ≤ T' := le_max_right _ _
  obtain ⟨K, hK⟩ := far_tail_numeric (show 0 ≤ 2 * C' * T' by positivity)
  refine ⟨max K (2 * Y + 2), le_max_right _ _, ?_⟩
  intro H hH v hv hv1 hvY
  have hHY : 2 * Y ≤ H := by linarith [le_max_right K (2 * Y + 2)]
  have hnum := hK H ((le_max_left _ _).trans hH)
  let P := {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|}
  let f : P → ℝ := fun p => ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖
  let sh : P → ℕ := fun p => ⌊|p.1.1.im|⌋₊
  let S (j : ℕ) : Set (ℂ × ℂ) := {p | p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧
    (j : ℝ) ≤ |p.1.im| ∧ |p.1.im| < j + 1}
  have hmap (j : ℕ) : MapsTo (fun p : P => p.val) {p | sh p = j} (S j) := by
    intro p hp
    have hh := (Nat.floor_eq_iff (abs_nonneg p.1.1.im)).1 hp
    exact ⟨p.2.1, p.2.2.1, p.2.2.2.1, hh⟩
  have hfin (j : ℕ) : {p : P | sh p = j}.Finite :=
    Set.Finite.of_injOn (hmap j) Subtype.val_injective.injOn (hC v hv j).1
  have hcard (j : ℕ) : ({p : P | sh p = j}.ncard : ℝ) ≤ C' * Real.log (j + 4) := by
    have hc : {p : P | sh p = j}.ncard ≤ (S j).ncard :=
      Set.ncard_le_ncard_of_injOn _ (hmap j) Subtype.val_injective.injOn (hC v hv j).1
    calc
      ({p : P | sh p = j}.ncard : ℝ) ≤ ((S j).ncard : ℝ) := by exact_mod_cast hc
      _ ≤ C * Real.log (j + 4) := (hC v hv j).2
      _ ≤ C' * Real.log (j + 4) := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]))
  let b : ℕ → ℝ := fun j => if H < (j : ℝ) + 1 then
    (2 * C' * T') * ((j : ℝ) + 2) ^ 5 * Real.exp (-(Real.pi * j)) else 0
  have hb (j : ℕ) : ∑ᶠ p ∈ {p : P | sh p = j}, f p ≤ b j := by
    by_cases hj : H < (j : ℝ) + 1
    · have hterm (p : P) (hp : sh p = j) : f p ≤ T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-(Real.pi * j)) := by
        have hh := (Nat.floor_eq_iff (abs_nonneg p.1.1.im)).1 hp
        have ht := hT v hv hv1 hvY p.1 p.2.1 p.2.2.1 p.2.2.2.1 (hHY.trans p.2.2.2.2.le)
        calc
          f p ≤ T * (1 + |p.1.1.im|) ^ 4 * Real.exp (-(Real.pi * |p.1.1.im|)) := ht
          _ ≤ T' * (1 + |p.1.1.im|) ^ 4 * Real.exp (-(Real.pi * |p.1.1.im|)) := by
            gcongr; exact le_max_left _ _
          _ ≤ T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-(Real.pi * j)) := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left _ hT0
              exact pow_le_pow_left₀ (by positivity) (by linarith [hh.2]) 4
            · apply Real.exp_le_exp.mpr
              exact neg_le_neg (mul_le_mul_of_nonneg_left hh.1 Real.pi_pos.le)
            · positivity
            · positivity
      have hlog : Real.log ((j : ℝ) + 4) ≤ 2 * ((j : ℝ) + 2) := by
        have hh := Real.log_le_sub_one_of_pos (show 0 < (j : ℝ) + 4 by positivity)
        linarith [Nat.cast_nonneg (α := ℝ) j]
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfin j)]
      calc
        ∑ p ∈ (hfin j).toFinset, f p ≤
            ∑ _p ∈ (hfin j).toFinset, T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-(Real.pi * j)) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hterm p ((hfin j).mem_toFinset.mp hp)
        _ = ({p : P | sh p = j}.ncard : ℝ) *
            (T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-(Real.pi * j))) := by
          simp only [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ (hfin j)]
        _ ≤ (C' * Real.log (j + 4)) *
            (T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-(Real.pi * j))) := by gcongr; exact hcard j
        _ ≤ (C' * (2 * ((j : ℝ) + 2))) *
            (T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-(Real.pi * j))) := by gcongr
        _ = b j := by simp only [b, ite_eq_left hj]; ring
    · have hempty : {p : P | sh p = j} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro p hp
        have hh := (Nat.floor_eq_iff (abs_nonneg p.1.1.im)).1 hp
        exact hj (p.2.2.2.2.trans hh.2)
      simp [hempty, b, hj]
  have hs := summable_tsum_le_of_shells f (fun p => norm_nonneg _) sh b hfin hb hnum.1
  exact ⟨hs.1, hs.2.trans hnum.2⟩

end GoldbachBoundaries.Paper2.M2
