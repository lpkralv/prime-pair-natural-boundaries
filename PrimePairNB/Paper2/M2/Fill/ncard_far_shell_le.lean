import PrimePairNB.Paper2.M2.Single
import PrimePairNB.ThmA.Fill.germ_unique
import PrimePairNB.Paper2.M2.Fill.pinchPairs_other_mem

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Competing pairs per unit shell** (Z1, Z2, `B < 1`). The map `p ↦ p.1` is injective on `pinchPairs (1 + v)`
(`p.2 = 1 + v - p.1`), and `p.1 ∈ Σ_Q` with `Re p.1 > 1 - B` (`pinchPairs_other_mem`) and
`Im p.1 ∈ [j, j + 1] ∪ [-j - 1, -j]`: two windows of `lem_Q_iii_proof` with `ε = 1 - B`, each with at most
`C log(j + 3)` points. -/
theorem ncard_far_shell_le (hZ1 : Z1) (hZ2 : Z2) (hB : Bsup < 1) :
    ∃ C : ℝ, ∀ v : ℂ, 0 < v.re → ∀ j : ℕ,
      {p | p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ (j : ℝ) ≤ |p.1.im| ∧ |p.1.im| < j + 1}.Finite ∧
      ({p | p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ (j : ℝ) ≤ |p.1.im| ∧
          |p.1.im| < j + 1}.ncard : ℝ) ≤ C * Real.log (j + 4) := by
  have hε : 0 < 1 - Bsup := by linarith
  have hε1 : 1 - Bsup < 1 := by linarith [(Bsup_facts hZ1).2.1]
  obtain ⟨C, hC⟩ := poleSetQ_window_count hZ1 hZ2 hε hε1
  have hC0 : 0 ≤ C := by
    have h := (hC 0).2
    have hlog : 0 < Real.log (|(0 : ℝ)| + 3) := Real.log_pos (by norm_num)
    have hn : (0 : ℝ) ≤ ({a : ℂ | a ∈ PoleSetQ ∧ 1 - Bsup ≤ a.re ∧ 0 ≤ a.im ∧ a.im ≤ 0 + 1}.ncard : ℝ) := Nat.cast_nonneg _
    nlinarith
  refine ⟨2 * C, ?_⟩
  intro v hv j
  let S : Set (ℂ × ℂ) := {p | p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧
    (j : ℝ) ≤ |p.1.im| ∧ |p.1.im| < j + 1}
  let W (t : ℝ) : Set ℂ := {a | a ∈ PoleSetQ ∧ 1 - Bsup ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}
  have hmap : Prod.fst '' S ⊆ W j ∪ W (-(j : ℝ) - 1) := by
    rintro a ⟨p, hp, rfl⟩
    have ha := pinchPairs_other_mem hZ1 hv hp.1 hp.2.1 hp.2.2.1
    have habs := hp.2.2.2
    by_cases ht : 0 ≤ p.1.im
    · left
      exact ⟨ha.1.1, ha.2.2.1.1.le, by simpa [abs_of_nonneg ht] using habs.1,
        by simpa [abs_of_nonneg ht] using habs.2.le⟩
    · right
      rw [abs_of_neg (lt_of_not_ge ht)] at habs
      exact ⟨ha.1.1, ha.2.2.1.1.le, by linarith [habs.2], by linarith [habs.1]⟩
  have hinj : InjOn Prod.fst S := by
    intro p hp q hq heq
    apply Prod.ext heq
    have hpq := hp.1.2.2
    have hqq := hq.1.2.2
    linear_combination hpq - hqq - heq
  have hW : (W j ∪ W (-(j : ℝ) - 1)).Finite := (hC j).1.union (hC (-(j : ℝ) - 1)).1
  have hS : S.Finite := (hW.subset hmap).of_finite_image hinj
  refine ⟨hS, ?_⟩
  change (S.ncard : ℝ) ≤ _
  have hcount : S.ncard ≤ (W j).ncard + (W (-(j : ℝ) - 1)).ncard := by
    calc
      S.ncard = (Prod.fst '' S).ncard := (hinj.ncard_image).symm
      _ ≤ (W j ∪ W (-(j : ℝ) - 1)).ncard := Set.ncard_le_ncard hmap hW
      _ ≤ _ := Set.ncard_union_le _ _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpos := (hC (j : ℝ)).2
  have hneg := (hC (-(j : ℝ) - 1)).2
  have habs : |-(j : ℝ) - 1| + 3 = j + 4 := by rw [abs_of_nonpos (by linarith)]; ring
  rw [abs_of_nonneg hj] at hpos
  rw [habs] at hneg
  have hlog : Real.log ((j : ℝ) + 3) ≤ Real.log (j + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpos' := hpos.trans (mul_le_mul_of_nonneg_left hlog hC0)
  have hcast : (S.ncard : ℝ) ≤ (W j).ncard + (W (-(j : ℝ) - 1)).ncard := by exact_mod_cast hcount
  linarith

end GoldbachBoundaries.Paper2.M2
