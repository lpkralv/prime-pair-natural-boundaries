import PrimePairNB.Paper2.M2.Far

/-! `SH_finite_ncard_le` (`Lambda.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`|𝒮_H| ≪ (H + 1) log(H + 3)`** (Z1, Z2, `B < 1`). Cover `SH H` by the `2n + 1` unit windows
`[-n + i, -n + i + 1]`, `n = ⌈H⌉`, of `lem_Q_iii_proof` with `ε = 1 - B`. -/
theorem SH_finite_ncard_le (hZ1 : Z1) (hZ2 : Z2) (hB : Bsup < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 0 ≤ H →
      (SH H).Finite ∧ ((SH H).ncard : ℝ) ≤ C * (H + 1) * Real.log (H + 3) := by
  have hB2 := (Bsup_facts hZ1).2.1
  obtain ⟨C, -, hW⟩ := lem_Q_iii_proof hZ1 hZ2 (1 - Bsup) (by linarith) (by linarith)
  set C' := max C 0 with hC'
  refine ⟨6 * C', by positivity, fun H hH => ?_⟩
  set n : ℕ := ⌈H⌉₊ with hn
  set W : ℕ → Set ℂ := fun i => {a | a ∈ PoleSetQ ∧ 1 - Bsup ≤ a.re ∧ (-(n : ℝ) + i) ≤ a.im ∧
    a.im ≤ (-(n : ℝ) + i) + 1} with hWdef
  have hsub : SH H ⊆ ⋃ i ∈ Finset.range (2 * n + 1), W i := by
    rintro a ⟨ha, -, hre, him⟩
    have hHn : H ≤ n := Nat.le_ceil H
    rw [abs_le] at him
    have h0 : 0 ≤ a.im + n := by linarith
    refine mem_iUnion₂.mpr ⟨⌊a.im + n⌋₊, ?_, ha, hre.le, ?_, ?_⟩
    · rw [Finset.mem_range]
      have : ⌊a.im + n⌋₊ ≤ 2 * n := by
        apply Nat.floor_le_of_le
        push_cast
        linarith
      omega
    · linarith [Nat.floor_le h0]
    · linarith [Nat.lt_floor_add_one (a.im + n)]
  have hWfin : ∀ i, (W i).Finite := fun i => (hW (-(n : ℝ) + i)).1
  have hfinU : (⋃ i ∈ Finset.range (2 * n + 1), W i).Finite :=
    (Finset.range (2 * n + 1)).finite_toSet.biUnion fun i _ => hWfin i
  refine ⟨hfinU.subset hsub, ?_⟩
  have hlog3 : 0 ≤ Real.log (H + 3) := Real.log_nonneg (by linarith)
  have hWle : ∀ i ∈ Finset.range (2 * n + 1), ((W i).ncard : ℝ) ≤ C' * Real.log ((n : ℝ) + 3) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi' : (i : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : i ≤ 2 * n)
    have habs : |(-(n : ℝ) + i)| ≤ n := by
      rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    calc ((W i).ncard : ℝ) ≤ C * Real.log (|(-(n : ℝ) + i)| + 3) := (hW (-(n : ℝ) + i)).2
      _ ≤ C' * Real.log (|(-(n : ℝ) + i)| + 3) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith [abs_nonneg (-(n : ℝ) + i)]))
      _ ≤ C' * Real.log ((n : ℝ) + 3) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          exact Real.log_le_log (by positivity) (by linarith)
  have hnH : (n : ℝ) < H + 1 := Nat.ceil_lt_add_one hH
  have hlogn : Real.log ((n : ℝ) + 3) ≤ 2 * Real.log (H + 3) := by
    rw [← Real.log_rpow (by linarith : (0 : ℝ) < H + 3)]
    apply Real.log_le_log (by positivity)
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  calc ((SH H).ncard : ℝ) ≤ ((⋃ i ∈ Finset.range (2 * n + 1), W i).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfinU
    _ ≤ ∑ i ∈ Finset.range (2 * n + 1), ((W i).ncard : ℝ) := by
        exact_mod_cast Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ i ∈ Finset.range (2 * n + 1), C' * Real.log ((n : ℝ) + 3) := Finset.sum_le_sum hWle
    _ = (2 * n + 1 : ℝ) * (C' * Real.log ((n : ℝ) + 3)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (3 * (H + 1)) * (C' * (2 * Real.log (H + 3))) := by
        have hC0 : 0 ≤ C' := le_max_right _ _
        apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hlogn hC0)
          (mul_nonneg hC0 (Real.log_nonneg (by linarith))) (by linarith)
    _ = 6 * C' * (H + 1) * Real.log (H + 3) := by ring

end GoldbachBoundaries.Paper2.M2
