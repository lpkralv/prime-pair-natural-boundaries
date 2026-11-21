import PrimePairNB.Paper2.M2.Single
import PrimePairNB.ThmA.Fill.germ_unique

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The numerical tail** (real analysis). The shells `j` with `j + 1 > H` carry at most `A(j + 2)⁵e^{-πj}`; their
sum is `≤ A'(H + 3)⁵ e^{-π(H - 1)}`, which is `≤ e^{-H}` for `H ≥ H₀` (`(H + 3)⁵ e^{-(π - 1)H} → 0`). Summability
for every `H`: comparison with `(j + 2)⁵ e^{-πj}` (`summable_pow_mul_exp_neg_nat_mul` or ratio test). -/
theorem far_tail_numeric {A : ℝ} (hA : 0 ≤ A) :
    ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
      Summable (fun j : ℕ => if H < (j : ℝ) + 1 then A * ((j : ℝ) + 2) ^ 5 * Real.exp (-(Real.pi * j)) else 0) ∧
      ∑' j : ℕ, (if H < (j : ℝ) + 1 then A * ((j : ℝ) + 2) ^ 5 * Real.exp (-(Real.pi * j)) else 0) ≤
        Real.exp (-H) := by
  classical
  let c := Real.pi - 1
  have hc : 0 < c := by dsimp [c]; linarith [Real.pi_gt_three]
  let b : ℕ → ℝ := fun j => A * Real.exp 1 * ((j : ℝ) + 2) ^ 5 * Real.exp (-c * j)
  have hb0 : ∀ j, 0 ≤ b j := by intro j; dsimp [b]; positivity
  have hs : Summable b := by
    have hshift := (summable_nat_add_iff 2).2 (Real.summable_pow_mul_exp_neg_nat_mul 5 hc)
    have hh := hshift.mul_left (A * Real.exp 1 * Real.exp (2 * c))
    convert hh using 1
    ext j
    simp only [Nat.cast_add, Nat.cast_ofNat]
    dsimp [b]
    have he : Real.exp (-c * j) = Real.exp (2 * c) * Real.exp (-c * ((j : ℝ) + 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_sum_nat_add b).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨(N : ℝ) + 1, ?_⟩
  intro H hH
  let f : ℕ → ℝ := fun j => if H < (j : ℝ) + 1 then A * ((j : ℝ) + 2) ^ 5 * Real.exp (-(Real.pi * j)) else 0
  have hf0 : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; split_ifs <;> positivity
  have hle : ∀ j, f j ≤ Real.exp (-H) * b j := by
    intro j
    dsimp [f]
    split_ifs with hj
    · have he : Real.exp (-(Real.pi * j)) ≤ Real.exp (-H) * Real.exp 1 * Real.exp (-c * j) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [c]
        linarith
      dsimp [b]
      calc
        A * ((j : ℝ) + 2) ^ 5 * Real.exp (-(Real.pi * j))
          ≤ A * ((j : ℝ) + 2) ^ 5 * (Real.exp (-H) * Real.exp 1 * Real.exp (-c * j)) := by gcongr
        _ = _ := by ring
    · exact mul_nonneg (Real.exp_nonneg _) (hb0 j)
  have hfs : Summable f := (hs.mul_left (Real.exp (-H))).of_nonneg_of_le hf0 hle
  refine ⟨hfs, ?_⟩
  change ∑' j, f j ≤ _
  have hzero : ∑ j ∈ Finset.range N, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjN : (j : ℝ) < N := by exact_mod_cast Finset.mem_range.mp hj
    have hh : ¬ H < (j : ℝ) + 1 := by linarith
    simp [f, hh]
  have htail : (∑' j, f j) = ∑' j, f (j + N) := by
    have hh := hfs.sum_add_tsum_nat_add N
    simpa [hzero] using hh.symm
  rw [htail]
  calc
    ∑' j, f (j + N) ≤ ∑' j, Real.exp (-H) * b (j + N) :=
      Summable.tsum_le_tsum (fun j => hle (j + N)) ((summable_nat_add_iff N).2 hfs)
        (((summable_nat_add_iff N).2 hs).mul_left _)
    _ = Real.exp (-H) * ∑' j, b (j + N) := tsum_mul_left
    _ ≤ Real.exp (-H) * 1 := mul_le_mul_of_nonneg_left (le_of_lt (hN N le_rfl)) (Real.exp_nonneg _)
    _ = _ := mul_one _

end GoldbachBoundaries.Paper2.M2
