import PrimePairNB.Paper2.M2.Defs
import PrimePairNB.Paper2.M2.Fill.ncard_zeros_im_Icc_le
import PrimePairNB.Paper2.M2.Fill.ACommon

noncomputable section
open Complex Set
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Points of `Σ_Q` in a unit window** (Z1, Z2; second half of Paper, Lemma 2.1). The set is contained in
`{1} ∪ {1/k : 2 ≤ k ≤ 1/ε} ∪ ⋃_{1 ≤ n ≤ 1/ε} (· / n) '' {ρ : nt ≤ γ ≤ nt + n}` (a point `ρ/n` with
`Re = β/n ≥ ε` has `n < 1/ε`; `t ≤ γ/n ≤ t + 1` is `nt ≤ γ ≤ nt + n`). By `ncard_zeros_im_Icc_le` with `L = n` the
`n`-th piece has at most `C n log(n|t| + n + 3) ≪_ε log(|t| + 3)` points; sum over `n ≤ 1/ε`. -/
theorem poleSetQ_window_count (hZ1 : Z1) (hZ2 : Z2) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, ∀ t : ℝ, {a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.Finite ∧
      ({a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.ncard : ℝ) ≤ C * Real.log (|t| + 3) := by
  classical
  obtain ⟨N, hN2, hN⟩ := exists_tail_index hε 2
  obtain ⟨C₀, hC₀⟩ := ncard_zeros_im_Icc_le hZ1 hZ2
  let D := max C₀ 0
  let E := 1 + Real.log (N + 1) / Real.log 3
  let B := D * N * E
  have hD : 0 ≤ D := le_max_right _ _
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hN1 : 1 ≤ N := by omega
  let R : Set ℂ := (fun n : ℕ => 1 / (n : ℂ)) '' (Finset.range N : Set ℕ)
  have hRf : R.Finite := (Finset.finite_toSet _).image _
  have hRc : R.ncard ≤ N := (Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
  refine ⟨N / Real.log 3 + N * B, fun t => ?_⟩
  let T : ℕ → Set ℂ := fun n => {ρ | ρ ∈ NontrivialZeros ∧ (n : ℝ) * t ≤ ρ.im ∧ ρ.im ≤ (n : ℝ) * t + n}
  let S : ℕ → Set ℂ := fun n => if n = 0 then ∅ else (fun ρ : ℂ => ρ / (n : ℂ)) '' T n
  have hTf : ∀ n, (T n).Finite := fun n => A_finite_strip ((n : ℝ) * t) n
  have hSf : ∀ n, (S n).Finite := by
    intro n
    by_cases h : n = 0
    · simp [S, h]
    · simpa only [S, if_neg h] using (hTf n).image (fun ρ : ℂ => ρ / (n : ℂ))
  have hSc : ∀ n ∈ Finset.range N, ((S n).ncard : ℝ) ≤ B * Real.log (|t| + 3) := by
    intro n hn
    have hl0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
    by_cases hn0 : n = 0
    · simp [S, hn0, mul_nonneg hB hl0]
    have hn1 : 1 ≤ n := by omega
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
    have hlog0 : 0 ≤ Real.log (|(n : ℝ) * t| + n + 3) := Real.log_nonneg (by linarith [abs_nonneg ((n : ℝ) * t), Nat.cast_nonneg (α := ℝ) n])
    have hlog : Real.log (|(n : ℝ) * t| + n + 3) ≤ E * Real.log (|t| + 3) := by
      calc _ ≤ Real.log ((N : ℝ) * |t| + N + 3) := by
            apply Real.log_le_log (by positivity)
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            nlinarith [abs_nonneg t]
        _ ≤ _ := A_log_scale (abs_nonneg _) hN1
    calc ((S n).ncard : ℝ) ≤ ((T n).ncard : ℝ) := by
          dsimp [S]; rw [if_neg hn0]; exact_mod_cast Set.ncard_image_le (hTf n)
      _ ≤ C₀ * n * Real.log (|(n : ℝ) * t| + n + 3) := (hC₀ ((n : ℝ) * t) n hn1).2
      _ ≤ D * N * (E * Real.log (|t| + 3)) := by
          apply mul_le_mul
          · calc C₀ * n ≤ D * n := mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
                 _ ≤ D * N := mul_le_mul_of_nonneg_left hnN hD
          · exact hlog
          · exact hlog0
          · positivity
      _ = _ := by dsimp [B]; ring
  let U := ⋃ n ∈ Finset.range N, S n
  have hUf : U.Finite := (Finset.finite_toSet (Finset.range N)).biUnion fun n _ => hSf n
  have hUc : (U.ncard : ℝ) ≤ N * (B * Real.log (|t| + 3)) := by
    calc _ ≤ ((∑ n ∈ Finset.range N, (S n).ncard : ℕ) : ℝ) := by
            exact_mod_cast (Finset.range N).set_ncard_biUnion_le S
      _ = ∑ n ∈ Finset.range N, ((S n).ncard : ℝ) := by push_cast; rfl
      _ ≤ ∑ _ ∈ Finset.range N, B * Real.log (|t| + 3) := Finset.sum_le_sum hSc
      _ = _ := by simp
  have hsub : {a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1} ⊆ R ∪ U := by
    rintro a ⟨ha, hea, hat, hat'⟩
    rcases ha with (ha | ⟨k, hk, hsq, rfl⟩) | ⟨n, hn, hsq, ρ, hρ, rfl⟩
    · left
      refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
      simpa using ha.symm
    · left
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hea' : ε ≤ 1 / (k : ℝ) := by simpa only [div_natCast_re, one_re] using hea
      have he : ε * k ≤ 1 := (le_div_iff₀ hkR).mp hea'
      have hkN : k < N := by
        by_contra h
        have : (N : ℝ) ≤ k := by exact_mod_cast (by omega : N ≤ k)
        nlinarith
      exact ⟨k, Finset.mem_range.mpr hkN, rfl⟩
    · right
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have he : ε * n ≤ ρ.re := by
        rw [div_natCast_re] at hea
        exact (le_div_iff₀ hnR).mp hea
      have hnN : n < N := by
        by_contra h
        have : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
        nlinarith [hρ.2.2]
      refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hnN, ?_⟩⟩
      dsimp [S]
      rw [if_neg (by omega : n ≠ 0)]
      refine ⟨ρ, ⟨hρ, ?_, ?_⟩, rfl⟩
      · rw [div_natCast_im] at hat
        nlinarith [(le_div_iff₀ hnR).mp hat]
      · rw [div_natCast_im] at hat'
        nlinarith [(div_le_iff₀ hnR).mp hat']
  refine ⟨(hRf.union hUf).subset hsub, ?_⟩
  have hl : Real.log 3 ≤ Real.log (|t| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hreal : (N : ℝ) ≤ N / Real.log 3 * Real.log (|t| + 3) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl3]
    exact mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
  calc _ ≤ ((R ∪ U).ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub (hRf.union hUf)
    _ ≤ (R.ncard : ℝ) + (U.ncard : ℝ) := by exact_mod_cast Set.ncard_union_le R U
    _ ≤ (N : ℝ) + N * (B * Real.log (|t| + 3)) := add_le_add (by exact_mod_cast hRc) hUc
    _ ≤ _ := by nlinarith
end GoldbachBoundaries.Paper2.M2
