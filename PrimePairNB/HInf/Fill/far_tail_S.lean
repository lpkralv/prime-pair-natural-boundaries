import PrimePairNB.HInf.Fill.norm_KS_le

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2
namespace GoldbachBoundaries.HInf.Fill

private theorem norm_far_term_S (hZ1 : Z1) (hZ2 : Z2) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y → ∀ p ∈ pinchPairs (1 + v), p ≠ (1, v) →
      p ≠ (v, 1) → 2 * Y + 4 ≤ |p.1.im| →
        ‖Rcoef p.1 * Rcoef p.2 * KS ((p.1 - p.2 + 3) / 4)‖ ≤
          C * (1 + |p.1.im|) ^ 4 * Real.exp (-((Real.pi / 2) * |p.1.im|)) := by
  have hε : 0 < 1 - Bsup := by linarith
  have hε1 : 1 - Bsup < 1 := by linarith [(Bsup_facts hZ1).2.1]
  obtain ⟨R, hR⟩ := norm_Rcoef_le_log hZ1 hZ2 hε hε1
  let R' := max R 0
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hres (a : ℂ) (ha : a ∈ PoleSetQ) (haε : 1 - Bsup ≤ a.re) :
      ‖Rcoef a‖ ≤ R' * (|a.im| + 2) := by
    calc
      ‖Rcoef a‖ ≤ R * Real.log (|a.im| + 3) := hR a ha haε
      _ ≤ R' * Real.log (|a.im| + 3) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith [abs_nonneg a.im]))
      _ ≤ R' * (|a.im| + 2) := mul_le_mul_of_nonneg_left
        (by have := Real.log_le_sub_one_of_pos (show 0 < |a.im| + 3 by positivity); linarith) hR0
  refine ⟨R' ^ 2 * 7 * (Y + 3) ^ 3 * Real.exp (Real.pi * Y / 4), ?_⟩
  intro v hv hv1 hvY p hp hp1 hp2 ht
  have hm := pinchPairs_other_mem hZ1 hv hp hp1 hp2
  have ha := hres p.1 hm.1.1 hm.2.2.1.1.le
  have hb := hres p.2 hm.2.1.1 hm.2.2.2.1.le
  have hsum : p.1.im + p.2.im = v.im := by
    simpa only [add_im, one_im, zero_add] using congrArg Complex.im hp.2.2
  have hbi : |p.2.im| ≤ |p.1.im| + Y := by
    have hh : p.2.im = v.im - p.1.im := by linarith
    rw [hh]
    have := abs_sub v.im p.1.im
    linarith
  let w := (p.1 - p.2 + 3) / 4
  have wr : w.re = (p.1.re - p.2.re + 3) / 4 := by simp [w]
  have wi : w.im = (2 * p.1.im - v.im) / 4 := by simp [w]; linarith
  have hwlo : |p.1.im| / 2 - Y / 4 ≤ |w.im| := by
    have he : 2 * p.1.im = 4 * w.im + v.im := by linarith
    have hh := abs_add_le (4 * w.im) v.im
    rw [← he, abs_mul, abs_mul] at hh
    norm_num at hh
    linarith
  have hwhi : |w.im| ≤ |p.1.im| / 2 + Y / 4 := by
    rw [wi, abs_div]
    have hh := abs_sub (2 * p.1.im) v.im
    rw [abs_mul] at hh
    norm_num at hh ⊢
    linarith
  have hw := norm_KS_le (w := w) (by rw [wr]; linarith [hm.2.2.1.1, hm.2.2.2.2])
    (by rw [wr]; linarith [hm.2.2.2.1, hm.2.2.1.2]) (by linarith)
  let U := (Y + 3) * (1 + |p.1.im|)
  have haU : |p.1.im| + 2 ≤ U := by dsimp [U]; nlinarith [abs_nonneg p.1.im]
  have hbU : |p.2.im| + 2 ≤ U := by dsimp [U]; nlinarith [abs_nonneg p.1.im]
  have hwU : 1 + |w.im| ≤ U := by dsimp [U]; nlinarith [abs_nonneg p.1.im]
  have he : Real.exp (-(Real.pi * |w.im|)) ≤
      Real.exp (Real.pi * Y / 4) * Real.exp (-((Real.pi / 2) * |p.1.im|)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hpowers : (1 + |p.1.im|) ^ 3 ≤ (1 + |p.1.im|) ^ 4 := by
    exact pow_le_pow_right₀ (by linarith [abs_nonneg p.1.im]) (by norm_num)
  rw [norm_mul, norm_mul]
  calc
    ‖Rcoef p.1‖ * ‖Rcoef p.2‖ * ‖KS w‖ ≤
        (R' * U) * (R' * U) * (7 * U *
          (Real.exp (Real.pi * Y / 4) * Real.exp (-((Real.pi / 2) * |p.1.im|)))) := by
      gcongr
      · exact ha.trans (by gcongr)
      · exact hb.trans (by gcongr)
      · exact hw.trans (by gcongr)
    _ = (R' ^ 2 * 7 * (Y + 3) ^ 3 * Real.exp (Real.pi * Y / 4)) *
        (1 + |p.1.im|) ^ 3 * Real.exp (-((Real.pi / 2) * |p.1.im|)) := by dsimp [U]; ring
    _ ≤ _ := by gcongr

private theorem far_tail_numeric_S {A : ℝ} (hA : 0 ≤ A) :
    ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
      Summable (fun j : ℕ => if H < (j : ℝ) + 1 then A * ((j : ℝ) + 2) ^ 5 * Real.exp (-((Real.pi / 2) * j)) else 0) ∧
      ∑' j : ℕ, (if H < (j : ℝ) + 1 then A * ((j : ℝ) + 2) ^ 5 * Real.exp (-((Real.pi / 2) * j)) else 0) ≤
        Real.exp (-H) := by
  classical
  let c := (Real.pi / 2) - 1
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
  let f : ℕ → ℝ := fun j => if H < (j : ℝ) + 1 then A * ((j : ℝ) + 2) ^ 5 * Real.exp (-((Real.pi / 2) * j)) else 0
  have hf0 : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; split_ifs <;> positivity
  have hle : ∀ j, f j ≤ Real.exp (-H) * b j := by
    intro j
    dsimp [f]
    split_ifs with hj
    · have he : Real.exp (-((Real.pi / 2) * j)) ≤ Real.exp (-H) * Real.exp 1 * Real.exp (-c * j) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [c]
        linarith
      dsimp [b]
      calc
        A * ((j : ℝ) + 2) ^ 5 * Real.exp (-((Real.pi / 2) * j))
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

theorem far_tail_S (hZ1 : Z1) (hZ2 : Z2) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖Rcoef p.1.1 * Rcoef p.1.2 * KS ((p.1.1 - p.1.2 + 3) / 4)‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖Rcoef p.1.1 * Rcoef p.1.2 * KS ((p.1.1 - p.1.2 + 3) / 4)‖ ≤ Real.exp (-H) := by
  classical
  obtain ⟨C, hC⟩ := ncard_far_shell_le hZ1 hZ2 hB
  obtain ⟨T, hT⟩ := norm_far_term_S hZ1 hZ2 hB hY
  let C' := max C 0
  let T' := max T 0
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hT0 : 0 ≤ T' := le_max_right _ _
  obtain ⟨K, hK⟩ := far_tail_numeric_S (show 0 ≤ 2 * C' * T' by positivity)
  refine ⟨max K (2 * Y + 4), by linarith [le_max_right K (2 * Y + 4)], ?_⟩
  intro H hH v hv hv1 hvY
  have hHY : 2 * Y + 4 ≤ H := by linarith [le_max_right K (2 * Y + 4)]
  have hnum := hK H ((le_max_left _ _).trans hH)
  let P := {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|}
  let f : P → ℝ := fun p => ‖Rcoef p.1.1 * Rcoef p.1.2 * KS ((p.1.1 - p.1.2 + 3) / 4)‖
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
    (2 * C' * T') * ((j : ℝ) + 2) ^ 5 * Real.exp (-((Real.pi / 2) * j)) else 0
  have hb (j : ℕ) : ∑ᶠ p ∈ {p : P | sh p = j}, f p ≤ b j := by
    by_cases hj : H < (j : ℝ) + 1
    · have hterm (p : P) (hp : sh p = j) : f p ≤ T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-((Real.pi / 2) * j)) := by
        have hh := (Nat.floor_eq_iff (abs_nonneg p.1.1.im)).1 hp
        have ht := hT v hv hv1 hvY p.1 p.2.1 p.2.2.1 p.2.2.2.1 (hHY.trans p.2.2.2.2.le)
        calc
          f p ≤ T * (1 + |p.1.1.im|) ^ 4 * Real.exp (-((Real.pi / 2) * |p.1.1.im|)) := ht
          _ ≤ T' * (1 + |p.1.1.im|) ^ 4 * Real.exp (-((Real.pi / 2) * |p.1.1.im|)) := by
            gcongr; exact le_max_left _ _
          _ ≤ T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-((Real.pi / 2) * j)) := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left _ hT0
              exact pow_le_pow_left₀ (by positivity) (by linarith [hh.2]) 4
            · apply Real.exp_le_exp.mpr
              exact neg_le_neg (mul_le_mul_of_nonneg_left hh.1 (by positivity : 0 ≤ Real.pi / 2))
            · positivity
            · positivity
      have hlog : Real.log ((j : ℝ) + 4) ≤ 2 * ((j : ℝ) + 2) := by
        have hh := Real.log_le_sub_one_of_pos (show 0 < (j : ℝ) + 4 by positivity)
        linarith [Nat.cast_nonneg (α := ℝ) j]
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfin j)]
      calc
        ∑ p ∈ (hfin j).toFinset, f p ≤
            ∑ _p ∈ (hfin j).toFinset, T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-((Real.pi / 2) * j)) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hterm p ((hfin j).mem_toFinset.mp hp)
        _ = ({p : P | sh p = j}.ncard : ℝ) *
            (T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-((Real.pi / 2) * j))) := by
          simp only [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ (hfin j)]
        _ ≤ (C' * Real.log (j + 4)) *
            (T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-((Real.pi / 2) * j))) := by gcongr; exact hcard j
        _ ≤ (C' * (2 * ((j : ℝ) + 2))) *
            (T' * ((j : ℝ) + 2) ^ 4 * Real.exp (-((Real.pi / 2) * j))) := by gcongr
        _ = b j := by simp only [b, ite_eq_left hj]; ring
    · have hempty : {p : P | sh p = j} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro p hp
        have hh := (Nat.floor_eq_iff (abs_nonneg p.1.1.im)).1 hp
        exact hj (p.2.2.2.2.trans hh.2)
      simp [hempty, b, hj]
  have hs := summable_tsum_le_of_shells f (fun p => norm_nonneg _) sh b hfin hb hnum.1
  exact ⟨hs.1, hs.2.trans hnum.2⟩

end GoldbachBoundaries.HInf.Fill
