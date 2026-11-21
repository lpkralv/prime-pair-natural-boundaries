import PrimePairNB.HInf.Fill.prop71_S

/-!
Shared arithmetic for the square and later mixed kernels: shell summation at rate
`π/2`, and good-family counting with an arbitrary uniformly nonzero bracket.
The coefficient and the non-cancellation implication are explicit parameters.
-/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory ComplexConjugate
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2
namespace GoldbachBoundaries.HInf.Fill

theorem sqMix_far_tail_numeric {A : ℝ} (hA : 0 ≤ A) :
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

theorem sqMix_far_tail (hZ1 : Z1) (hZ2 : Z2) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y)
    (W : ℂ × ℂ → ℂ)
    (hW : ∃ T : ℝ, ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      ∀ p ∈ pinchPairs (1 + v), p ≠ (1, v) → p ≠ (v, 1) → 2 * Y + 4 ≤ |p.1.im| →
      ‖W p‖ ≤ T * (1 + |p.1.im|) ^ 4 * Real.exp (-((Real.pi / 2) * |p.1.im|))) :
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖W p.1‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖W p.1‖ ≤ Real.exp (-H) := by
  classical
  obtain ⟨C, hC⟩ := ncard_far_shell_le hZ1 hZ2 hB
  obtain ⟨T, hT⟩ := hW
  let C' := max C 0
  let T' := max T 0
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hT0 : 0 ≤ T' := le_max_right _ _
  obtain ⟨K, hK⟩ := sqMix_far_tail_numeric (show 0 ≤ 2 * C' * T' by positivity)
  refine ⟨max K (2 * Y + 4), by linarith [le_max_right K (2 * Y + 4)], ?_⟩
  intro H hH v hv hv1 hvY
  have hHY : 2 * Y + 4 ≤ H := by linarith [le_max_right K (2 * Y + 4)]
  have hnum := hK H ((le_max_left _ _).trans hH)
  let P := {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|}
  let f : P → ℝ := fun p => ‖W p.1‖
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

set_option maxHeartbeats 1000000 in
/-- Good-family counting for a bracket bounded away from zero on each window. -/
lemma sqMix_arith_core (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hB : Bsup < 1)
    (β : ℂ → ℂ)
    (hlower : ∀ y ε : ℝ, 0 < ε → ε < y →
      ∃ κ : ℝ, 0 < κ ∧ ∀ u ∈ closedBall ((y : ℂ) * I) ε, κ ≤ ‖β u‖)
    (T : ℂ → Prop)
    (hT : ∀ Y : ℝ, 0 < Y → ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
      ∀ u ∈ PoleSetQ, u ≠ 1 → 0 < u.re → u.re ≤ 1 → |u.im| ≤ Y → u ∉ NearBad H Y →
      Real.exp (-H) < ‖Rcoef u * β u‖ → T (1 + u))
    {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) (hε1 : ε < 1) :
    (arithPoints T y ε).Infinite := by
  obtain ⟨A₀, hA₀, t₀, hN0⟩ := hZ4
  obtain ⟨c₂, hc₂, X₀, hX₀⟩ := thm_single_proof hZ1 hZ2 hZ5 hA₀ hN0 hy hε hεy
  set Y : ℝ := y + 1 with hYdef
  have hY : 0 < Y := by linarith
  obtain ⟨H₀, hH₀⟩ := hT Y hY
  obtain ⟨C, hC, hSH⟩ := SH_finite_ncard_le hZ1 hZ2 hB
  obtain ⟨κ, hκ, hκbound⟩ := hlower y ε hε hεy
  let c := κ * (y - ε)
  have hc : 0 < c := mul_pos hκ (sub_pos.mpr hεy)
  apply infinite_of_forall_le_ncard
  intro N
  obtain ⟨X, hXbig, hXge, hXlog⟩ := ((eventually_nearBad_small hc₂ hC hY.le (N : ℝ)).and
    ((Filter.eventually_ge_atTop (max (max X₀ 3) (2 / c + 3))).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (H₀ / 2)))).exists
  have hX₀' : X₀ ≤ X := (le_max_left X₀ 3).trans ((le_max_left _ _).trans hXge)
  have hX3 : 3 ≤ X := (le_max_right X₀ 3).trans ((le_max_left _ _).trans hXge)
  have hXc : 2 / c + 3 ≤ X := (le_max_right _ _).trans hXge
  obtain ⟨hfin, -, -, hgood, hb, hinj⟩ := hX₀ X hX₀' hX3
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  set H : ℝ := 2 * Real.log X with hHdef
  have hH0 : 0 ≤ H := by positivity
  have hHH₀ : H₀ ≤ H := by linarith
  obtain ⟨hSHfin, hSHle⟩ := hSH (H + Y) (by linarith)
  obtain ⟨hNBfin, hNBle⟩ := nearBad_finite_ncard_le hZ1 hH0 hY.le hSHfin
  have hNBreal : ((NearBad H Y).ncard : ℝ) ≤ (C * (H + Y + 1) * Real.log (H + Y + 3)) ^ 2 := by
    have h1 : ((NearBad H Y).ncard : ℝ) ≤ ((SH (H + Y)).ncard : ℝ) ^ 2 := by exact_mod_cast hNBle
    exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hSHle 2)
  -- the good pairs, split by near-badness
  set G := {p : ℂ × ℕ | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2} with hG
  set Tbad := {p : ℂ × ℕ | p.1 / (p.2 : ℂ) ∈ NearBad H Y} with hTbad
  have hGsub : G ⊆ singlePairs A₀ y ε X := fun p hp => hp.1
  have hGfin : G.Finite := hfin.subset hGsub
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard G Tbad hGfin
  have hbad : (G ∩ Tbad).ncard ≤ (NearBad H Y).ncard :=
    Set.ncard_le_ncard_of_injOn (fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) (fun p hp => hp.2)
      (hinj.mono fun p hp => hGsub hp.1) hNBfin
  have hcount : (N : ℝ) ≤ ((G \ Tbad).ncard : ℝ) := by
    have e : ((G ∩ Tbad).ncard : ℝ) + ((G \ Tbad).ncard : ℝ) = (G.ncard : ℝ) := by exact_mod_cast hsplit
    have hbad' : ((G ∩ Tbad).ncard : ℝ) ≤ ((NearBad H Y).ncard : ℝ) := by exact_mod_cast hbad
    linarith
  -- the points `1 + u`
  have hinj' : InjOn (fun p : ℂ × ℕ => 1 + p.1 / (p.2 : ℂ)) (G \ Tbad) := by
    intro p hp p' hp' h
    exact hinj (hGsub hp.1) (hGsub hp'.1) (add_left_cancel h)
  refine ⟨(fun p : ℂ × ℕ => 1 + p.1 / (p.2 : ℂ)) '' (G \ Tbad), ?_, (hGfin.sdiff).image _, ?_⟩
  · rintro _ ⟨p, ⟨⟨hsp, hs⟩, hnT⟩, rfl⟩
    obtain ⟨hdist, hreu, -, -, hnorm, hlow⟩ := hb p hsp hs
    obtain ⟨hρ, hre, -, -, hq, -⟩ := hsp
    set u : ℂ := p.1 / (p.2 : ℂ) with hu
    refine ⟨p.1, hρ, hre, p.2, hq, rfl, hs, ?_, ?_⟩
    · rw [mem_ball, Complex.dist_eq]
      convert hdist using 2
      ring
    · have huQ : u ∈ PoleSetQ := Or.inr ⟨p.2, hq.one_lt.le, hq.squarefree, p.1, hρ, rfl⟩
      have hq2 : (2 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hq.two_le
      have hre0 : 0 < u.re := by rw [hreu]; positivity
      have hre1 : u.re ≤ 1 := by
        rw [hreu, div_le_one (by positivity)]; linarith
      have hu1 : u ≠ 1 := by
        intro h1
        have : u.re = 1 := by rw [h1, one_re]
        rw [hreu, div_eq_one_iff_eq (by positivity)] at this
        linarith
      have hYu : |u.im| ≤ Y := by
        have him : |(u - (y : ℂ) * I).im| ≤ ‖u - (y : ℂ) * I‖ := Complex.abs_im_le_norm _
        have e : (u - (y : ℂ) * I).im = u.im - y := by simp
        rw [e] at him
        have := lt_of_le_of_lt him hdist
        rw [abs_lt] at this
        rw [abs_le]
        constructor <;> linarith
      have hexpS : Real.exp (-H) < ‖Rcoef u * β u‖ := by
        have hX0 : 0 < X := by linarith
        have e1 : Real.exp (-H) = (X ^ 2)⁻¹ := by
          rw [hHdef, show -(2 * Real.log X) = Real.log ((X ^ 2)⁻¹) by
            rw [Real.log_inv, Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
        have hXmul : 2 < c * X := by
          have hh := (div_le_iff₀ hc).mp (show 2 / c ≤ X - 3 by linarith)
          nlinarith
        have e2 : (X ^ 2)⁻¹ < c / (X + 1) := by
          rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have huNorm : y - ε ≤ ‖u‖ := by
          have hi := (Complex.abs_im_le_norm (u - (y : ℂ) * I)).trans hdist.le
          have hi' : |u.im - y| ≤ ε := by simpa using hi
          have hh := (abs_le.mp hi').1
          linarith [Complex.im_le_norm u]
        have hu0 : 0 < ‖u‖ := lt_of_lt_of_le (sub_pos.mpr hεy) huNorm
        have hR : ‖u‖ / (X + 1) ≤ ‖Rcoef u‖ := by
          have hh : 2 / (X + 1) ≤ 2 * ‖Rcoef u‖ / ‖u‖ := by
            rw [← hnorm, norm_div, norm_mul, norm_ofNat] at hlow
            exact hlow
          have hh' := (le_div_iff₀ hu0).mp hh
          rw [div_mul_eq_mul_div] at hh'
          have hh'' := (div_le_iff₀ (by positivity : 0 < X + 1)).mp hh'
          apply (div_le_iff₀ (by positivity : 0 < X + 1)).mpr
          linarith only [hh'']
        have hbκ := hκbound u (mem_closedBall.mpr (by rw [dist_eq_norm]; exact hdist.le))
        rw [e1, norm_mul]
        calc
          (X ^ 2)⁻¹ < c / (X + 1) := e2
          _ = ((y - ε) / (X + 1)) * κ := by dsimp [c]; ring
          _ ≤ (‖u‖ / (X + 1)) * κ := by gcongr
          _ ≤ ‖Rcoef u‖ * ‖β u‖ := by gcongr
      exact hH₀ H hHH₀ u huQ hu1 hre0 hre1 hYu hnT hexpS
  · rw [hinj'.ncard_image]
    exact_mod_cast hcount

end GoldbachBoundaries.HInf.Fill
