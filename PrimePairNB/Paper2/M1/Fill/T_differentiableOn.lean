import PrimePairNB.Paper2.M1.Kernel

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Weierstrass bound, following the unweighted proof in `ThmA/G20_Branches.lean`. -/
private lemma E2_T_diff_on {a : ℝ} (ha : 2 < a) : DifferentiableOn ℂ T (halfPlane a) := by
  let b : ℝ := a / 2
  have hb : 1 < b := by dsimp [b]; linarith
  let M : Nat.Primes → ℝ := fun p =>
    ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(b : ℂ))‖
  have hM : Summable M := summable_norm_Q_terms (by simpa using hb)
  have hnn : 0 ≤ M := fun _ => norm_nonneg _
  have hM2 := hM.mul_of_nonneg hM hnn hnn
  refine differentiableOn_tsum_of_summable_norm hM2 ?_ (isOpen_halfPlane a) ?_
  · intro pq w _
    have hn : (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ≠ 0 := by
      have hp := pq.1.prop.pos
      exact_mod_cast (by omega : (pq.1 : ℕ) + (pq.2 : ℕ) ≠ 0)
    exact ((differentiableAt_const _).mul
      (differentiableAt_id.neg.const_cpow (Or.inl hn))).differentiableWithinAt
  · intro pq w hw
    have hp : 0 < (pq.1 : ℕ) := pq.1.prop.pos
    have hq : 0 < (pq.2 : ℕ) := pq.2.prop.pos
    have hw' : a < w.re := hw
    let n : ℝ := ((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ)
    have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (by omega : 1 ≤ (pq.1 : ℕ) + (pq.2 : ℕ))
    have hpn : ((pq.1 : ℕ) : ℝ) ≤ n := by dsimp [n]; exact_mod_cast Nat.le_add_right _ _
    have hqn : ((pq.2 : ℕ) : ℝ) ≤ n := by dsimp [n]; exact_mod_cast Nat.le_add_left _ _
    have hk : n ^ (-w.re) ≤ ((pq.1 : ℕ) : ℝ) ^ (-b) * ((pq.2 : ℕ) : ℝ) ^ (-b) := by
      calc n ^ (-w.re) ≤ n ^ (-a) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = n ^ (-b) * n ^ (-b) := by
          rw [← Real.rpow_add (by linarith : 0 < n)]
          congr 1
          dsimp [b]
          ring
        _ ≤ ((pq.1 : ℕ) : ℝ) ^ (-b) * ((pq.2 : ℕ) : ℝ) ^ (-b) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hp) hpn (by linarith)
          · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hq) hqn (by linarith)
          · exact Real.rpow_nonneg (by linarith) _
          · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos (by omega), neg_re]
    calc ‖(Real.log (pq.1 : ℕ) : ℂ)‖ * ‖(Real.log (pq.2 : ℕ) : ℂ)‖ * n ^ (-w.re)
        ≤ ‖(Real.log (pq.1 : ℕ) : ℂ)‖ * ‖(Real.log (pq.2 : ℕ) : ℂ)‖ *
          (((pq.1 : ℕ) : ℝ) ^ (-b) * ((pq.2 : ℕ) : ℝ) ^ (-b)) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
      _ = M pq.1 * M pq.2 := by
        simp only [M, norm_mul, norm_natCast_cpow_of_pos hp,
          norm_natCast_cpow_of_pos hq, neg_re, ofReal_re]
        ring

/-- The series `T` is holomorphic on `σ > 2` (as `G_differentiableOn` of the RH development; Weierstrass M-test with
`|log p log q (p+q)^{-s}| ≤ log p log q (p+q)^{-σ₀}`). -/
theorem T_differentiableOn : DifferentiableOn ℂ T (halfPlane 2) := by
  intro s hs
  have ha : 2 < (s.re + 2) / 2 := by change 2 < s.re at hs; linarith
  have hsa : s ∈ halfPlane ((s.re + 2) / 2) := by change 2 < s.re at hs; change _ < s.re; linarith
  exact ((E2_T_diff_on ha).differentiableAt ((isOpen_halfPlane _).mem_nhds hsa)).differentiableWithinAt

end GoldbachBoundaries.Paper2.M1
