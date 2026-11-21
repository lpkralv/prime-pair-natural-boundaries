import PrimePairNB.Paper2.M4b.MB
import PrimePairNB.Paper2.M4b.Fill.ACommon
import PrimePairNB.Paper2.M4b.Fill.rising_summable_eq

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Holomorphy of `∑ ω(p)ω(q) Wrise`** on `σ > 2` (M-test). Each term is holomorphic in `s` (`hcf`, and
`s ↦ n^{-(s+i+j)}` entire for `n ≥ 1`). For `s₀` with `σ₀ > 2` put `r = (σ₀ - 2)/4`, `σ₁ = σ₀ - r > 2` and
`V = closedBall s₀ r ⊆ {σ ≥ σ₁}`: on `V`, `|c_{ij}(s)| ≤ C` (`hcf` gives continuity on the compact `V`),
`p^iq^j ≤ (p+q)^{i+j}`, `|(p+q)^{-(s+i+j)}| = (p+q)^{-σ-i-j} ≤ (p+q)^{-σ₁-i-j}`, so
`‖wtd ω (Wrise N cf) s p q‖ ≤ N²C · ω(p)ω(q)(p+q)^{-σ₁}`, and the right side is summable: it is
`N²C ‖wtd ω (Wrise 1 1) σ₁ p q‖`, summable by `rising_summable_eq` at `σ₁ > 2`. Conclude with
`differentiableOn_dser`. -/
theorem rising_differentiableOn {ω : ℕ → ℝ} (hω : PrimeWeight ω) (N : ℕ) (cf : ℕ → ℕ → ℂ → ℂ)
    (hcf : ∀ i j, DifferentiableOn ℂ (cf i j) (halfPlane 2)) :
    DifferentiableOn ℂ (Dser (wtd ω (Wrise N cf))) (halfPlane 2) := by
  apply differentiableOn_dser (isOpen_halfPlane 2)
  · intro pq
    have hn : (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by have := pq.1.prop.pos; omega : (pq.1 : ℕ) + (pq.2 : ℕ) ≠ 0)
    unfold wtd Wrise
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro i hi
    apply DifferentiableOn.fun_sum
    intro j hj
    apply DifferentiableOn.mul
    · exact ((hcf i j).mul_const _).mul_const _
    · exact (Differentiable.const_cpow (by fun_prop) (Or.inl hn)).differentiableOn
  · intro s₀ hs₀
    have hs₀' : 2 < s₀.re := hs₀
    let r : ℝ := (s₀.re - 2) / 4
    let σ : ℝ := s₀.re - r
    have hr : 0 < r := by dsimp [r]; linarith
    have hσ : 2 < σ := by dsimp [σ, r]; linarith
    have hlow : ∀ s ∈ closedBall s₀ r, σ ≤ s.re := by
      intro s hs
      have hn : ‖s - s₀‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hs
      have hb := (abs_le.mp ((abs_re_le_norm (s - s₀)).trans hn)).1
      simp only [sub_re] at hb
      dsimp [σ]
      linarith
    have hsub : closedBall s₀ r ⊆ halfPlane 2 := fun s hs => lt_of_lt_of_le hσ (hlow s hs)
    have hcont : ∀ i j, ContinuousOn (cf i j) (closedBall s₀ r) :=
      fun i j => (hcf i j).continuousOn.mono hsub
    choose C hC using fun i j => (isCompact_closedBall s₀ r).exists_bound_of_continuousOn (hcont i j)
    let M : Nat.Primes × Nat.Primes → ℝ := fun pq =>
      ‖(ω (pq.1 : ℕ) : ℂ) * (ω (pq.2 : ℕ) : ℂ) *
        (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-(σ : ℂ))‖
    have hM : Summable M := by
      simpa only [M, wtd, Wrise, Finset.range_one, Finset.sum_singleton,
        pow_zero, one_mul, mul_one, Nat.cast_zero, add_zero] using
        (rising_summable_eq hω 1 (fun _ _ _ => 1) (s := (σ : ℂ)) (by simpa using hσ)).1
    let u : Nat.Primes × Nat.Primes → ℝ := fun pq =>
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, C i j * M pq
    refine ⟨closedBall s₀ r, closedBall_mem_nhds s₀ hr, u, ?_, ?_⟩
    · exact A_summable_finset _ _ (fun i hi => A_summable_finset _ _ (fun j hj => hM.mul_left (C i j)))
    · intro s hs pq
      have hnonneg : ∀ i j, 0 ≤ C i j := by
        intro i j
        exact le_trans (norm_nonneg _) (hC i j s₀ (mem_closedBall_self hr.le))
      have hmono : ∀ i j : ℕ,
          ‖cf i j s * ((pq.1 : ℕ) : ℂ) ^ i * ((pq.2 : ℕ) : ℂ) ^ j *
            (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-(s + i + j))‖ ≤
          C i j * ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-σ)) := by
        intro i j
        calc _ = ‖cf i j s‖ * ‖((pq.1 : ℕ) : ℂ) ^ i * ((pq.2 : ℕ) : ℂ) ^ j *
            (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-(s + i + j))‖ := by
              rw [← norm_mul]; congr 1; ring
          _ ≤ _ := mul_le_mul (hC i j s hs) (A_norm_rising_le i j s pq.1 pq.2 (hlow s hs))
            (norm_nonneg _) (hnonneg i j)
      have hn : 0 < (pq.1 : ℕ) + (pq.2 : ℕ) := by have := pq.1.prop.pos; omega
      dsimp [wtd]
      rw [norm_mul]
      have hsum : ‖Wrise N cf s (pq.1 : ℕ) (pq.2 : ℕ)‖ ≤
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            C i j * ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-σ)) := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hmono i j))
      calc
        _ ≤ ‖(ω (pq.1 : ℕ) : ℂ) * (ω (pq.2 : ℕ) : ℂ)‖ *
            (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
              C i j * ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-σ))) :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
        _ = u pq := by
          dsimp [u, M]
          simp only [norm_mul, norm_natCast_cpow_of_pos hn, neg_re, ofReal_re, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

end GoldbachBoundaries.Paper2.M4b
