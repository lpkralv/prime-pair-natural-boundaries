import PrimePairNB.HInf.MixDefs
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

lemma norm_Wlogq_le_WT (s : ℂ) (pq : Nat.Primes × Nat.Primes) {σ : ℝ}
    (hσ : σ ≤ s.re) :
    ‖Wlogq s pq.1 pq.2‖ ≤ (Real.log 2)⁻¹ * ‖WT (σ : ℂ) pq.1 pq.2‖ := by
  have hp : 0 ≤ Real.log (pq.1 : ℕ) := Real.log_natCast_nonneg _
  have hq : 0 ≤ Real.log (pq.2 : ℕ) := Real.log_natCast_nonneg _
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (pq.1 : ℕ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast pq.1.prop.two_le)
  have hn : 0 < (pq.1 : ℕ) + (pq.2 : ℕ) := by have := pq.1.prop.pos; omega
  have hn1 : (1 : ℝ) ≤ ((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) := by exact_mod_cast hn
  have hpow : (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-s.re) ≤
      (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hσ)
  simp only [Wlogq, WG, WT, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hp, abs_of_nonneg hq, norm_natCast_cpow_of_pos hn,
    neg_re, ofReal_re]
  have hc : 1 ≤ (Real.log 2)⁻¹ * Real.log (pq.1 : ℕ) := by
    rw [inv_mul_eq_div, le_div_iff₀ h2]
    simpa using hlog
  calc
    _ ≤ Real.log (pq.2 : ℕ) *
      (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-σ) := by gcongr
    _ ≤ ((Real.log 2)⁻¹ * Real.log (pq.1 : ℕ)) *
      (Real.log (pq.2 : ℕ) * (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-σ)) :=
        le_mul_of_one_le_left (by positivity) hc
    _ = _ := by ring

theorem MixSer_analyticAt {s : ℂ} (hs : 2 < s.re) : AnalyticAt ℂ MixSer s := by
  have hd : DifferentiableOn ℂ MixSer (halfPlane 2) := by
    apply M4b.differentiableOn_dser (isOpen_halfPlane 2)
    · intro pq
      have hn : ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast (by have := pq.1.prop.pos; omega : (pq.1 : ℕ) + (pq.2 : ℕ) ≠ 0)
      exact ((Differentiable.const_cpow (by fun_prop) (Or.inl hn)).const_mul _).differentiableOn
    · intro s₀ hs₀
      have hs₀' : 2 < s₀.re := hs₀
      let r := (s₀.re - 2) / 4
      let σ := s₀.re - r
      have hr : 0 < r := by dsimp [r]; linarith
      have hσ : 2 < σ := by dsimp [σ, r]; linarith
      refine ⟨closedBall s₀ r, closedBall_mem_nhds s₀ hr,
        fun pq : Nat.Primes × Nat.Primes => (Real.log 2)⁻¹ * ‖WT (σ : ℂ) pq.1 pq.2‖,
        ?_, ?_⟩
      · exact (M4b.hypR_kerG_WT.1 (σ : ℂ) (by simpa [Aff.RL, Aff.app, Aff.idL] using hσ)).mul_left _
      · intro v hv pq
        apply norm_Wlogq_le_WT
        have hh := (abs_le.mp ((Complex.abs_re_le_norm (v - s₀)).trans
          (show ‖v - s₀‖ ≤ r by simpa [dist_eq_norm] using hv))).1
        simp only [sub_re] at hh
        dsimp [σ]
        linarith
  exact hd.analyticAt ((isOpen_halfPlane 2).mem_nhds hs)

end GoldbachBoundaries.HInf
