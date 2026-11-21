import PrimePairNB.Paper2.M4b.Rising
import PrimePairNB.Paper2.M4b.Fill.DCommon
import PrimePairNB.Paper2.M4b.Fill.kerS_basic
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WG
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WT
import PrimePairNB.Paper2.M4b.Fill.E1Common

noncomputable section
open Complex Filter Topology Set MeasureTheory
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma square_weight (s : ℂ) (p q : Nat.Primes) :
    WSq s (p : ℕ) (q : ℕ) = ((q : ℕ) : ℂ) ^ (-(2 * s)) *
      ((((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (0 : ℂ) *
      (((1 + (((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) ^ (-s) := by
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.pos
  have he : (((((p : ℕ) ^ 2 + (q : ℕ) ^ 2) : ℕ) : ℂ)) =
      (((((q : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) * (((1 + (((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) := by
    push_cast
    field_simp [show ((q : ℕ) : ℂ) ≠ 0 by exact_mod_cast q.prop.ne_zero]
    <;> ring
  unfold WSq
  rw [he, mul_cpow_ofReal_nonneg (sq_nonneg _) (by positivity)]
  simp only [ofReal_pow, ofReal_natCast, ← natCast_cpow_natCast_mul, cpow_zero, mul_one]
  congr 1
  congr 1
  ring

private lemma square_kernel (z s : ℂ) : kMB 2 0 s z = kerSq z s := by
  simp [kMB, KerS, kerSq]
  ring

private lemma square_MB (s : ℂ) (c : ℝ) (hc1 : 1 < c) (hc2 : c < 2 * s.re - 1) :
    Summable (fun pq : Nat.Primes × Nat.Primes => ‖WSq s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
      Dser WSq s = VerticalIntegral' (fun z => kerSq z s * P z * P (2 * s - z)) c := by
  have h1 : 0 < (c + (0 : ℂ).re) / (2 : ℝ) := by simp; linarith
  have h2 : (c + (0 : ℂ).re) / (2 : ℝ) < s.re := by simp; linarith
  have hh := E1_MB_pair 2 (by norm_num) 0 s (2 * s) c hc1 (by simpa using hc2) h1 h2
  simpa only [← square_weight, square_kernel, Dser] using hh

/-- **(R) for `∑(p²+q²)^{-s}`** (no hypothesis). `R_L = {σ > 1}`, `R_L ∩ D_L = {1 < σ < 3/2}`, lines
`c ∈ (1, 2σ - 1)`. For primes, `(p² + q²)^{-s} = q^{-2s}·t^0(1 + t²)^{-s}` at `t = p/q` (positive reals,
`Complex.mul_cpow_ofReal_nonneg`). `mellinInv_kMB` with `a = 2`, `μ = 0`, `ν = s` (`0 < c/2 < σ`) gives the kernel
`kMB 2 0 s z = ½K_s(z/2) = kerSq z s` (`KerS`, `mul_div_assoc`), and `tsum_eq_verticalIntegral'_of_mellin` with
`ω = 1`, `L = 2s` (`twoL_app`, `primeSum_one`) gives absolute convergence at every `s ∈ R_L` (a line exists:
`2σ - 1 > 1`) and the identity. Holomorphy: `differentiableOn_dser` with
`‖(p²+q²)^{-s}‖ = (p²+q²)^{-σ} ≤ (p²+q²)^{-σ₁}` on `{σ ≥ σ₁}`, `σ₁ > 1` (summable by the first part at the real
point `σ₁`). Reality: real terms at real `s` (`Complex.im_tsum`). -/
theorem hypR_kerSq : HypR Aff.twoL kerSq WSq P := by
  have hsum : ∀ s : ℂ, 1 < s.re → Summable fun pq : Nat.Primes × Nat.Primes =>
      ‖WSq s (pq.1 : ℕ) (pq.2 : ℕ)‖ := by
    intro s hs
    exact (square_MB s s.re hs (by linarith)).1
  have hdiff : DifferentiableOn ℂ (Dser WSq) (halfPlane 1) := by
    apply E1_differentiable_halfPlane hsum
    · intro pq
      apply DifferentiableOn.const_cpow (by fun_prop)
      left
      exact_mod_cast (show (pq.1 : ℕ) ^ 2 + (pq.2 : ℕ) ^ 2 ≠ 0 by
        have := pq.1.prop.pos; positivity)
    · intro s x _ hxs pq
      exact norm_natCast_cpow_le_norm_natCast_cpow_of_pos
        (by have := pq.1.prop.pos; positivity)
        (by simp only [neg_re, ofReal_re]; linarith)
  have hRL : Aff.twoL.RL = halfPlane 1 := by
    ext s
    simp only [Aff.RL, twoL_app, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
      halfPlane, mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hRL] at hs
    exact hsum s hs
  · rwa [hRL]
  · intro x hx
    apply E1_dser_real
    intro pq
    simpa only [WSq, ofReal_neg] using E1_cpow_real ((pq.1 : ℕ) ^ 2 + (pq.2 : ℕ) ^ 2) (-x)
  · intro s hs c hc1 hc2
    simp only [twoL_app] at hc2 ⊢
    exact (square_MB s c hc1 (by simpa using hc2)).2

end GoldbachBoundaries.Paper2.M4b
