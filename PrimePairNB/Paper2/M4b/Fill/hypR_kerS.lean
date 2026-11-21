import PrimePairNB.Paper2.M4b.Rising
import PrimePairNB.Paper2.M4b.Fill.DCommon
import PrimePairNB.Paper2.M4b.Fill.kerS_basic
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WG
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WT
import PrimePairNB.Paper2.M4b.Fill.E1Common
import PrimePairNB.Paper2.M4b.Fill.hypR_kerSq

noncomputable section
open Complex Filter Topology Set MeasureTheory
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma S_weight (s : ℂ) (p q : Nat.Primes) :
    WS s (p : ℕ) (q : ℕ) = ((q : ℕ) : ℂ) ^ (-(2 * s + 1)) *
      ((((p : ℕ) : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (1 - s) *
      (((1 + (((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) ^ (-(2 : ℂ)) := by
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.pos
  have hq0 : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
  have he : (((((p : ℕ) ^ 2 + (q : ℕ) ^ 2) : ℕ) : ℂ)) =
      (((((q : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) * (((1 + (((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) := by
    push_cast
    field_simp [show ((q : ℕ) : ℂ) ≠ 0 by exact_mod_cast q.prop.ne_zero]
    <;> ring
  have hsquare : ((((((p : ℕ) ^ 2 + (q : ℕ) ^ 2) : ℕ) : ℂ)) ^ 2)⁻¹ =
      ((q : ℕ) : ℂ) ^ (-(4 : ℂ)) *
        (((1 + (((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) ^ (-(2 : ℂ)) := by
    rw [← cpow_ofNat, ← cpow_neg, he,
      mul_cpow_ofReal_nonneg (sq_nonneg _) (by positivity)]
    simp only [ofReal_pow, ofReal_natCast, ← natCast_cpow_natCast_mul]
    norm_num
  have hdiv :
      (((((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : ℝ) : ℂ) ^ (1 - s) =
        ((p : ℕ) : ℂ) ^ (1 - s) / ((q : ℕ) : ℂ) ^ (1 - s) := by
    simpa only [ofReal_div, ofReal_natCast] using
      div_cpow_ofReal_nonneg (a := ((p : ℕ) : ℝ)) (b := ((q : ℕ) : ℝ))
        (Nat.cast_nonneg _) hq.le (1 - s)
  unfold WS
  rw [hsquare, hdiv]
  calc
    _ = ((p : ℕ) : ℂ) ^ (1 - s) * ((q : ℕ) : ℂ) ^ ((2 - s) + -(4 : ℂ)) *
        (((1 + (((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) ^ (-(2 : ℂ)) := by
      rw [cpow_add _ _ hq0]
      ring
    _ = ((p : ℕ) : ℂ) ^ (1 - s) * ((q : ℕ) : ℂ) ^ (-(2 * s + 1) - (1 - s)) *
        (((1 + (((p : ℕ) : ℝ) / ((q : ℕ) : ℝ)) ^ 2 : ℝ)) : ℂ) ^ (-(2 : ℂ)) := by
      congr 2
      congr 1
      ring
    _ = _ := by rw [cpow_sub _ _ hq0]; ring

private lemma S_kernel (z s : ℂ) : kMB 2 (1 - s) 2 z = kerS z s := by
  simp only [kMB, KerS, kerS, KS, Nat.cast_ofNat]
  have hG : Gamma (2 : ℂ) = 1 := by simpa using Gamma_add_one (1 : ℂ) one_ne_zero
  rw [hG]
  have he : (z + (1 - s)) / 2 = (z - s + 1) / 2 := by ring
  rw [he]
  norm_num

private lemma S_MB (s : ℂ) (c : ℝ) (hc1 : 1 < c) (hc2 : c < 2 * s.re)
    (hlo : s.re - 1 < c) (hhi : c < s.re + 3) :
    Summable (fun pq : Nat.Primes × Nat.Primes => ‖WS s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
      Dser WS s = VerticalIntegral' (fun z => kerS z s * P z * P (2 * s + 1 - z)) c := by
  have h1 : 0 < (c + (1 - s).re) / (2 : ℝ) := by simp; linarith
  have h2 : (c + (1 - s).re) / (2 : ℝ) < (2 : ℂ).re := by simp; linarith
  have hh := E1_MB_pair 2 (by norm_num) (1 - s) 2 (2 * s + 1) c hc1
    (by simpa using hc2) h1 h2
  simpa only [← S_weight, S_kernel, Dser] using hh

/-- **(R) for `S`** (no hypothesis). `R_L = {σ > 1/2}`, `R_L ∩ D_L = {1/2 < σ < 1}`, lines `c ∈ (1, 2σ)`. For primes,
`p^{1-s}q^{2-s}(p²+q²)^{-2} = q^{-(2s+1)}·t^{1-s}(1 + t²)^{-2}` at `t = p/q` (positive reals; `((p²+q²)²)⁻¹ =
q^{-4}(1 + t²)^{-2}`). `mellinInv_kMB` with `a = 2`, `μ = 1 - s`, `ν = 2` needs `0 < (c + 1 - σ)/2 < 2`, i.e.
`σ - 1 < c < σ + 3`; on the lines of (R) this holds (`c > 1 > σ - 1`, `c < 2σ < σ + 3`), and for absolute convergence at
any `s ∈ R_L` choose `c ∈ (max(1, σ - 1), min(2σ, σ + 3))`. The kernel `kMB 2 (1 - s) 2 z = ½Γ(w)Γ(2 - w)/Γ(2)` with
`w = (z + 1 - s)/2`, `Γ(2) = 1` (`Complex.Gamma_two`), is `kerS z s`. `tsum_eq_verticalIntegral'_of_mellin` with `ω = 1`,
`L = 2s + 1` (`twoOneL_app`, `primeSum_one`). Holomorphy: `differentiableOn_dser` with
`‖W_S(s)‖ = p^{1-σ}q^{2-σ}(p²+q²)^{-2} ≤` its value at `σ₁` on `{σ ≥ σ₁}`, `σ₁ > 1/2`. Reality: real terms at real `s`. -/
theorem hypR_kerS : HypR Aff.twoOneL kerS WS P := by
  have hsum : ∀ s : ℂ, 1 / 2 < s.re → Summable fun pq : Nat.Primes × Nat.Primes =>
      ‖WS s (pq.1 : ℕ) (pq.2 : ℕ)‖ := by
    intro s hs
    exact (S_MB s (s.re + 1 / 2) (by linarith) (by linarith) (by linarith) (by linarith)).1
  have hdiff : DifferentiableOn ℂ (Dser WS) (halfPlane (1 / 2)) := by
    apply E1_differentiable_halfPlane hsum
    · intro pq
      apply DifferentiableOn.mul_const
      apply DifferentiableOn.mul
      · apply DifferentiableOn.const_cpow (by fun_prop)
        exact Or.inl (by exact_mod_cast pq.1.prop.ne_zero)
      · apply DifferentiableOn.const_cpow (by fun_prop)
        exact Or.inl (by exact_mod_cast pq.2.prop.ne_zero)
    · intro s x _ hxs pq
      unfold WS
      simp only [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul
      · exact norm_natCast_cpow_le_norm_natCast_cpow_of_pos pq.1.prop.pos
          (by simp only [sub_re, one_re, ofReal_re]; linarith)
      · exact norm_natCast_cpow_le_norm_natCast_cpow_of_pos pq.2.prop.pos
          (by simp only [sub_re, re_ofNat, ofReal_re]; linarith)
      · positivity
      · positivity
  have hRL : Aff.twoOneL.RL = halfPlane (1 / 2) := by
    ext s
    simp only [Aff.RL, twoOneL_app, add_re, mul_re, re_ofNat, im_ofNat, zero_mul,
      sub_zero, one_re, halfPlane, mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hRL] at hs
    exact hsum s hs
  · rwa [hRL]
  · intro x hx
    apply E1_dser_real
    intro pq
    have hp := E1_cpow_real (pq.1 : ℕ) (1 - x)
    have hq := E1_cpow_real (pq.2 : ℕ) (2 - x)
    simp only [ofReal_sub, ofReal_one, ofReal_ofNat] at hp hq
    simp only [WS, mul_im, inv_im, pow_two, mul_im, natCast_im, add_im,
      zero_add, add_zero, zero_mul, mul_zero, neg_zero, zero_div, hp, hq]
  · intro s hs c hc1 hc2
    have hs3 : 2 * s.re + 1 < 3 := by
      simpa [Aff.DL, twoOneL_app] using hs.2.2
    simp only [twoOneL_app] at hc2 ⊢
    exact (S_MB s c hc1 (by simpa using hc2) (by linarith) (by
      have hc : c < 2 * s.re := by simpa using hc2
      linarith)).2

end GoldbachBoundaries.Paper2.M4b
