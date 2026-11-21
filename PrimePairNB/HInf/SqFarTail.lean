import PrimePairNB.HInf.SqDefs
import PrimePairNB.HInf.SqMixArithmetic

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2
namespace GoldbachBoundaries.HInf.Fill

/-- The square kernel at a collision; symmetric in the two colliding poles. -/
lemma kSq_at_sum (a b : ℂ) : kSq a (a + b) = betaB (a / 2) (b / 2) / 2 := by
  have he : (a + b) / 2 - a / 2 = b / 2 := by ring
  have he' : (a + b) / 2 = a / 2 + b / 2 := by ring
  unfold kSq kerSq betaB
  rw [he, he']
  ring

def pairTermSq (p : ℂ × ℂ) : ℂ :=
  Rcoef p.1 * Rcoef p.2 * (betaB (p.1 / 2) (p.2 / 2) / 2)

theorem norm_far_term_Sq (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y → ∀ p ∈ pinchPairs (1 + v), p ≠ (1, v) →
      p ≠ (v, 1) → 2 * Y + 4 ≤ |p.1.im| →
        ‖Rcoef p.1 * Rcoef p.2 * (betaB (p.1 / 2) (p.2 / 2) / 2)‖ ≤
          C * (1 + |p.1.im|) ^ 4 * Real.exp (-((Real.pi / 2) * |p.1.im|)) := by
  have hε : 0 < 1 - Bsup := by linarith
  have hε1 : 1 - Bsup < 1 := by linarith [(Bsup_facts hZ1).2.1]
  obtain ⟨R, hR⟩ := norm_Rcoef_le_log hZ1 hZ2 hε hε1
  obtain ⟨G, hG⟩ := hZ6 ((1 - Bsup) / 2) (Bsup / 2) (by linarith) (by linarith [(Bsup_facts hZ1).2.1])
  have hK : IsCompact (Icc (1 / 2 : ℝ) 1 ×ℂ Icc (-Y) Y) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  let R' := max R 0
  let G' := max G 0
  let D' := max D 0
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hG0 : 0 ≤ G' := le_max_right _ _
  have hD0 : 0 ≤ D' := le_max_right _ _
  have hres (a : ℂ) (ha : a ∈ PoleSetQ) (haε : 1 - Bsup ≤ a.re) :
      ‖Rcoef a‖ ≤ R' * (|a.im| + 2) := by
    calc
      ‖Rcoef a‖ ≤ R * Real.log (|a.im| + 3) := hR a ha haε
      _ ≤ R' * Real.log (|a.im| + 3) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith [abs_nonneg a.im]))
      _ ≤ R' * (|a.im| + 2) := mul_le_mul_of_nonneg_left
        (by have := Real.log_le_sub_one_of_pos (show 0 < |a.im| + 3 by positivity); linarith) hR0
  have hgam (a : ℂ) (ha : a.re ∈ Icc (1 - Bsup) Bsup) :
      ‖Gamma (a / 2)‖ ≤ G' * (1 + |a.im|) * Real.exp (-(Real.pi * |a.im| / 4)) := by
    have hh := hG (a.re / 2) ⟨by linarith [ha.1], by linarith [ha.2]⟩ (a.im / 2)
    have he : ((a.re / 2 : ℝ) : ℂ) + ((a.im / 2 : ℝ) : ℂ) * I = a / 2 := by
      apply Complex.ext <;> simp
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    have hp : (1 + |a.im| / 2) ^ (Bsup / 2) ≤ 1 + |a.im| := by
      calc
        (1 + |a.im| / 2) ^ (Bsup / 2) ≤ 1 + |a.im| / 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + |a.im| / 2 by linarith [abs_nonneg a.im]) (show Bsup / 2 ≤ 1 by linarith)
        _ ≤ 1 + |a.im| := by linarith [abs_nonneg a.im]
    calc
      ‖Gamma (a / 2)‖ ≤ G * (1 + |a.im| / 2) ^ (Bsup / 2) * Real.exp (-(Real.pi * |a.im| / 4)) := by
        convert hh using 1
        congr 2
        ring
      _ ≤ G' * (1 + |a.im| / 2) ^ (Bsup / 2) * Real.exp (-(Real.pi * |a.im| / 4)) := by
        gcongr; exact le_max_left _ _
      _ ≤ G' * (1 + |a.im|) * Real.exp (-(Real.pi * |a.im| / 4)) := by gcongr
  refine ⟨R' ^ 2 * G' ^ 2 * D' * (Y + 2) ^ 4 * Real.exp (Real.pi * Y / 4), ?_⟩
  intro v hv hv1 hvY p hp hp1 hp2 ht
  have hm := pinchPairs_other_mem hZ1 hv hp hp1 hp2
  have ha := hres p.1 hm.1.1 hm.2.2.1.1.le
  have hb := hres p.2 hm.2.1.1 hm.2.2.2.1.le
  have hga := hgam p.1 ⟨hm.2.2.1.1.le, hm.2.2.1.2⟩
  have hgb := hgam p.2 ⟨hm.2.2.2.1.le, hm.2.2.2.2⟩
  have hsum : p.1.im + p.2.im = v.im := by
    simpa only [add_im, one_im, zero_add] using congrArg Complex.im hp.2.2
  have hbi : |p.2.im| ≤ |p.1.im| + Y := by
    have hh : p.2.im = v.im - p.1.im := by linarith
    rw [hh]
    have := abs_sub v.im p.1.im
    linarith
  have hreverse : |p.1.im| ≤ Y + |p.2.im| := by
    have hh : p.1.im = v.im - p.2.im := by linarith
    rw [hh]
    exact (abs_sub _ _).trans (by linarith)
  have hden : ‖(Gamma (p.1 / 2 + p.2 / 2))⁻¹‖ ≤ D' := by
    rw [show p.1 / 2 + p.2 / 2 = (1 + v) / 2 by rw [← hp.2.2]; ring]
    apply le_trans (hD ((1 + v) / 2) ?_) (le_max_left _ _)
    change ((1 + v) / 2).re ∈ Icc (1 / 2) 1 ∧ ((1 + v) / 2).im ∈ Icc (-Y) Y
    constructor
    · simp only [mem_Icc, div_ofNat_re, add_re, one_re]
      constructor <;> linarith
    · simp only [mem_Icc, div_ofNat_im, add_im, one_im, zero_add]
      constructor <;> linarith [(abs_le.mp hvY).1, (abs_le.mp hvY).2]
  let U := (Y + 2) * (1 + |p.1.im|)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have haU : |p.1.im| + 2 ≤ U := by dsimp [U]; nlinarith [abs_nonneg p.1.im]
  have hbU : |p.2.im| + 2 ≤ U := by dsimp [U]; nlinarith [abs_nonneg p.1.im]
  have hgaU : 1 + |p.1.im| ≤ U := by linarith
  have hgbU : 1 + |p.2.im| ≤ U := by linarith
  have he : Real.exp (-(Real.pi * |p.1.im| / 4)) * Real.exp (-(Real.pi * |p.2.im| / 4)) ≤
      Real.exp (Real.pi * Y / 4) * Real.exp (-((Real.pi / 2) * |p.1.im|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hhalf : ‖Rcoef p.1 * Rcoef p.2 * (betaB (p.1 / 2) (p.2 / 2) / 2)‖ ≤
      ‖Rcoef p.1 * Rcoef p.2 * betaB (p.1 / 2) (p.2 / 2)‖ := by
    rw [← mul_div_assoc, norm_div, norm_ofNat]
    linarith [norm_nonneg (Rcoef p.1 * Rcoef p.2 * betaB (p.1 / 2) (p.2 / 2))]
  apply hhalf.trans
  rw [betaB, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    ‖Rcoef p.1‖ * ‖Rcoef p.2‖ * (‖Gamma (p.1 / 2)‖ * ‖Gamma (p.2 / 2)‖ * ‖(Gamma (p.1 / 2 + p.2 / 2))⁻¹‖)
      ≤ (R' * U) * (R' * U) *
          ((G' * U * Real.exp (-(Real.pi * |p.1.im| / 4))) *
           (G' * U * Real.exp (-(Real.pi * |p.2.im| / 4))) * D') := by
        gcongr
        · exact ha.trans (mul_le_mul_of_nonneg_left haU hR0)
        · exact hb.trans (mul_le_mul_of_nonneg_left hbU hR0)
        · exact hga.trans (by gcongr)
        · exact hgb.trans (by gcongr)
    _ = (R' ^ 2 * G' ^ 2 * D' * U ^ 4) *
        (Real.exp (-(Real.pi * |p.1.im| / 4)) * Real.exp (-(Real.pi * |p.2.im| / 4))) := by ring
    _ ≤ (R' ^ 2 * G' ^ 2 * D' * U ^ 4) *
        (Real.exp (Real.pi * Y / 4) * Real.exp (-((Real.pi / 2) * |p.1.im|))) := by gcongr
    _ = _ := by dsimp [U]; ring

theorem far_tail_Sq (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ,
      0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖pairTermSq p.1‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖pairTermSq p.1‖ ≤ Real.exp (-H) :=
  sqMix_far_tail hZ1 hZ2 hB hY pairTermSq (norm_far_term_Sq hZ1 hZ2 hZ6 hB hY)

end GoldbachBoundaries.HInf.Fill
