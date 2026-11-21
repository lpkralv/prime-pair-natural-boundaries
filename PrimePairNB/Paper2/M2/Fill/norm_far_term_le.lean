import PrimePairNB.Paper2.M2.Single
import PrimePairNB.ThmA.Fill.germ_unique
import PrimePairNB.Paper2.M2.Fill.pinchPairs_other_mem

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Size of one far term** (Z1, Z2, Z6, `B < 1`). With `ε = 1 - B ∈ (0, 1)` (`B ≥ 1/2` by `Bsup_facts`):
`|R_a| ≤ C log(|t| + 3)`, `|R_b| ≤ C log(|t| + Y + 3)` (`norm_Rcoef_le_log`, `Re a, Re b > 1 - B`,
`|Im b| = |Im v - t| ≤ |t| + Y`); (Z6) on `[1 - B, B]`: `|Γ(a)| ≤ C'(1 + |t|) e^{-π|t|/2}`,
`|Γ(b)| ≤ C'(1 + |t| + Y) e^{-π(|t| - Y)/2}` (`B ≤ 1`, `|Im b| ≥ |t| - Y ≥ 0` for `|t| ≥ 2Y`);
`1/|Γ(1 + v)| ≤ C_Y` (`Complex.differentiable_one_div_Gamma`, continuity on the compact rectangle
`[1, 2] × [-Y, Y]`). Logs are `≤ 1 + |t| + Y`, and `1 + |t| + Y ≤ (1 + Y)(1 + |t|)`. -/
theorem norm_far_term_le (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    ∃ C : ℝ, ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y → ∀ p ∈ pinchPairs (1 + v), p ≠ (1, v) →
      p ≠ (v, 1) → 2 * Y ≤ |p.1.im| →
        ‖Rcoef p.1 * Rcoef p.2 * betaB p.1 p.2‖ ≤
          C * (1 + |p.1.im|) ^ 4 * Real.exp (-(Real.pi * |p.1.im|)) := by
  have hε : 0 < 1 - Bsup := by linarith
  have hε1 : 1 - Bsup < 1 := by linarith [(Bsup_facts hZ1).2.1]
  obtain ⟨R, hR⟩ := norm_Rcoef_le_log hZ1 hZ2 hε hε1
  obtain ⟨G, hG⟩ := hZ6 (1 - Bsup) Bsup hε (by linarith [(Bsup_facts hZ1).2.1])
  have hK : IsCompact (Icc (1 : ℝ) 2 ×ℂ Icc (-Y) Y) := isCompact_Icc.reProdIm isCompact_Icc
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
      ‖Gamma a‖ ≤ G' * (1 + |a.im|) * Real.exp (-(Real.pi * |a.im| / 2)) := by
    have hh := hG a.re ha a.im
    rw [Complex.re_add_im] at hh
    have hp : (1 + |a.im|) ^ Bsup ≤ 1 + |a.im| := by
      simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1 + |a.im| by linarith [abs_nonneg a.im]) hB.le
    calc
      ‖Gamma a‖ ≤ G * (1 + |a.im|) ^ Bsup * Real.exp (-(Real.pi * |a.im| / 2)) := hh
      _ ≤ G' * (1 + |a.im|) ^ Bsup * Real.exp (-(Real.pi * |a.im| / 2)) := by
        gcongr; exact le_max_left _ _
      _ ≤ G' * (1 + |a.im|) * Real.exp (-(Real.pi * |a.im| / 2)) := by gcongr
  refine ⟨R' ^ 2 * G' ^ 2 * D' * (Y + 2) ^ 4 * Real.exp (Real.pi * Y / 2), ?_⟩
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
  have hden : ‖(Gamma (p.1 + p.2))⁻¹‖ ≤ D' := by
    rw [hp.2.2]
    apply le_trans (hD (1 + v) ?_) (le_max_left _ _)
    change (1 + v).re ∈ Icc 1 2 ∧ (1 + v).im ∈ Icc (-Y) Y
    constructor
    · simp only [mem_Icc, add_re, one_re]
      constructor <;> linarith
    · simpa only [add_im, one_im, zero_add, mem_Icc] using abs_le.mp hvY
  let U := (Y + 2) * (1 + |p.1.im|)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have haU : |p.1.im| + 2 ≤ U := by dsimp [U]; nlinarith [abs_nonneg p.1.im]
  have hbU : |p.2.im| + 2 ≤ U := by dsimp [U]; nlinarith [abs_nonneg p.1.im]
  have hgaU : 1 + |p.1.im| ≤ U := by linarith
  have hgbU : 1 + |p.2.im| ≤ U := by linarith
  have he : Real.exp (-(Real.pi * |p.1.im| / 2)) * Real.exp (-(Real.pi * |p.2.im| / 2)) ≤
      Real.exp (Real.pi * Y / 2) * Real.exp (-(Real.pi * |p.1.im|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  rw [betaB, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    ‖Rcoef p.1‖ * ‖Rcoef p.2‖ * (‖Gamma p.1‖ * ‖Gamma p.2‖ * ‖(Gamma (p.1 + p.2))⁻¹‖)
      ≤ (R' * U) * (R' * U) *
          ((G' * U * Real.exp (-(Real.pi * |p.1.im| / 2))) *
           (G' * U * Real.exp (-(Real.pi * |p.2.im| / 2))) * D') := by
        gcongr
        · exact ha.trans (mul_le_mul_of_nonneg_left haU hR0)
        · exact hb.trans (mul_le_mul_of_nonneg_left hbU hR0)
        · exact hga.trans (by gcongr)
        · exact hgb.trans (by gcongr)
    _ = (R' ^ 2 * G' ^ 2 * D' * U ^ 4) *
        (Real.exp (-(Real.pi * |p.1.im| / 2)) * Real.exp (-(Real.pi * |p.2.im| / 2))) := by ring
    _ ≤ (R' ^ 2 * G' ^ 2 * D' * U ^ 4) *
        (Real.exp (Real.pi * Y / 2) * Real.exp (-(Real.pi * |p.1.im|))) := by gcongr
    _ = _ := by dsimp [U]; ring

end GoldbachBoundaries.Paper2.M2
