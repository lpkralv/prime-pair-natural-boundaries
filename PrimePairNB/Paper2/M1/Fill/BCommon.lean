import PrimePairNB.Paper2.M1.BNumbers

/-!
# Shared helpers for `BNumbers.lean` and the growth bound for `Q`

The family `t ↦ sSup {β : |γ| ≥ t}` whose infimum is `B_∞`, its basic bounds, finiteness of zeros of bounded
height, and a bound for `-ζ'/ζ` on `Re s ≥ x > 1`. All unconditional.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The family whose infimum is `B_∞`. -/
def binfFam (t : ℝ) : ℝ := sSup (re '' {ρ | ρ ∈ NontrivialZeros ∧ t ≤ |ρ.im|})

lemma Binf_eq_iInf : Binf = ⨅ t : ℝ, binfFam t := rfl

lemma re_image_bddAbove {s : Set ℂ} (hs : s ⊆ NontrivialZeros) : BddAbove (re '' s) :=
  ⟨1, by rintro _ ⟨ρ, hρ, rfl⟩; exact (hs hρ).2.2.le⟩

lemma re_image_nonempty_height (t : ℝ) :
    (re '' {ρ | ρ ∈ NontrivialZeros ∧ t ≤ |ρ.im|}).Nonempty := by
  obtain ⟨ρ, hρ, h⟩ := exists_nontrivialZero_im_gt |t|
  exact ⟨ρ.re, ρ, ⟨hρ, (le_abs_self t).trans (h.le.trans (le_abs_self _))⟩, rfl⟩

lemma nontrivialZeros_nonempty : NontrivialZeros.Nonempty := by
  obtain ⟨ρ, hρ, -⟩ := exists_nontrivialZero_im_gt 0
  exact ⟨ρ, hρ⟩

lemma binfFam_nonneg (t : ℝ) : 0 ≤ binfFam t :=
  Real.sSup_nonneg (by rintro _ ⟨ρ, hρ, rfl⟩; exact hρ.1.2.1.le)

lemma binfFam_bddBelow : BddBelow (range binfFam) :=
  ⟨0, by rintro _ ⟨t, rfl⟩; exact binfFam_nonneg t⟩

lemma Binf_nonneg : 0 ≤ Binf := le_ciInf binfFam_nonneg

lemma Binf_le_binfFam (t : ℝ) : Binf ≤ binfFam t := ciInf_le binfFam_bddBelow t

lemma re_le_binfFam {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) {t : ℝ} (ht : t ≤ |ρ.im|) : ρ.re ≤ binfFam t :=
  le_csSup (re_image_bddAbove fun _ h => h.1) ⟨ρ, ⟨hρ, ht⟩, rfl⟩

lemma exists_binfFam_lt {δ : ℝ} (hδ : 0 < δ) : ∃ t, binfFam t < Binf + δ :=
  (ciInf_lt_iff binfFam_bddBelow).1 (by rw [← Binf_eq_iInf]; linarith)

/-- Zeros of bounded height are finite. -/
lemma finite_zeros_abs_im_le (T : ℝ) : {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ T}.Finite := by
  refine ((isCompact_Icc.reProdIm isCompact_Icc :
    IsCompact ((Icc (0 : ℝ) 1) ×ℂ (Icc (-T) T))).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨hρ, h⟩
  rw [abs_le] at h
  refine ⟨?_, hρ.1⟩
  simp only [mem_reProdIm, mem_Icc]
  exact ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, h.1, h.2⟩

/-- No non-trivial zero is real (`ζ(x) ≠ 0` for `0 < x < 1`). -/
lemma im_ne_zero_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.im ≠ 0 := by
  intro h
  have hρ' : ρ = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp [h]
  apply riemannZeta_ne_zero_of_mem_Ioo (x := ρ.re) ⟨hρ.2.1, hρ.2.2⟩
  rw [← hρ']
  exact hρ.1

/-- `‖-ζ'/ζ(s)‖ ≤ ∑ Λ(m) m^{-x}` for `Re s ≥ x > 1` (as `norm_negLogDerivZeta_le` in
`SigmaMeromorphic.lean`). -/
lemma norm_negLogDerivZeta_le_of_re {x : ℝ} (hx : 1 < x) {s : ℂ} (hs : x ≤ s.re) :
    ‖negLogDerivZeta s‖ ≤ ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-x) := by
  rw [negLogDerivZeta_eq_LSeries (by linarith), LSeries]
  refine tsum_of_norm_bounded (summable_vonMangoldt_rpow hx).hasSum fun m => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hm
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    simp only [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg m)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith))
      ArithmeticFunction.vonMangoldt_nonneg

end GoldbachBoundaries.Paper2.M1
