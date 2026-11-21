import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-!
# `exists_admS`

`S` is holomorphic on `σ > 1/2` (`M4b.hypR_kerS`), and the catalogue has `σ ≤ 1/2` (`re_le_two_of_mem_pinch`). The helpers
here are used by the other `S` files of this group.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

lemma twoOneL_app_eq (s : ℂ) : Aff.twoOneL.app s = 2 * s + 1 := by
  simp [Aff.app, Aff.twoOneL]

lemma re_twoOneL_app (s : ℂ) : (Aff.twoOneL.app s).re = 2 * s.re + 1 := by
  simp [twoOneL_app_eq]

lemma mem_catS_iff {s : ℂ} : s ∈ catS ↔ 0 < s.re ∧ 2 * s + 1 ∈ Pinch := by
  have e : (2 * s + 1).re = 2 * s.re + 1 := by simp
  simp only [catS, catalogueL, Aff.HL, mem_ofPred_eq, twoOneL_app_eq, e]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, h2⟩

/-- The catalogue of `S` has `σ ≤ 1/2`. -/
lemma re_le_half_of_mem_catS {s : ℂ} (hs : s ∈ catS) : s.re ≤ 1 / 2 := by
  have h := re_le_two_of_mem_pinch (mem_catS_iff.mp hs).2
  have e : (2 * s + 1).re = 2 * s.re + 1 := by simp
  rw [e] at h
  linarith

/-- `S` is holomorphic on `σ > 1/2`. -/
lemma Sser_analyticAt {s : ℂ} (hs : 1 / 2 < s.re) : AnalyticAt ℂ Sser s := by
  have hopen : IsOpen Aff.twoOneL.RL := by
    have : Aff.twoOneL.RL = {s : ℂ | 1 / 2 < s.re} := by
      ext z
      simp only [Aff.RL, mem_ofPred_eq, re_twoOneL_app]
      constructor <;> intro h <;> linarith
    rw [this]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hmem : s ∈ Aff.twoOneL.RL := by
    simp only [Aff.RL, mem_ofPred_eq, re_twoOneL_app]
    linarith
  exact M4b.hypR_kerS.2.1.analyticAt (hopen.mem_nhds hmem)

/-- `S` itself is an admissible germ at `2`. -/
theorem exists_admS : AdmS Sser 2 := by
  have h2 : (1 / 2 : ℝ) < (2 : ℂ).re := by norm_num
  have hmem : (2 : ℂ) ∈ halfPlane 0 \ catS := by
    refine ⟨show (0 : ℝ) < (2 : ℂ).re by norm_num, fun hc => ?_⟩
    have := re_le_half_of_mem_catS hc
    norm_num at this
  exact ⟨ContinuousMap.const _ 2, fun _ => hmem, show (1 : ℝ) < (2 : ℂ).re by norm_num, rfl,
    ThmA.isTerminalGerm_of_analyticAt (fun _ => Sser_analyticAt h2) EventuallyEq.rfl⟩

end GoldbachBoundaries.HInf.Fill

