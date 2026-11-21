import PrimePairNB.HInf.SqDefs
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf.Fill

lemma twoL_app_eq (s : ℂ) : Aff.twoL.app s = 2 * s := by simp [Aff.app, Aff.twoL]

lemma twoL_HL : Aff.twoL.HL = halfPlane (1 / 2) := by
  ext s
  simp only [Aff.HL, twoL_app_eq, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
    halfPlane, mem_ofPred_eq]
  constructor <;> intro h <;> linarith

lemma twoL_RL : Aff.twoL.RL = halfPlane 1 := by
  ext s
  simp only [Aff.RL, twoL_app_eq, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
    halfPlane, mem_ofPred_eq]
  constructor <;> intro h <;> linarith

lemma mem_catSq_iff {s : ℂ} : s ∈ catSq ↔ 1 / 2 < s.re ∧ 2 * s ∈ Pinch := by
  simp only [catSq, catalogueL, twoL_HL, twoL_app_eq, halfPlane, mem_ofPred_eq]

lemma SqSer_analyticAt {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ SqSer s := by
  have h := M4b.hypR_kerSq.2.1
  rw [twoL_RL] at h
  exact h.analyticAt ((isOpen_halfPlane 1).mem_nhds hs)

lemma DSq_analyticAt {v : ℂ} (hv : 2 < v.re) : AnalyticAt ℂ DSq v := by
  have h : AnalyticAt ℂ SqSer (v / 2) := SqSer_analyticAt (by simp; linarith)
  exact AnalyticAt.comp (g := SqSer) (f := fun v : ℂ => v / 2) h (by fun_prop)

end GoldbachBoundaries.HInf.Fill
