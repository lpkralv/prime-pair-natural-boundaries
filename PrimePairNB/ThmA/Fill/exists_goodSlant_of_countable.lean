import PrimePairNB.ThmA.G14_Geometry
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

/-- Excluding a countable set of slopes (general).

Sketch. For `α ≠ α'` in `S`, `α - α' = t(1 + iκ)` forces `t = Re(α - α')`; if that is `0` then
`α = α'`; otherwise `κ = Im(α-α')/Re(α-α')`. So the bad slopes are the image of the countable
`S ×ˢ S`; `Ioo (-1) 1 \ {0}` is uncountable (`Cardinal.mk_Ioo_real` or `Set.Countable.dense_compl`),
so some `κ` avoids them. -/
theorem exists_goodSlant_of_countable {S : Set ℂ} (hS : S.Countable) :
    ∃ κ : ℝ, κ ≠ 0 ∧ |κ| < 1 ∧
      ∀ α ∈ S, ∀ α' ∈ S, α ≠ α' → ∀ t : ℝ, α - α' ≠ (t : ℂ) * slantDir κ := by
  let B : Set ℝ := {0} ∪ (fun p : ℂ × ℂ => (p.1 - p.2).im / (p.1 - p.2).re) '' (S ×ˢ S)
  have hB : B.Countable := (countable_singleton _).union ((hS.prod hS).image _)
  obtain ⟨κ, hκ, hκB⟩ := (hB.dense_compl ℝ).inter_open_nonempty
    (Ioo (-1 : ℝ) 1) isOpen_Ioo ⟨0, by norm_num⟩
  refine ⟨κ, ?_, abs_lt.mpr hκ, ?_⟩
  · intro h
    exact hκB (Or.inl (mem_singleton_iff.mpr h))
  · intro α hα α' hα' hne t he
    have hre : (α - α').re = t := by
      simpa [slantDir] using congrArg Complex.re he
    have him : (α - α').im = t * κ := by
      simpa [slantDir] using congrArg Complex.im he
    have ht : t ≠ 0 := by
      intro ht
      apply hne
      apply sub_eq_zero.mp
      apply Complex.ext
      · simpa [ht] using hre
      · simpa [ht] using him
    apply hκB
    right
    refine ⟨(α, α'), ⟨hα, hα'⟩, ?_⟩
    change (α - α').im / (α - α').re = κ
    rw [hre, him]
    exact mul_div_cancel_left₀ κ ht

end GoldbachBoundaries.ThmA
