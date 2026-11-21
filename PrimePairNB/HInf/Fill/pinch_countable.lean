import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! Proofs of `poleSetQ_countable`, `pinch_countable`, `generic_cocountable`, `countable_not_mem_Om`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `Σ` is countable. -/
theorem poleSetQ_countable : PoleSetQ.Countable := by
  have hz : NontrivialZeros.Countable :=
    (isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete
      isDiscrete_riemannZetaZeros).mono (fun _ h => h.1)
  have hc := (countable_singleton (1 : ℂ)).union
    ((countable_range (fun k : ℕ => 1 / (k : ℂ))).union
      (countable_iUnion fun n : ℕ => hz.image (fun ρ => ρ / (n : ℂ))))
  apply hc.mono
  rintro s ((hs | ⟨k, _, _, rfl⟩) | ⟨n, _, _, ρ, hρ, rfl⟩)
  · exact Or.inl hs
  · exact Or.inr (Or.inl ⟨k, rfl⟩)
  · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨n, ρ, hρ, rfl⟩))

/-- `Σ + Σ` is countable. -/
theorem pinch_countable : Pinch.Countable := by
  have h := (poleSetQ_countable.prod poleSetQ_countable).image (fun p : ℂ × ℂ => p.1 + p.2)
  refine h.mono ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- The slope of a nonzero real multiple of `slantDir κ`. -/
theorem slope_eq {x y : ℂ} (hne : x ≠ y) {κ t : ℝ} (h : x - y = (t : ℂ) * slantDir κ) :
    (x - y).im / (x - y).re = κ := by
  have hre : (x - y).re = t := by simpa [slantDir] using congrArg Complex.re h
  have him : (x - y).im = t * κ := by simpa [slantDir] using congrArg Complex.im h
  have ht : t ≠ 0 := by
    intro ht
    apply hne
    apply sub_eq_zero.mp
    apply Complex.ext
    · simpa [ht] using hre
    · simpa [ht] using him
  rw [hre, him]
  exact mul_div_cancel_left₀ κ ht

/-- Only countably many slopes fail to be generic.  -/
theorem generic_cocountable : {κ : ℝ | ¬ IsGenericSlope κ}.Countable := by
  let f : ℂ × ℂ → ℝ := fun p => (p.1 - p.2).im / (p.1 - p.2).re
  have hB : (f '' (PoleSetQ ×ˢ PoleSetQ) ∪ f '' (Pinch ×ˢ Pinch)).Countable :=
    ((poleSetQ_countable.prod poleSetQ_countable).image f).union
      ((pinch_countable.prod pinch_countable).image f)
  refine hB.mono ?_
  intro κ hκ
  simp only [mem_setOf_eq, IsGenericSlope, not_and_or, not_forall] at hκ
  rcases hκ with ⟨a, ha, a', ha', hne, t, he⟩ | ⟨x, hx, x', hx', hne, t, he⟩
  · left
    exact ⟨(a, a'), ⟨ha, ha'⟩, slope_eq hne (not_not.mp he)⟩
  · right
    exact ⟨(x, x'), ⟨hx, hx'⟩, slope_eq hne (not_not.mp he)⟩

/-- A point off `Σ + Σ` lies on the ray of a pinch for only countably many slopes. Each point of `𝒱_∞ ∖ X` lies in `Ω_θ` for almost every `θ`.  -/
theorem countable_not_mem_Om {top : EReal} {q : ℂ} (hq : q ∈ VInf top) (hqX : q ∉ Pinch) :
    {κ : ℝ | q ∉ Om κ top}.Countable := by
  have hB := (pinch_countable.image (fun x : ℂ => (x - q).im / (x - q).re))
  refine hB.mono ?_
  intro κ hκ
  simp only [mem_setOf_eq, Om, mem_diff, not_and, not_not, mem_iUnion] at hκ
  obtain ⟨x, hx, t, ht, hqx⟩ := hκ hq
  refine ⟨x, hx, ?_⟩
  have hne : x ≠ q := fun h => hqX (h ▸ hx)
  exact slope_eq hne (by rw [hqx]; ring)

end GoldbachBoundaries.HInf.Fill

