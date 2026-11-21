import PrimePairNB.Paper2.M4a.Defs
import PrimePairNB.SigmaFinite
import PrimePairNB.Density

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The segment lies in the strip** (no RH, no hypothesis on `k`). For `s ∈ ℍ_L`: `0 < Re a ≤ 1 < Re L(s)` and
`0 < Re L(s) - 1 ≤ Re(L(s) - b) < Re L(s)` (`poleSetQ_re_bounds` for `a` and `b`); `Str(s)` is convex
(intersection of two open half-planes in `Re`), so `segment ℝ a (L(s) - b) ⊆ Str(s)` (`Convex.segment_subset`). -/
theorem segment_subset_Str (A : Aff) {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) {s : ℂ} (hs : s ∈ A.HL) :
    segment ℝ a (A.app s - b) ⊆ A.Str s := by
  have ha0 := (poleSetQ_re_bounds ha).1
  have ha1 := (poleSetQ_re_bounds ha).2.1
  have hb0 := (poleSetQ_re_bounds hb).1
  have hb1 := (poleSetQ_re_bounds hb).2.1
  change 1 < (A.app s).re at hs
  rw [segment_eq_image']
  rintro z ⟨t, ht, rfl⟩
  change 0 < (a + t • (A.app s - b - a)).re ∧
    (a + t • (A.app s - b - a)).re < (A.app s).re
  simp only [add_re, sub_re, smul_re, smul_eq_mul]
  constructor
  · have h0 := mul_nonneg ht.1 (sub_pos.mpr (lt_of_le_of_lt hb1 hs)).le
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) ha0.le
    by_cases ht0 : t = 0
    · simp [ht0, ha0]
    · have h2 := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0))
        (sub_pos.mpr (lt_of_le_of_lt hb1 hs))
      nlinarith
  · have h0 := mul_nonneg ht.1 hb0.le
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr (lt_of_le_of_lt ha1 hs)).le
    by_cases ht1 : t = 1
    · simp only [ht1, one_mul]; linarith
    · have h2 := mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1))
        (sub_pos.mpr (lt_of_le_of_lt ha1 hs))
      nlinarith

end GoldbachBoundaries.Paper2.M4a
