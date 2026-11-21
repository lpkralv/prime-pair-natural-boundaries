import PrimePairNB.Paper2.M4a.Fill.segment_subset_Str
import PrimePairNB.ThmA.Fill.CCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace GroupB

theorem isOpen_domain (A : Aff) {U : Set ℂ} (hU : IsOpen U) :
    IsOpen {p : ℂ × ℂ | p.2 ∈ U ∧ p.1 ∈ A.Str p.2} := by
  exact (hU.preimage continuous_snd).inter
    ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt (Complex.continuous_re.comp continuous_fst)
        ((continuous_app_re A).comp continuous_snd)))

end GroupB
end GoldbachBoundaries.Paper2.M4a
