import PrimePairNB.HInf.Branch
import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.differentiableOn_graphInt
import PrimePairNB.HInf.Fill.exists_trapezoid_graph
import PrimePairNB.HInf.Fill.graphInt_eq_of_homotopy
import PrimePairNB.HInf.Fill.graphInt_line
import PrimePairNB.HInf.Fill.absc_lt_iff_re_lt
import PrimePairNB.HInf.Fill.exists_separating_iff
import PrimePairNB.HInf.Fill.interpPt_mem_of_separating
import PrimePairNB.HInf.Fill.isSeparating_eventually
import PrimePairNB.HInf.Fill.isSeparating_line

/-!
# HInf: separating graphs

A separating graph for `v` exists exactly when `v` lies off every cut.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- **Paper, Lemma 5.2.** A separating `κ`-graph for `v ∈ 𝒱_∞` exists iff `v ∈ Ω_θ`.
No genericity. The "if" direction is the tent construction. -/
theorem exists_separating_iff (hZ1 : Z1) {κ : ℝ} {top : EReal} {v : ℂ} (hv : v ∈ VInf top) :
    (∃ Γ : SlantGraph κ, IsSeparating v Γ) ↔ v ∈ Om κ top :=
  @Fill.exists_separating_iff hZ1 κ top v hv

end GoldbachBoundaries.HInf
