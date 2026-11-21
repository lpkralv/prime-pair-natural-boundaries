import PrimePairNB.HInf.Sheet
import PrimePairNB.HInf.Fill.arc_model
import PrimePairNB.HInf.Fill.exists_arc
import PrimePairNB.HInf.Fill.exists_glued_graph
import PrimePairNB.HInf.Fill.exists_outer_contour
import PrimePairNB.HInf.Fill.graphInt_eq_outer_add_arcs
import PrimePairNB.HInf.Fill.local_model

/-!
# HInf: the local model at every catalogue point

`arc_model` is the pinch computation on a small disc, with no zeta and no contour outside the disc. `exists_outer_contour`
is the outer contour. `local_model` assembles them.

An arc is a graph over `Im t` in `t = (z - a) / slantDir κ`, on `|Im t| ≤ r₀`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- **Paper, Theorem 6.1.** At `x ∈ X`, for generic `κ`, with any finite number of colliding pairs:
`D^θ(v) = Log_θ(v - x) X_x(v) + H(v)` on the slit disc, `H` holomorphic on the disc. Its proof applies `exists_outer_contour`
with `R` as described there, then `exists_glued_graph`, `graphInt_eq_outer_add_arcs`, `arc_model`. The parameter `R` of
`exists_outer_contour` is internal to the proof. -/
theorem local_model (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {κ : ℝ} (hκ : IsGenericSlope κ) {x : ℂ} (hx : x ∈ Xcat) (hxV : x ∈ Vt top) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ VInf top ∧ ball x r \ rayW κ x ⊆ Om κ top ∧
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball x r) ∧
        ∀ v ∈ ball x r \ rayW κ x, Dth k κ v = logK κ (v - x) * Xc k x v + H v :=
  @Fill.local_model hZ1 hZ2 hZ3 k top D hK κ hκ x hx hxV

end GoldbachBoundaries.HInf
