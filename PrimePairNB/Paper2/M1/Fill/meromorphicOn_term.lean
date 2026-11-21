import PrimePairNB.Paper2.M1.Fill.E2Common

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Each term `R_a K_s(a) Qc(s - a)` is meromorphic on `σ > Re a` (`K_s(a) = Γ(a)Γ(s - a)/Γ(s)` is holomorphic there,
`Qc` is meromorphic on `Re z > 0`). -/
theorem meromorphicOn_term {Qc : ℂ → ℂ} (hQc : IsQCont Qc) {a : ℂ} (ha : a ∈ PoleSetQ) :
    MeromorphicOn (fun s => Rcoef a * KerS s a * Qc (s - a)) (halfPlane a.re) := by
  intro s hs
  have hQ : MeromorphicAt (fun z => Qc (z - a)) s :=
    (hQc.1 (s - a) (by show 0 < (s - a).re; simp only [sub_re]; exact sub_pos.mpr hs)).comp_analyticAt (g := fun z : ℂ => z - a)
      (analyticAt_id.sub analyticAt_const)
  exact ((analyticAt_const.fun_mul (E2_analytic_KerS hs)).meromorphicAt).mul hQ

end GoldbachBoundaries.Paper2.M1
