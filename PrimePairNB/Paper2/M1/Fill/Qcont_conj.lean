import PrimePairNB.Paper2.M1.QnoRH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Conjugation symmetry of `Qcont` off `Σ_Q` (no (Z1): termwise, `ζ(s̄) = conj ζ(s)` gives
`A(z̄) = conj A(z)`; or the identity theorem from `Re z > 1`). -/
theorem Qcont_conj {z : ℂ} (hz : z ∈ halfPlane 0 \ PoleSetQ) : Qcont (conj z) = conj (Qcont z) := by
  -- Same derivative-conjugation argument as PNT+ ZetaConj.lean.
  have hd : ∀ s : ℂ, deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
    intro s
    have h := congrFun (deriv_conj_conj (f := riemannZeta)) (conj s)
    simpa [Function.comp_def] using h
  unfold Qcont
  rw [Complex.conj_tsum]
  congr 1
  funext n
  have heq : (n : ℂ) * conj z = conj ((n : ℂ) * z) := by simp
  simp only [sigmaTerm]
  rw [heq]
  simp only [negLogDerivZeta, hd, riemannZeta_conj]
  simp

end GoldbachBoundaries.Paper2.M1
