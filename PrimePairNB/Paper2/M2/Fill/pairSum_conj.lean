import PrimePairNB.Paper2.M2.Far

/-! `pairSum_conj` (`Lambda.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillF

/-- Conjugation of pairs maps `pinchPairs s` onto `pinchPairs (conj s)`. -/
lemma conj_mem_pinchPairs {s : ℂ} {p : ℂ × ℂ} (hp : p ∈ pinchPairs s) :
    (conj p.1, conj p.2) ∈ pinchPairs (conj s) :=
  ⟨conj_mem_poleSetQ hp.1, conj_mem_poleSetQ hp.2.1, by rw [← map_add, hp.2.2]⟩

/-- The bijection `(a, b) ↦ (ā, b̄)` from `pinchPairs s` to `pinchPairs (conj s)`. -/
def pinchPairsConj (s : ℂ) : pinchPairs s ≃ pinchPairs (conj s) where
  toFun p := ⟨(conj p.1.1, conj p.1.2), conj_mem_pinchPairs p.2⟩
  invFun p := ⟨(conj p.1.1, conj p.1.2), by
    have := conj_mem_pinchPairs p.2
    simpa using this⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

end FillF

open FillF in
/-- **Conjugation symmetry of the pair sum** (Z1). -/
theorem pairSum_conj (hZ1 : Z1) (s : ℂ) : pairSum (conj s) = conj (pairSum s) := by
  unfold pairSum
  rw [← (pinchPairsConj s).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun p => ?_
  have ha := Rcoef_real_conj hZ1 p.2.1
  have hb := Rcoef_real_conj hZ1 p.2.2.1
  have hra : conj (Rcoef p.1.1) = Rcoef p.1.1 := Complex.conj_eq_iff_im.mpr ha.1
  have hrb : conj (Rcoef p.1.2) = Rcoef p.1.2 := Complex.conj_eq_iff_im.mpr hb.1
  show Rcoef (conj p.1.1) * Rcoef (conj p.1.2) * betaB (conj p.1.1) (conj p.1.2) = _
  rw [ha.2, hb.2, betaB, betaB, ← map_add, Complex.Gamma_conj, Complex.Gamma_conj, Complex.Gamma_conj,
    map_mul, map_mul, map_div₀, map_mul, hra, hrb]

end GoldbachBoundaries.Paper2.M2
