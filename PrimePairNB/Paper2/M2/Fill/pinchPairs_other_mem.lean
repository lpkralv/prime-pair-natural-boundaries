import PrimePairNB.Paper2.M2.Single
import PrimePairNB.ThmA.Fill.germ_unique

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The competing pairs** (Z1; first sentence of Paper, Lemma 3.4, which needs neither `B < 1` nor `Re v ≤ 1`). If
`p.1 = 1` then `p.2 = v` and `p = (1, v)`; if `p.2 = 1` then `p = (v, 1)`. So `p.1, p.2 ∈ Σ_Q ∖ {1}`, hence
`Re ≤ B` (`poleSetQ_re_le_Bsup`), and `Re p.1 = 1 + Re v - Re p.2 ≥ 1 + Re v - B > 1 - B`, likewise for `p.2`. -/
theorem pinchPairs_other_mem (hZ1 : Z1) {v : ℂ} (hv : 0 < v.re) {p : ℂ × ℂ} (hp : p ∈ pinchPairs (1 + v))
    (h1 : p ≠ (1, v)) (h2 : p ≠ (v, 1)) :
    p.1 ∈ PoleSetQ \ {1} ∧ p.2 ∈ PoleSetQ \ {1} ∧
      p.1.re ∈ Ioc (1 - Bsup) Bsup ∧ p.2.re ∈ Ioc (1 - Bsup) Bsup := by
  rcases p with ⟨a, b⟩
  rcases hp with ⟨ha, hb, hab⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply h1
    have hb' : b = v := by simpa [h] using hab
    exact Prod.ext h hb'
  have hb1 : b ≠ 1 := by
    intro h
    apply h2
    have ha' : a = v := by simpa [h, add_comm] using hab
    exact Prod.ext ha' h
  have haB := poleSetQ_re_le_Bsup hZ1 ha ha1
  have hbB := poleSetQ_re_le_Bsup hZ1 hb hb1
  have hre : a.re + b.re = 1 + v.re := by
    simpa only [add_re, one_re] using congrArg Complex.re hab
  exact ⟨⟨ha, ha1⟩, ⟨hb, hb1⟩, ⟨by linarith, haB⟩, ⟨by linarith, hbB⟩⟩

end GoldbachBoundaries.Paper2.M2
