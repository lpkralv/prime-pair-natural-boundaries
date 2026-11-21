import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Every point of `σ > 2B_∞` lies in the region of some admissible `(δ, c)`, when `B_∞ < 1` (Z1): take
`δ < (1 - B_∞)/2` with `2B_∞ + 4δ < σ`, and `c ∈ (B_∞ + 2δ, min(1, σ - B_∞ - 2δ))` avoiding the finitely many values
`Re a`, `σ - Re a` (`a ∈ F_δ`). Uses: `Fdelta_spec`. -/
theorem exists_adm_reg (hZ1 : Z1) (hB : Binf < 1) {s : ℂ} (hs : 2 * Binf < s.re) :
    ∃ δ c : ℝ, AdmC δ c ∧ s ∈ RegC δ c := by
  let δ : ℝ := min ((1 - Binf) / 4) ((s.re - 2 * Binf) / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hd1 : δ ≤ (1 - Binf) / 4 := min_le_left _ _
  have hd2 : δ ≤ (s.re - 2 * Binf) / 8 := min_le_right _ _
  have hf := (Fdelta_spec hZ1 δ hδ).1
  let bad : Set ℝ := (Complex.re '' Fdelta δ) ∪ ((fun a : ℂ => s.re - a.re) '' Fdelta δ)
  have hbad : bad.Finite := (hf.image _).union (hf.image _)
  have hi : Binf + 2 * δ < min 1 (s.re - Binf - 2 * δ) :=
    lt_min (by linarith) (by linarith)
  obtain ⟨c, hc, hcn⟩ := (Set.Ioo_infinite hi).exists_notMem_finite hbad
  refine ⟨δ, c, ⟨hδ, by linarith, hc.1, lt_of_lt_of_le hc.2 (min_le_left _ _), ?_⟩, ?_⟩
  · intro a ha he
    exact hcn (Or.inl ⟨a, ha, he.symm⟩)
  · refine ⟨?_, ?_⟩
    · have := lt_of_lt_of_le hc.2 (min_le_right _ _)
      linarith
    · intro a ha he
      exact hcn (Or.inr ⟨a, ha, by linarith⟩)

end GoldbachBoundaries.Paper2.M1
