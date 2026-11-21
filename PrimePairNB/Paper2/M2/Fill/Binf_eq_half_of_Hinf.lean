import PrimePairNB.Paper2.M2.Lambda

/-! `Binf_eq_half_of_Hinf`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`(H_∞)` gives `B_∞ = 1/2`** (Z1). `≥`: `half_le_Binf`. `≤`: for `δ > 0` the zeros with `β > 1/2 + δ` are
finitely many (`hH`); take `t` above all their `|γ|`. Then every zero with `|γ| ≥ t` has `β ≤ 1/2 + δ`, so the
`t`-th supremum is `≤ 1/2 + δ`, and `B_∞ ≤ 1/2 + δ`. -/
theorem Binf_eq_half_of_Hinf (hZ1 : Z1) (hH : Hinf) : Binf = 1 / 2 := by
  refine le_antisymm ?_ (half_le_Binf hZ1)
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have hfin := hH (δ / 2) (by linarith)
  obtain ⟨T, hT⟩ := (hfin.image fun ρ : ℂ => |ρ.im|).bddAbove
  have hle : binfFam (T + 1) ≤ 1 / 2 + δ / 2 := by
    refine csSup_le (re_image_nonempty_height _) ?_
    rintro _ ⟨ρ, ⟨hρ, ht⟩, rfl⟩
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have := hT ⟨ρ, ⟨hρ, hcon⟩, rfl⟩
    linarith
  linarith [Binf_le_binfFam (T + 1)]

end GoldbachBoundaries.Paper2.M2
