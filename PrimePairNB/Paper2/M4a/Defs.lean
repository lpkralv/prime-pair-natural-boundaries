import PrimePairNB.Paper2.M1.Skeleton

/-!
# The kernel class (Section 4): definitions and small facts

The class data of Section 4 are an affine map `A : Aff` (`L(s) = ℓ s + ℓ₀`) and a kernel `k` (`k z s` is the
paper's `k(z, s)`). This file needs only the facts about `Σ_Q` and `R_a` without RH (`M1`) and the RH development
(the local finiteness and density lemmas for `Σ`, the catalogue lemmas, the parametric integral lemma of `ThmA`), so it imports
`Paper2.M1.Skeleton`. Nothing imports `Paper2/Statements.lean`.

-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## The affine map and its regions -/

lemma continuous_app_re (A : Aff) : Continuous fun s => (A.app s).re := by
  unfold Aff.app; fun_prop

lemma isOpen_DL (A : Aff) : IsOpen A.DL :=
  (isOpen_lt continuous_const (continuous_app_re A)).inter (isOpen_lt (continuous_app_re A) continuous_const)

lemma app_idL (s : ℂ) : Aff.idL.app s = s := by simp [Aff.app, Aff.idL]

end GoldbachBoundaries.Paper2.M4a
