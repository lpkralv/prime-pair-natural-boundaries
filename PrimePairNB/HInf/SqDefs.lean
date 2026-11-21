import PrimePairNB.HInf.Defs

/-! Prime-square series and the pinch coordinate `v = 2s`. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

abbrev SqSer : ℂ → ℂ := Dser WSq
def kSq (z v : ℂ) : ℂ := kerSq z (v / 2)
def DSq (v : ℂ) : ℂ := SqSer (v / 2)
abbrev catSq : Set ℂ := catalogueL Aff.twoL
def AdmSq (g : ℂ → ℂ) (s₁ : ℂ) : Prop :=
  IsAdmissibleGermOn SqSer (Aff.twoL.HL \ catSq) Aff.twoL.RL g s₁

def pairSumSq (x : ℂ) : ℂ :=
  ∑' p : pinchPairs x, Rcoef p.1.1 * Rcoef p.1.2 * kSq p.1.1 x

end GoldbachBoundaries.HInf
