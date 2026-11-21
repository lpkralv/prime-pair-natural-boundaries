import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec

/-!
# `pinchPairs_finite`

With `δ = (Re s₀ - 2B_∞)/4 > 0`, every ordered pair `(a, b) ∈ Σ_Q²` with `a + b = s₀` has a member of real part
`> B_∞ + δ`, i.e. in the finite `F_δ` (`Fdelta_spec`), and that member determines the pair.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Finitely many ordered pairs `(a, b) ∈ Σ_Q²` have `a + b = s₀` when `Re s₀ > 2B_∞` (Z1): one of `a, b` lies in the
finite `F_δ` (`2B_∞ + 4δ < Re s₀`) and determines the pair; if `B_∞ = 1` there are none (`Re a, Re b ≤ 1`).
Uses: `Fdelta_spec`, `poleSetQ_re_bounds`, `Binf_le_Bsup_le_one`. -/
theorem pinchPairs_finite (hZ1 : Z1) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    (pinchPairs s₀).Finite := by
  set δ : ℝ := (s₀.re - 2 * Binf) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hF := (Fdelta_spec hZ1 δ hδ).1
  refine ((hF.image fun x => (x, s₀ - x)).union (hF.image fun x => (s₀ - x, x))).subset ?_
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  simp only at ha hb hab
  have hre : a.re + b.re = s₀.re := by rw [← hab]; simp
  by_cases haF : Binf + δ < a.re
  · left
    exact ⟨a, ⟨ha, haF⟩, by simp [← hab]⟩
  · right
    have hbF : Binf + δ < b.re := by
      push Not at haF
      rw [hδdef] at haF ⊢
      linarith
    exact ⟨b, ⟨hb, hbF⟩, by simp [← hab]⟩

end GoldbachBoundaries.Paper2.M1
