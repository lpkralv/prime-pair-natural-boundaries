import PrimePairNB.Paper2.M2.Rigidity

/-! `singlePairs_injOn` of `Paper2/M2/Single.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Part (c): `u` determines the pair** (unconditional). `Re(ρ/q) = 1/(2q)` determines `q`, and then
`ρ = q · u`. -/
theorem singlePairs_injOn (A₀ y ε X : ℝ) :
    InjOn (fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) (singlePairs A₀ y ε X) := by
  rintro ⟨ρ₁, q₁⟩ h₁ ⟨ρ₂, q₂⟩ h₂ h
  simp only at h
  have hq₁ : (0 : ℝ) < q₁ := by exact_mod_cast h₁.2.2.2.2.1.pos
  have hq₂ : (0 : ℝ) < q₂ := by exact_mod_cast h₂.2.2.2.2.1.pos
  have hre := congrArg Complex.re h
  simp only [Complex.div_natCast_re] at hre
  rw [h₁.2.1, h₂.2.1] at hre
  have hqR : (q₁ : ℝ) = q₂ := by
    field_simp at hre
    linarith
  have hq : q₁ = q₂ := by exact_mod_cast hqR
  subst hq
  have hn0 : (q₁ : ℂ) ≠ 0 := by exact_mod_cast hq₁.ne'
  rw [div_left_inj' hn0] at h
  rw [h]

end GoldbachBoundaries.Paper2.M2
