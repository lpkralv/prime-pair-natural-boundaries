import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.poleSetQ_locallyFinite
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `Π` is locally finite in `σ > 2B_∞` (Z1): near `s₀` every `a + b` has one of `a, b` in the finite `F_δ`
(`2B_∞ + 4δ < σ₀`), and the other in a bounded part of `Re z > 0`, where `Σ_Q` is locally finite. If `B_∞ = 1`,
`Π ⊆ {σ ≤ 2}` (`Re a ≤ 1`) misses a neighbourhood. Uses: `Fdelta_spec`, `poleSetQ_locallyFinite`,
`poleSetQ_re_bounds`. -/
theorem pinch_locallyFinite (hZ1 : Z1) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    ∃ U ∈ 𝓝 s₀, (U ∩ Pinch).Finite := by
  classical
  let δ : ℝ := (s₀.re - 2 * Binf) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hF := (Fdelta_spec hZ1 δ hδ).1
  let := hF.fintype
  have hsa : ∀ a : Fdelta δ, 0 < (s₀ - a).re := by
    intro a
    have hb := half_le_Binf hZ1
    have ha := (poleSetQ_re_bounds a.property.1).2.1
    simp only [sub_re]
    linarith
  choose U hU hUf using fun a : Fdelta δ => poleSetQ_locallyFinite (s₀ - a) (hsa a)
  let V : Set ℂ := {s | 2 * (Binf + δ) < s.re ∧ ∀ a : Fdelta δ, s - (a : ℂ) ∈ U a}
  have hV : V ∈ 𝓝 s₀ := by
    have hr : ∀ᶠ s in 𝓝 s₀, 2 * (Binf + δ) < s.re :=
      (isOpen_halfPlane _).mem_nhds (by dsimp [δ]; change 2 * (Binf + (s₀.re - 2 * Binf) / 4) < s₀.re; linarith)
    have hall : ∀ᶠ s in 𝓝 s₀, ∀ a : Fdelta δ, s - (a : ℂ) ∈ U a := by
      rw [Filter.eventually_all]
      intro a
      exact (show ContinuousAt (fun s : ℂ => s - (a : ℂ)) s₀ from
        continuousAt_id.sub continuousAt_const).eventually (hU a)
    exact hr.and hall
  refine ⟨V, hV, ?_⟩
  have hfinite : (⋃ a : Fdelta δ, (fun b : ℂ => (a : ℂ) + b) '' (U a ∩ PoleSetQ)).Finite :=
    Set.finite_iUnion fun a => (hUf a).image _
  apply hfinite.subset
  rintro s ⟨hsV, a, ha, b, hb, rfl⟩
  have hex : a ∈ Fdelta δ ∨ b ∈ Fdelta δ := by
    by_contra hn
    have hn' := not_or.mp hn
    have ha' : a.re ≤ Binf + δ := le_of_not_gt (fun h => hn'.1 ⟨ha, h⟩)
    have hb' : b.re ≤ Binf + δ := le_of_not_gt (fun h => hn'.2 ⟨hb, h⟩)
    have hh := hsV.1
    simp only [add_re] at hh
    linarith
  rcases hex with haf | hbf
  · apply Set.mem_iUnion.mpr
    refine ⟨⟨a, haf⟩, b, ⟨?_, hb⟩, rfl⟩
    simpa using hsV.2 ⟨a, haf⟩
  · apply Set.mem_iUnion.mpr
    refine ⟨⟨b, hbf⟩, a, ⟨?_, ha⟩, add_comm b a⟩
    simpa using hsV.2 ⟨b, hbf⟩

end GoldbachBoundaries.Paper2.M1
