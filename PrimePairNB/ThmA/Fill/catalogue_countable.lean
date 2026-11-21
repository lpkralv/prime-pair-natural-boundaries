import PrimePairNB.ThmA.G14_Geometry
import Mathlib.NumberTheory.LSeries.ZetaZeros

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.ThmA

/-- `𝒞` is countable.

Sketch. `𝒞 ⊆ {2} ∪ range (k ↦ 1 + 1/k) ∪ ⋃ₙ (ρ ↦ 1 + ρ/n) '' NontrivialZeros`. The zeros of `ζ`
in `{1}ᶜ` are a discrete closed subset (`riemannZeta_zeros_locallyFinite`, `SigmaFinite.lean`, or
`AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`), hence countable in the second-countable `ℂ`
(`Set.Countable` of a set with `DiscreteTopology` in a second-countable space). -/
theorem catalogue_countable : catalogue.Countable := by
  have hz : NontrivialZeros.Countable :=
    (isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete
      isDiscrete_riemannZetaZeros).mono (fun _ h => h.1)
  have hc := (countable_singleton (2 : ℂ)).union
    ((countable_range (fun k : ℕ => 1 + 1 / (k : ℂ))).union
      (countable_iUnion fun n : ℕ => hz.image (fun ρ => 1 + ρ / (n : ℂ))))
  apply hc.mono
  rintro s ((hs | ⟨k, _, _, rfl⟩) | ⟨n, _, _, ρ, hρ, rfl⟩)
  · exact Or.inl hs
  · exact Or.inr (Or.inl ⟨k, rfl⟩)
  · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨n, ρ, hρ, rfl⟩))

end GoldbachBoundaries.ThmA
