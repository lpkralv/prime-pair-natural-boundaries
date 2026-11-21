import PrimePairNB.Paper2.M4b.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Holomorphy of a double prime series by the M-test** (general). Given `s₀ ∈ U`, take `V` and `u` from `hloc`
and an open ball `B ⊆ V ∩ U` about `s₀`; on `B`, `Dser W = ∑' pq, W · pq.1 pq.2` is holomorphic by Mathlib's
`differentiableOn_tsum_of_summable_norm` (each term is, by `hW`, and `‖W s pq‖ ≤ u pq`). Holomorphy at every point of
`U` from an open neighbourhood (`DifferentiableOn.differentiableAt`, `IsOpen.mem_nhds`). -/
theorem differentiableOn_dser {W : ℂ → ℕ → ℕ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hW : ∀ pq : Nat.Primes × Nat.Primes, DifferentiableOn ℂ (fun s => W s (pq.1 : ℕ) (pq.2 : ℕ)) U)
    (hloc : ∀ s₀ ∈ U, ∃ V ∈ 𝓝 s₀, ∃ u : Nat.Primes × Nat.Primes → ℝ, Summable u ∧
      ∀ s ∈ V, ∀ pq : Nat.Primes × Nat.Primes, ‖W s (pq.1 : ℕ) (pq.2 : ℕ)‖ ≤ u pq) :
    DifferentiableOn ℂ (Dser W) U := by
  intro s₀ hs₀
  obtain ⟨V, hV, u, hu, hbound⟩ := hloc s₀ hs₀
  obtain ⟨B, hBV, hBo, hsB⟩ := _root_.mem_nhds_iff.mp hV
  have hD : DifferentiableOn ℂ (Dser W) (B ∩ U) := by
    apply differentiableOn_tsum_of_summable_norm hu
    · intro pq
      exact (hW pq).mono inter_subset_right
    · exact hBo.inter hU
    · intro pq s hs
      exact hbound s (hBV hs.1) pq
  exact (hD.differentiableAt ((hBo.inter hU).mem_nhds ⟨hsB, hs₀⟩)).differentiableWithinAt

end GoldbachBoundaries.Paper2.M4b
