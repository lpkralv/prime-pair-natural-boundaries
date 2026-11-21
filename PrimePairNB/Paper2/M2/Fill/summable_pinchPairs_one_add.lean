import PrimePairNB.Paper2.M2.Single
import PrimePairNB.ThmA.Fill.germ_unique
import PrimePairNB.Paper2.M2.Fill.ncard_far_shell_le
import PrimePairNB.Paper2.M2.Fill.far_tail

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

set_option maxHeartbeats 800000 in
/-- **Absolute convergence of `𝓡(1 + v)`** (Z1, Z2, Z6, `B < 1`). Apply `lem_far_proof` with `Y = |Im v| + 1` and
`H = H₀`: the far pairs are summable. The other pairs of `pinchPairs (1 + v)` are `(1, v)`, `(v, 1)` and the competing
pairs with `|Im p.1| ≤ H₀`; the latter have `p.1 ∈ SH H₀` (`pinchPairs_other_mem`), a finite set
(`lem_Q_iii_proof` windows with `ε = 1 - B`, or `poleSetQ_locallyFinite` on a compact set), and `p ↦ p.1` is
injective. A family summable off a finite set is summable (`Finset.summable_compl_iff`, after identifying the far
subtype with the complement through `Equiv.subtypeSubtypeEquivSubtypeInter` or `Summable.subtype`-style lemmas). -/
theorem summable_pinchPairs_one_add (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) :
    ∀ v : ℂ, 0 < v.re → v.re ≤ 1 →
      Summable fun p : pinchPairs (1 + v) => ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ := by
  classical
  intro v hv hv1
  obtain ⟨H, hHY, htail⟩ := far_tail hZ1 hZ2 hZ6 hB (show 0 < |v.im| + 1 by positivity)
  have hfar := (htail H le_rfl v hv hv1 (by linarith)).1
  obtain ⟨C, hC⟩ := ncard_far_shell_le hZ1 hZ2 hB
  let S (j : ℕ) : Set (ℂ × ℂ) := {p | p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧
    (j : ℝ) ≤ |p.1.im| ∧ |p.1.im| < j + 1}
  let K : Set (ℂ × ℂ) := {(1, v), (v, 1)} ∪ ⋃ j ∈ Finset.range (⌊H⌋₊ + 1), S j
  have hK : K.Finite := by
    apply Set.Finite.union (Set.toFinite _)
    exact (Finset.finite_toSet _).biUnion fun j _ => (hC v hv j).1
  let I := pinchPairs (1 + v)
  let N : Set I := {p | p.val = (1, v) ∨ p.val = (v, 1) ∨ |p.val.1.im| ≤ H}
  have hmap : MapsTo (fun p : I => p.val) N K := by
    intro p hp
    rcases hp with hp | hp | hp
    · exact Or.inl (by simp [hp])
    · exact Or.inl (by simp [hp])
    · by_cases h1 : p.val = (1, v)
      · exact Or.inl (by simp [h1])
      by_cases h2 : p.val = (v, 1)
      · exact Or.inl (by simp [h2])
      right
      refine Set.mem_iUnion.mpr ⟨⌊|p.val.1.im|⌋₊, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · apply Finset.mem_range.mpr
        exact Nat.lt_succ_of_le (Nat.floor_mono hp)
      · exact ⟨p.property, h1, h2, Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  have hN : N.Finite := Set.Finite.of_injOn hmap Subtype.val_injective.injOn hK
  have hn (p : I) (hp : p ∈ Nᶜ) :
      p.val ≠ (1, v) ∧ p.val ≠ (v, 1) ∧ H < |p.val.1.im| := by
    change ¬ (p.val = (1, v) ∨ p.val = (v, 1) ∨ |p.val.1.im| ≤ H) at hp
    push Not at hp
    exact hp
  let g : ↑(Nᶜ : Set I) → {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} :=
    fun p => ⟨p.val.val, p.val.property, hn p.val p.property⟩
  have hginj : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val hpq
    exact hh
  let f : I → ℝ := fun p => ‖Rcoef p.val.1 * Rcoef p.val.2 * betaB p.val.1 p.val.2‖
  have hs := hfar.comp_injective hginj
  change Summable (fun p : ↑(Nᶜ : Set I) => f p.val) at hs
  exact (hN.summable_compl_iff (f := f)).mp hs

end GoldbachBoundaries.Paper2.M2
