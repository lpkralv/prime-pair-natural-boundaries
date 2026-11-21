import PrimePairNB.Paper2.M2.Single
import PrimePairNB.ThmA.Fill.germ_unique

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Summing over finite shells** (general). For `f ≥ 0` on `ι`, a shell map `sh : ι → ℕ` with finite shells,
shell sums `≤ b j`, and `b` summable: `f` is summable with `∑' f ≤ ∑' b`. A finite `F ⊆ ι` has
`∑_F f ≤ ∑_{j ∈ sh F} b j ≤ ∑' b` (`b ≥ 0` because shell sums are), so `summable_of_sum_le` and
`Real.tsum_le_of_sum_le`. -/
theorem summable_tsum_le_of_shells {ι : Type*} (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (sh : ι → ℕ) (b : ℕ → ℝ)
    (hfin : ∀ j, {i | sh i = j}.Finite) (hb : ∀ j, ∑ᶠ i ∈ {i | sh i = j}, f i ≤ b j) (hbs : Summable b) :
    Summable f ∧ ∑' i, f i ≤ ∑' j, b j := by
  classical
  have hb0 : ∀ j, 0 ≤ b j := fun j =>
    (finsum_nonneg fun i => finsum_nonneg fun _ => hf i).trans (hb j)
  have hbound (F : Finset ι) : ∑ i ∈ F, f i ≤ ∑' j, b j := by
    calc
      ∑ i ∈ F, f i = ∑ j ∈ F.image sh, ∑ i ∈ F with sh i = j, f i :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem sh hi) f).symm
      _ ≤ ∑ j ∈ F.image sh, b j := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ∑ i ∈ F with sh i = j, f i ≤ ∑ i ∈ (hfin j).toFinset, f i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro i hi
              simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using (Finset.mem_filter.mp hi).2
            · intro i _ _
              exact hf i
          _ = ∑ᶠ i ∈ {i | sh i = j}, f i :=
            (finsum_mem_eq_finite_toFinset_sum _ (hfin j)).symm
          _ ≤ b j := hb j
      _ ≤ ∑' j, b j := hbs.sum_le_tsum _ (fun j _ => hb0 j)
  exact ⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩

end GoldbachBoundaries.Paper2.M2
