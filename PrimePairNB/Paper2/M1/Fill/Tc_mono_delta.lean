import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec

/-!
# `Tc_mono_delta`

Shrinking `δ` to `δ' ≤ δ` adds to `F_δ` only points `a` with `Re a ≤ B_∞ + δ < c` and `σ - Re a > c + δ`, where
both indicators of `ν` vanish.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Shrinking `δ` does not change `𝒯_c` (Z1, for the finiteness of `F_{δ'}`): the extra points `a ∈ F_{δ'} ∖ F_δ` have
`Re a ≤ B_∞ + δ < c` and `σ - Re a > c + δ`, so both indicators vanish. Uses: `Fdelta_spec`. -/
theorem Tc_mono_delta (hZ1 : Z1) {δ δ' c : ℝ} (h : AdmC δ c) (hδ' : 0 < δ') (hδδ : δ' ≤ δ) :
    AdmC δ' c ∧ ∀ s ∈ RegC δ c, s ∈ RegC δ' c ∧ Tc δ' c s = Tc δ c s := by
  obtain ⟨hδ, hδ1, hc1, hc2, hcne⟩ := h
  have hsub : Fdelta δ ⊆ Fdelta δ' := fun a ha => ⟨ha.1, by linarith [ha.2]⟩
  -- a point of `F_{δ'}` outside `F_δ` has real part at most `B_∞ + δ`
  have hout : ∀ a ∈ Fdelta δ', a ∉ Fdelta δ → a.re ≤ Binf + δ := by
    intro a ha hna
    by_contra hlt
    exact hna ⟨ha.1, lt_of_not_ge hlt⟩
  have hadm : AdmC δ' c := by
    refine ⟨hδ', by linarith, by linarith, hc2, fun a ha => ?_⟩
    by_cases haδ : a ∈ Fdelta δ
    · exact hcne a haδ
    · have := hout a ha haδ
      intro e; linarith
  refine ⟨hadm, fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  have hreg : s ∈ RegC δ' c := by
    refine ⟨by linarith, fun a ha => ?_⟩
    by_cases haδ : a ∈ Fdelta δ
    · exact hs2 a haδ
    · have := hout a ha haδ
      intro e; linarith
  refine ⟨hreg, ?_⟩
  have hF := (Fdelta_spec hZ1 δ hδ).1
  have hF' := (Fdelta_spec hZ1 δ' hδ').1
  show IcQ Qcont c s + _ = IcQ Qcont c s + _
  congr 1
  rw [finsum_mem_eq_finite_toFinset_sum _ hF', finsum_mem_eq_finite_toFinset_sum _ hF]
  symm
  refine Finset.sum_subset (fun a ha => hF'.mem_toFinset.mpr (hsub (hF.mem_toFinset.mp ha)))
    fun a ha hna => ?_
  have ha' := hF'.mem_toFinset.mp ha
  have hna' : a ∉ Fdelta δ := fun h' => hna (hF.mem_toFinset.mpr h')
  have hre := hout a ha' hna'
  have h1 : ¬ (c < a.re) := by linarith
  have h2 : ¬ (s.re - a.re < c) := by linarith
  simp [nu, iverson, h1, h2]

end GoldbachBoundaries.Paper2.M1
