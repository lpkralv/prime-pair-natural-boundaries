import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.T_differentiableOn
import PrimePairNB.Paper2.M1.Fill.Tc_indep
import PrimePairNB.Paper2.M1.Fill.exists_adm_reg
import PrimePairNB.Paper2.M1.Fill.finsum_nu_eq_pairSum
import PrimePairNB.Paper2.M1.Fill.hasResidue_Tc
import PrimePairNB.Paper2.M1.Fill.isOpen_RegC
import PrimePairNB.Paper2.M1.Fill.pinch_locallyFinite
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds

/-!
# `hasResidue_Tcont`

Case `B_∞ < 1`: an admissible `(δ, c)` has `s₀` in its region (`exists_adm_reg`); on a punctured neighbourhood of
`s₀` inside the open region and off `Π` (`pinch_locallyFinite`), `Tcont = 𝒯_c` (`Tcont_eq_Tc`); then
`hasResidue_Tc` and `finsum_nu_eq_pairSum`. Case `B_∞ ≥ 1`: `Tcont = T` everywhere (`Tcont_eq_T_of_not`), which is
holomorphic at `s₀` (`Re s₀ > 2`, `T_differentiableOn`), and there is no pair (`Re a ≤ 1` on `Σ_Q`), so both sides
are `0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Residue of `Tcont`** (Z1, Z2, Z3) at every `s₀` with `Re s₀ > 2B_∞`: if `B_∞ < 1`, `Tcont = 𝒯_c` on a punctured
neighbourhood (`exists_adm_reg`, `Tcont_eq_Tc`, `pinch_locallyFinite`, `isOpen_RegC`), then `hasResidue_Tc` and
`finsum_nu_eq_pairSum`; if `B_∞ = 1`, `Tcont = T` is holomorphic at `s₀` and there is no pair (`pairSum s₀ = 0`).
Uses: the lemmas named. -/
theorem hasResidue_Tcont (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    HasResidue Tcont s₀ (pairSum s₀) := by
  by_cases hB : Binf < 1
  · obtain ⟨δ, c, h, hs⟩ := exists_adm_reg hZ1 hB hs₀
    have hres := hasResidue_Tc hZ1 hZ2 hZ3 h hs
    rw [finsum_nu_eq_pairSum hZ1 h hs] at hres
    refine hres.congr ?_
    obtain ⟨U, hU, hUfin⟩ := pinch_locallyFinite hZ1 hs₀
    have hcl : ((U ∩ Pinch) \ {s₀})ᶜ ∈ 𝓝 s₀ :=
      (hUfin.sdiff).isClosed.compl_mem_nhds fun hm => hm.2 rfl
    filter_upwards [nhdsWithin_le_nhds (inter_mem (inter_mem hU ((isOpen_RegC hZ1 h).mem_nhds hs)) hcl),
      self_mem_nhdsWithin] with s ⟨⟨hsU, hsR⟩, hsc⟩ hsne
    have hsP : s ∉ Pinch := fun hP => hsc ⟨⟨hsU, hP⟩, hsne⟩
    exact (Tcont_eq_Tc hZ1 hZ2 hZ3 h hsR hsP).symm
  · have hs2 : 2 < s₀.re := by push Not at hB; linarith
    have hfun : Tcont = T := funext fun s => Tcont_eq_T_of_not fun hh => hB hh.1
    have hempty : IsEmpty (pinchPairs s₀) := by
      refine ⟨fun ⟨p, hp1, hp2, hp12⟩ => ?_⟩
      have h1 := (poleSetQ_re_bounds hp1).2.1
      have h2 := (poleSetQ_re_bounds hp2).2.1
      have hre : p.1.re + p.2.re = s₀.re := by rw [← hp12]; simp
      linarith
    have hzero : pairSum s₀ = 0 := by
      rw [pairSum]
      exact tsum_empty
    rw [hfun, hzero]
    exact hasResidue_zero_of_analyticAt
      (T_differentiableOn.analyticAt ((isOpen_halfPlane 2).mem_nhds hs2))

end GoldbachBoundaries.Paper2.M1
