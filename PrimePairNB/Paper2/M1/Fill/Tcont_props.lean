import PrimePairNB.Paper2.M1.Fill.Binf_le_Bsup_le_one
import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.T_differentiableOn
import PrimePairNB.Paper2.M1.Fill.Tc_analyticAt
import PrimePairNB.Paper2.M1.Fill.Tc_indep
import PrimePairNB.Paper2.M1.Fill.Tc_meromorphicAt
import PrimePairNB.Paper2.M1.Fill.exists_adm_reg
import PrimePairNB.Paper2.M1.Fill.isOpen_RegC
import PrimePairNB.Paper2.M1.Fill.pinch_locallyFinite

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma E2_avoid_pinch_ne (hZ1 : Z1) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    ∀ᶠ s in 𝓝[≠] s₀, s ∉ Pinch := by
  obtain ⟨U, hU, hfin⟩ := pinch_locallyFinite hZ1 hs₀
  have hn : ((U ∩ Pinch) ∩ {s₀}ᶜ)ᶜ ∈ 𝓝 s₀ :=
    (hfin.subset (show ((U ∩ Pinch) ∩ {s₀}ᶜ) ⊆ U ∩ Pinch from inter_subset_left)).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hU, nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with s hs hn hsne
  intro hp
  exact hn ⟨⟨hs, hp⟩, hsne⟩

private lemma E2_avoid_pinch (hZ1 : Z1) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) (hP : s₀ ∉ Pinch) :
    ∀ᶠ s in 𝓝 s₀, s ∉ Pinch := by
  obtain ⟨U, hU, hfin⟩ := pinch_locallyFinite hZ1 hs₀
  have hn : (U ∩ Pinch)ᶜ ∈ 𝓝 s₀ :=
    hfin.isClosed.isOpen_compl.mem_nhds (by rintro ⟨_, hp⟩; exact hP hp)
  filter_upwards [hU, hn] with s hs hn
  exact fun hp => hn ⟨hs, hp⟩

/-- **`Tcont` is the continuation** (Z1, Z2, Z3): meromorphic on `σ > 2B_∞`, analytic off `Π`, order `≥ -1`
everywhere. Near `s₀` (case `B_∞ < 1`): `exists_adm_reg` gives `(δ, c)` with `s₀ ∈ RegC δ c`; on a neighbourhood
inside the open region and meeting `Π` at most in `s₀` (`pinch_locallyFinite`), `Tcont = 𝒯_c` off `s₀`
(`Tcont_eq_Tc`), and at `s₀` too when `s₀ ∉ Π`. Case `B_∞ = 1`: the region is `σ > 2` and `Tcont = T`
(`T_differentiableOn`). Uses: `exists_adm_reg`, `Tcont_eq_Tc`, `Tc_analyticAt`, `Tc_meromorphicAt`, `isOpen_RegC`,
`pinch_locallyFinite`, `T_differentiableOn`, `Tcont_eq_T_of_not`, `Binf_le_Bsup_le_one`. -/
theorem Tcont_props (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    MeromorphicOn Tcont (halfPlane (2 * Binf)) ∧ AnalyticOnNhd ℂ Tcont (halfPlane (2 * Binf) \ Pinch) ∧
      ∀ s ∈ halfPlane (2 * Binf), -1 ≤ meromorphicOrderAt Tcont s := by
  by_cases hB : Binf < 1
  · have hlocal : ∀ s ∈ halfPlane (2 * Binf), MeromorphicAt Tcont s ∧
        -1 ≤ meromorphicOrderAt Tcont s ∧ (s ∉ Pinch → AnalyticAt ℂ Tcont s) := by
      intro s hs
      obtain ⟨δ, c, h, hreg⟩ := exists_adm_reg hZ1 hB hs
      have he : Tcont =ᶠ[𝓝[≠] s] Tc δ c := by
        filter_upwards [nhdsWithin_le_nhds ((isOpen_RegC hZ1 h).mem_nhds hreg),
          E2_avoid_pinch_ne hZ1 hs] with z hz hzp
        exact Tcont_eq_Tc hZ1 hZ2 hZ3 h hz hzp
      obtain ⟨hm, ho⟩ := Tc_meromorphicAt hZ1 hZ2 hZ3 h hreg
      refine ⟨hm.congr he.symm, ?_, ?_⟩
      · rw [meromorphicOrderAt_congr he]
        exact ho
      · intro hP
        have he' : Tcont =ᶠ[𝓝 s] Tc δ c := by
          filter_upwards [((isOpen_RegC hZ1 h).mem_nhds hreg), E2_avoid_pinch hZ1 hs hP] with z hz hzp
          exact Tcont_eq_Tc hZ1 hZ2 hZ3 h hz hzp
        exact (Tc_analyticAt hZ1 hZ2 hZ3 h hreg hP).congr he'.symm
    exact ⟨fun s hs => (hlocal s hs).1, fun s hs => (hlocal s hs.1).2.2 hs.2,
      fun s hs => (hlocal s hs).2.1⟩
  · have hB1 : Binf = 1 := le_antisymm (Binf_le_Bsup_le_one.1.trans Binf_le_Bsup_le_one.2) (le_of_not_gt hB)
    have he : Tcont = T := by
      funext s
      exact Tcont_eq_T_of_not (fun h => hB h.1)
    have han : AnalyticOnNhd ℂ Tcont (halfPlane (2 * Binf)) := by
      rw [he, hB1, mul_one]
      exact T_differentiableOn.analyticOnNhd (isOpen_halfPlane 2)
    exact ⟨fun s hs => (han s hs).meromorphicAt, fun s hs => han s hs.1,
      fun s hs => le_trans (show (-1 : WithTop ℤ) ≤ 0 from by decide) (han s hs).meromorphicOrderAt_nonneg⟩

end GoldbachBoundaries.Paper2.M1
