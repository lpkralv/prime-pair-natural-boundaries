import PrimePairNB.Paper2.M1.QnoRH
import PrimePairNB.Paper2.M1.Fill.meromorphicOrderAt_Qcont_ge

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Every continuation `Qc` of `Q` (`IsQCont`) equals `Qcont` off `Σ_Q`, and on a punctured neighbourhood of every
point of `Re z > 0` (identity theorem on the connected open set `{Re z > 0} ∖ Σ_Q`, whose complement in the
half-plane is closed and discrete by `poleSetQ_locallyFinite`). Uses: `poleSetQ_locallyFinite`. -/
theorem isQCont_eventuallyEq {Qc : ℂ → ℂ} (hQc : IsQCont Qc) :
    (∀ z ∈ halfPlane 0 \ PoleSetQ, Qc z = Qcont z) ∧ ∀ a ∈ halfPlane 0, Qc =ᶠ[𝓝[≠] a] Qcont := by
  have hQ : MeromorphicOn Qcont (halfPlane 0) := fun _ hz => meromorphicAt_Qcont hz
  have h2 : (2 : ℂ) ∈ halfPlane 1 := by norm_num [halfPlane]
  have hstart : Qc =ᶠ[𝓝[≠] (2 : ℂ)] Qcont := by
    filter_upwards [nhdsWithin_le_nhds ((isOpen_halfPlane 1).mem_nhds h2)] with z hz
    exact (hQc.2.1 hz).trans (GoldbachBoundaries.TIdentity.Qcont_eq_Q_of_one_lt hz).symm
  have htop : meromorphicOrderAt (Qc - Qcont) 2 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hstart] with z hz
    simp [hz]
  have hall : ∀ a ∈ halfPlane 0, Qc =ᶠ[𝓝[≠] a] Qcont := by
    intro a ha
    have ht := (hQc.1.sub hQ).meromorphicOrderAt_eq_top_of_isPreconnected
      (convex_halfSpace_re_gt 0).isPreconnected (by norm_num [halfPlane]) ha htop
    rw [meromorphicOrderAt_eq_top_iff] at ht
    filter_upwards [ht] with z hz
    exact sub_eq_zero.mp hz
  refine ⟨?_, hall⟩
  intro z hz
  have hcont : AnalyticAt ℂ Qcont z := by
    have h := analyticAt_Qcont_sub_sum hz.1 ∅ (fun n _ hn => regular_of_not_mem_poleSetQ hz.1 hz.2 hn)
    simpa using h
  exact tendsto_nhds_unique
    ((hQc.2.2 z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hall z hz.1).symm)

/-! Consequences of this file's lemma. -/

end GoldbachBoundaries.Paper2.M1
