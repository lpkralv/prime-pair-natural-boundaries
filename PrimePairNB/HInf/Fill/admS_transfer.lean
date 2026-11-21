import PrimePairNB.HInf.Fill.exists_admS

/-!
# `admS_transfer`

The change of variable `v = 2s + 1` on germ chains: the path is scaled and each function is precomposed with `(v - 1)/2`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `(v - 1)/2` at `2s + 1` is `s`. -/
lemma half_sub_one_two_add (s : ℂ) : (2 * s + 1 - 1) / 2 = s := by ring

/-- Germs carried by `v ↦ (v - 1)/2`. -/
lemma eventuallyEq_comp_half {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[𝓝 s] g) :
    (fun v => f ((v - 1) / 2)) =ᶠ[𝓝 (2 * s + 1)] fun v => g ((v - 1) / 2) := by
  have hc : ContinuousAt (fun v : ℂ => (v - 1) / 2) (2 * s + 1) := by fun_prop
  have ht : Tendsto (fun v : ℂ => (v - 1) / 2) (𝓝 (2 * s + 1)) (𝓝 s) := by
    have := hc.tendsto
    rwa [half_sub_one_two_add] at this
  exact ht.eventually h

/-- Analyticity carried by `v ↦ (v - 1)/2`. -/
lemma analyticAt_comp_half {f : ℂ → ℂ} {s : ℂ} (h : AnalyticAt ℂ f s) :
    AnalyticAt ℂ (fun v => f ((v - 1) / 2)) (2 * s + 1) := by
  have hm : AnalyticAt ℂ (fun v : ℂ => (v - 1) / 2) (2 * s + 1) := by fun_prop
  have h' : AnalyticAt ℂ f ((2 * s + 1 - 1) / 2) := by rwa [half_sub_one_two_add]
  exact AnalyticAt.comp (g := f) (f := fun v : ℂ => (v - 1) / 2) h' hm

/-- Under `(H_∞)`, the change of variable `v = 2s + 1` carries `AdmS` to the hypothesis of `germFam_of_admissible_S`. -/
theorem admS_transfer (hZ1 : Z1) (hH : Hinf) {g : ℂ → ℂ} {s₁ : ℂ} (hg : AdmS g s₁) :
    IsAdmissibleGermOn DS (halfPlane (2 * Binf) \ Pinch) (halfPlane 3) (fun v => g ((v - 1) / 2)) (2 * s₁ + 1) := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := hg
  have hB : Binf = 1 / 2 := M2.Binf_eq_half_of_Hinf hZ1 hH
  let γ' : C(unitInterval, ℂ) := ⟨fun t => 2 * γ t + 1, by fun_prop⟩
  have hγ' : ∀ t, γ' t = 2 * γ t + 1 := fun _ => rfl
  refine ⟨γ', fun t => ?_, ?_, rfl, fun t v => f t ((v - 1) / 2), ⟨fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · have ht := hγ t
    have ht0 : (0 : ℝ) < (γ t).re := ht.1
    refine ⟨?_, fun hc => ht.2 (mem_catS_iff.mpr ⟨ht0, hc⟩)⟩
    show 2 * Binf < (2 * γ t + 1).re
    rw [hB]
    simp
    linarith
  · have h0' : (1 : ℝ) < (γ 0).re := h0
    show 3 < (2 * γ 0 + 1).re
    simp
    linarith
  · exact analyticAt_comp_half (hf.analyticAt t)
  · filter_upwards [hf.locallyEq t] with t' ht'
    exact eventuallyEq_comp_half ht'
  · exact eventuallyEq_comp_half hf0
  · exact eventuallyEq_comp_half hg1

end GoldbachBoundaries.HInf.Fill

