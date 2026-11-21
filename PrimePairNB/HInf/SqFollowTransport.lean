import PrimePairNB.HInf.SqBoundary

/-! Transport of continuation and admissibility through `v = 2s`. -/
noncomputable section
open Complex Filter Topology Set Metric
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.SqFollow

lemma double_half (v : ℂ) : 2 * (v / 2) = v := by ring
lemma half_double (s : ℂ) : 2 * s / 2 = s := by ring

lemma eventuallyEq_double {f g : ℂ → ℂ} {v : ℂ} (h : f =ᶠ[𝓝 v] g) :
    (fun s => f (2 * s)) =ᶠ[𝓝 (v / 2)] fun s => g (2 * s) := by
  have hc : ContinuousAt (fun s : ℂ => 2 * s) (v / 2) := by fun_prop
  have ht : Tendsto (fun s : ℂ => 2 * s) (𝓝 (v / 2)) (𝓝 v) := by
    simpa only [double_half] using hc.tendsto
  exact ht.eventually h

lemma analyticAt_double {f : ℂ → ℂ} {v : ℂ} (h : AnalyticAt ℂ f v) :
    AnalyticAt ℂ (fun s => f (2 * s)) (v / 2) := by
  have h' : AnalyticAt ℂ f (2 * (v / 2)) := by simpa only [double_half] using h
  exact h'.comp (f := fun s : ℂ => 2 * s) (by fun_prop)

lemma continuation_half {γ : C(unitInterval, ℂ)} {f : unitInterval → ℂ → ℂ}
    (hf : IsContinuationAlong γ f) :
    IsContinuationAlong (⟨fun t => γ t / 2, by fun_prop⟩ : C(unitInterval, ℂ))
      (fun t s => f t (2 * s)) := by
  refine ⟨fun t => analyticAt_double (hf.analyticAt t), fun t => ?_⟩
  filter_upwards [hf.locallyEq t] with t' ht'
  exact eventuallyEq_double ht'

lemma terminal_double {γ : C(unitInterval, ℂ)} {g : ℂ → ℂ}
    (hg : IsTerminalGerm SqSer γ g) :
    IsTerminalGerm DSq (⟨fun t => 2 * γ t, by fun_prop⟩ : C(unitInterval, ℂ))
      (fun v => g (v / 2)) := by
  obtain ⟨f, hf, hf0, hg1⟩ := hg
  refine ⟨fun t v => f t (v / 2),
    ⟨fun t => analyticAt_comp_sq_half (hf.analyticAt t), fun t => ?_⟩,
    eventuallyEq_comp_sq_half hf0, eventuallyEq_comp_sq_half hg1⟩
  filter_upwards [hf.locallyEq t] with t' ht'
  exact eventuallyEq_comp_sq_half ht'

lemma admSq_of_admSqV {g : ℂ → ℂ} {v : ℂ} (hg : AdmSqV g v) :
    AdmSq (fun s => g (2 * s)) (v / 2) := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := hg
  let γ' : C(unitInterval, ℂ) := ⟨fun t => γ t / 2, by fun_prop⟩
  refine ⟨γ', fun t => ?_, ?_, rfl, fun t s => f t (2 * s), continuation_half hf,
    ?_, eventuallyEq_double hg1⟩
  · have ht := hγ t
    have hre : 1 < (γ t).re := ht.1
    refine ⟨?_, ?_⟩
    · rw [twoL_HL]
      show 1 / 2 < (γ t / 2).re
      simp; linarith
    · intro hc
      have hp := (mem_catSq_iff.mp hc).2
      change 2 * (γ t / 2) ∈ Pinch at hp
      rw [double_half] at hp
      exact ht.2 (mem_catG_iff.mpr ⟨hre, hp⟩)
  · rw [twoL_RL]
    show 1 < (γ 0 / 2).re
    have h0' : 2 < (γ 0).re := h0
    simp; linarith
  · simpa only [γ', ContinuousMap.coe_mk, DSq, half_double] using eventuallyEq_double hf0

end GoldbachBoundaries.HInf.SqFollow
