import PrimePairNB.ThmA.G13_Continuation

/-!
# `germ_unique`

Proof: the set `A = {t | f t =ᶠ[𝓝 (γ t)] g t}` is open and has open complement in the connected
space `[0,1]`, and contains `0`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-- **Uniqueness of continuation along a path.** Two continuations along the same path with
the same initial germ have the same germ at every time.

Sketch. Let `A = {t | f t =ᶠ[𝓝 (γ t)] g t}`; `0 ∈ A`. `A` is open: if `t ∈ A`, for `t'` near `t`
`f t' =ᶠ f t =ᶠ g t =ᶠ g t'` near `γ t'` (`EventuallyEq.eventuallyEq_nhds` moves the middle germ
from `γ t` to `γ t'`). `A` is closed: if `t ∈ closure A`, take a ball `B` around `γ t` on which
`f t` and `g t` are analytic; for `t' ∈ A` close to `t` with `γ t' ∈ B`, `f t = g t` near `γ t'`, so
on all of `B` (identity theorem, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`). `[0,1]` is
connected (`IsClopen.eq_univ`). -/
theorem germ_unique {γ : C(unitInterval, ℂ)} {f g : unitInterval → ℂ → ℂ}
    (hf : IsContinuationAlong γ f) (hg : IsContinuationAlong γ g)
    (h0 : f 0 =ᶠ[𝓝 (γ 0)] g 0) (t : unitInterval) : f t =ᶠ[𝓝 (γ t)] g t := by
  set A : Set unitInterval := {t | f t =ᶠ[𝓝 (γ t)] g t} with hAdef
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have h1 : ∀ᶠ t' in 𝓝 t, f t =ᶠ[𝓝 (γ t')] g t :=
      (γ.continuous.tendsto t).eventually ht.eventuallyEq_nhds
    filter_upwards [hf.locallyEq t, hg.locallyEq t, h1] with t' hft hgt h1t
    exact hft.trans (h1t.trans hgt.symm)
  have hAc : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨r, hr, hfr⟩ := Metric.isOpen_iff.mp (isOpen_analyticAt ℂ (f t)) _ (hf.analyticAt t)
    obtain ⟨r', hr', hgr⟩ := Metric.isOpen_iff.mp (isOpen_analyticAt ℂ (g t)) _ (hg.analyticAt t)
    set ρ := min r r'
    have hfA : AnalyticOnNhd ℂ (f t) (ball (γ t) ρ) := fun z hz =>
      hfr (ball_subset_ball (min_le_left _ _) hz)
    have hgA : AnalyticOnNhd ℂ (g t) (ball (γ t) ρ) := fun z hz =>
      hgr (ball_subset_ball (min_le_right _ _) hz)
    have hball : ∀ᶠ t' in 𝓝 t, γ t' ∈ ball (γ t) ρ :=
      (γ.continuous.tendsto t).eventually (isOpen_ball.mem_nhds (mem_ball_self (lt_min hr hr')))
    filter_upwards [hf.locallyEq t, hg.locallyEq t, hball] with t' hft hgt hbt
    intro ht'
    apply ht
    have heq : f t =ᶠ[𝓝 (γ t')] g t := hft.symm.trans (ht'.trans hgt)
    have := hfA.eqOn_of_preconnected_of_eventuallyEq hgA (convex_ball _ _).isPreconnected hbt heq
    exact Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self (lt_min hr hr'))) this
  have hcl : IsClopen A := ⟨⟨hAc⟩, hAo⟩
  rcases isClopen_iff.mp hcl with h | h
  · exact absurd (show (0 : unitInterval) ∈ A from h0) (by rw [h]; exact notMem_empty _)
  · show t ∈ A
    rw [h]; exact mem_univ t

end GoldbachBoundaries.ThmA
