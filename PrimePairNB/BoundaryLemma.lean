import PrimePairNB.Defs

/-!
# The abstract natural-boundary lemma

If the poles of `F` (points `a ∈ U` with `meromorphicOrderAt F a < 0`) accumulate at `z₀`, then no
function meromorphic on a disc around `z₀` agrees with `F` off a discrete subset of `disc ∩ U`, i.e.
`NoMeromorphicExtensionAt F U z₀`.

Proof: such an `f` is analytic on a punctured neighbourhood of `z₀` (it is meromorphic at `z₀`).
Take a pole `a ≠ z₀` of `F` in that punctured neighbourhood. Since `disc ∩ U` is open, agreement
off a discrete subset of it gives `f = F` on a punctured neighbourhood of `a`, so
`meromorphicOrderAt f a = meromorphicOrderAt F a < 0`; but `f` is analytic at `a`, so its order
there is `≥ 0`.

Only `IsOpen U` and the accumulation hypothesis are used. Meromorphy of `F` on `U` and
`z₀ ∈ frontier U` are not needed: `meromorphicOrderAt F a` is defined for every `F` (it is `0` when
`F` is not meromorphic at `a`), and the accumulation hypothesis already forces `z₀ ∈ closure U`.
The paper states the lemma with those hypotheses; the form here, without them, implies it.
-/

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- Agreement off a discrete subset of `S` gives agreement on a punctured neighbourhood of every
point `a` of which `S` is a neighbourhood. -/
lemma eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin {f F : ℂ → ℂ} {S : Set ℂ} {a : ℂ}
    (h : f =ᶠ[codiscreteWithin S] F) (ha : S ∈ 𝓝 a) : f =ᶠ[𝓝[≠] a] F := by
  have hd := (mem_codiscreteWithin.mp h) a (mem_of_mem_nhds ha)
  rw [disjoint_principal_right] at hd
  filter_upwards [hd, nhdsWithin_le_nhds ha] with y hy hyS
  by_contra hne
  exact hy ⟨hyS, hne⟩

/-- **Abstract natural-boundary lemma.** If `U` is open and the poles of `F` in `U` accumulate at
`z₀`, then `F` has no meromorphic extension to any disc around `z₀`. -/
theorem noMeromorphicExtensionAt_of_poles_accumulate {F : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U)
    (hacc : z₀ ∈ closure ({a ∈ U | meromorphicOrderAt F a < 0} \ {z₀})) :
    NoMeromorphicExtensionAt F U z₀ := by
  rintro r hr ⟨f, hf, hfF⟩
  have hev : ∀ᶠ y in 𝓝[≠] z₀, AnalyticAt ℂ f y ∧ y ∈ ball z₀ r :=
    (hf z₀ (mem_ball_self hr)).eventually_analyticAt.and
      (nhdsWithin_le_nhds (ball_mem_nhds z₀ hr))
  obtain ⟨a, ⟨haA, haB⟩, haU, hord⟩ :=
    (hev.and_frequently (mem_closure_ne_iff_frequently_within.mp hacc)).exists
  have hEq : f =ᶠ[𝓝[≠] a] F :=
    eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hfF
      ((isOpen_ball.inter hU).mem_nhds ⟨haB, haU⟩)
  have hnonneg := haA.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr hEq] at hnonneg
  exact (not_lt.mpr hnonneg) hord

/-- Ball form of the accumulation hypothesis: every disc around `z₀` contains a pole `a ≠ z₀` of
`F` in `U`. -/
theorem noMeromorphicExtensionAt_of_poles_in_every_ball {F : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U)
    (hacc : ∀ ε > 0, ∃ a ∈ U, a ≠ z₀ ∧ a ∈ ball z₀ ε ∧ meromorphicOrderAt F a < 0) :
    NoMeromorphicExtensionAt F U z₀ := by
  refine noMeromorphicExtensionAt_of_poles_accumulate hU (Metric.mem_closure_iff.mpr ?_)
  intro ε hε
  obtain ⟨a, haU, hne, hab, hord⟩ := hacc ε hε
  exact ⟨a, ⟨⟨haU, hord⟩, hne⟩, by rw [dist_comm]; exact hab⟩

end GoldbachBoundaries
