import PrimePairNB.ThmA.G20_Branches
import PrimePairNB.ThmA.Fill.GCommon
import PrimePairNB.ThmA.Fill.jump_of_access
import PrimePairNB.ThmA.Fill.J_spec
import PrimePairNB.ThmA.Fill.cutDisc_facts

/-!
# `isBranch_uniform_cut` (the branch proposition, the discs `V_p` at cut points)

Take the access disc `V = Δ(p, r)` and its continuation `Gp`. Every member of the family at a point
`q ∈ V` is `Gp + m₀` near `q` for one `m₀ ∈ MSpan`: pick a point `q₁` of `V⁺ ∪ V⁻` close to `q` where
the germ of `f` is `Gn + m`; there `Gn = Gp` (on `V⁺`) or `Gn = Gp - M_α` (on `V⁻`, the jump), and the
identity theorem on a small ball carries `f = Gp + m₀` back to `q`. `Gp + m₀` is analytic on `V`
and is a branch at every point of `V` (its germ at points of `Ω_ℍ ∩ V` is `Gn + m₀` or
`Gn + (M_α + m₀)`).
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-- **the branch proposition, the discs `V_p` for `p` on a cut.** No RH.

Sketch. Take `(r, Gp)` from `hP.access`; members of `𝔉_p` are `Gp + m`, `m ∈ MSpan`. Given `q ∈ V`
and `f` with `IsBranch κ Gn q f`: if `q ∈ V⁺`, `f = Gn + m = Gp + m` near `q`; if `q ∈ V⁻`,
`f = Gn + m = Gp + (m - M_α)` near `q` (`jump_of_access`, `Mon_mem_MSpan`); if `q ∈ cut_α`, take a
small ball `B` about `q` inside `V` on which `f` is analytic and `IsBranch`'s eventual clause holds;
on the convex `B ∩ V⁺`, `f - Gn` is locally in `MSpan`, so equal to one `m₀` (identity theorem from
one point), and `f = Gp + m₀` on `B` (identity theorem). In all cases `F = Gp + m` is analytic on
`V` (`MSpan_analyticOn`, `V ⊆ ℍ`) and is a branch at every `q' ∈ V`: points of `Ω_ℍ` near `q'` inside
`V` lie in `V⁺` (germ `Gn + m`) or `V⁻` (germ `Gn + (M_α + m)`) by `cutDisc_facts`. -/
theorem isBranch_uniform_cut {κ : ℝ} (hκ : IsGoodSlant κ) {Gn : ℂ → ℂ}
    (hP : IsPrincipalSheet κ Gn) {α : ℂ} (hα : α ∈ catalogue) {p : ℂ}
    (hp : p ∈ cut (slantDir κ) α) (hne : p ≠ α) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ ball p r, ∀ f : ℂ → ℂ, IsBranch κ Gn q f →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball p r) ∧ F =ᶠ[𝓝 q] f ∧
        ∀ q' ∈ ball p r, IsBranch κ Gn q' F := by
  obtain ⟨r, hr, hD, Gp, hGp, hup⟩ := hP.access α hα p hp hne
  have hjump := jump_of_access hκ hP hα hp hne hr hD hGp hup
  obtain ⟨htri, hupΩ, hlowΩ, hupo, hlowo, -, -⟩ := cutDisc_facts hp hD
  have hM := Mon_mem_MSpan hα
  -- the germ of `Gp + m` at points of `Ω_ℍ ∩ V`
  have hgerm : ∀ m ∈ MSpan, ∀ q' ∈ ball p r, q' ∈ Omega κ →
      ∃ m' ∈ MSpan, (fun s => Gp s + m s) =ᶠ[𝓝 q'] fun s => Gn s + m' s := by
    intro m hm q' hq' hΩ
    have hnc : q' ∉ cut (slantDir κ) α := fun hc => hΩ.2 (mem_biUnion hα hc)
    rcases htri q' hq' hnc with hu | hl
    · refine ⟨m, hm, ?_⟩
      filter_upwards [hupo.mem_nhds hu] with s hs
      rw [hup hs]
    · refine ⟨Mon α + m, add_mem hM hm, ?_⟩
      filter_upwards [hlowo.mem_nhds hl] with s hs
      rw [hjump hs, Pi.add_apply]
      ring
  have hFa : ∀ m ∈ MSpan, AnalyticOnNhd ℂ (fun s => Gp s + m s) (ball p r) := fun m hm z hz =>
    (hGp z hz).add (MSpan_analyticOn hm z (hD.1 hz))
  refine ⟨r, hr, fun q hq f hf => ?_⟩
  have hev : ∀ᶠ z in 𝓝 q, z ∈ ball p r ∧ AnalyticAt ℂ f z ∧
      (z ∈ Omega κ → ∃ m ∈ MSpan, f =ᶠ[𝓝 z] fun s => Gn s + m s) :=
    (isOpen_ball.eventually_mem hq).and (hf.1.eventually_analyticAt.and hf.2)
  obtain ⟨ε, hε, hB⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- a point of `V⁺ ∪ V⁻` in the small ball
  have hq₁ : ∃ q₁ ∈ ball q ε, q₁ ∈ upperPart κ α p r ∨ q₁ ∈ lowerPart κ α p r := by
    by_cases hqc : q ∈ cut (slantDir κ) α
    · obtain ⟨⟨z, hz, hzi⟩, -⟩ := G_exists_upper_lower (κ := κ) (α := α)
        (isOpen_ball.inter isOpen_ball) ⟨mem_ball_self hε, hq⟩ (G_im_cut hqc)
      exact ⟨z, hz.1, Or.inl ⟨hz.2, hzi⟩⟩
    · exact ⟨q, mem_ball_self hε, htri q hq hqc⟩
  obtain ⟨q₁, hq₁B, hq₁V⟩ := hq₁
  have hq₁Ω : q₁ ∈ Omega κ := hq₁V.elim (fun h => hupΩ h) (fun h => hlowΩ h)
  obtain ⟨m, hm, hfm⟩ := (hB q₁ hq₁B).2.2 hq₁Ω
  -- one `m₀` with `Gp + m₀ = f` near `q₁`
  obtain ⟨m₀, hm₀, hm₀eq⟩ : ∃ m₀ ∈ MSpan, (fun s => Gp s + m₀ s) =ᶠ[𝓝 q₁] f := by
    rcases hq₁V with hu | hl
    · refine ⟨m, hm, ?_⟩
      filter_upwards [hupo.mem_nhds hu, hfm] with s hs hfs
      rw [hfs, hup hs]
    · refine ⟨m - Mon α, sub_mem hm hM, ?_⟩
      filter_upwards [hlowo.mem_nhds hl, hfm] with s hs hfs
      rw [hfs, hjump hs, Pi.sub_apply]
      ring
  have hBV : ball q ε ⊆ ball p r := fun z hz => (hB z hz).1
  have hfB : AnalyticOnNhd ℂ f (ball q ε) := fun z hz => (hB z hz).2.1
  have heq : EqOn (fun s => Gp s + m₀ s) f (ball q ε) :=
    ((hFa m₀ hm₀).mono hBV).eqOn_of_preconnected_of_eventuallyEq hfB
      (convex_ball _ _).isPreconnected hq₁B hm₀eq
  refine ⟨fun s => Gp s + m₀ s, hFa m₀ hm₀,
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) heq, fun q' hq' => ?_⟩
  refine ⟨hFa m₀ hm₀ q' hq', ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hq'] with z hz hzΩ
  exact hgerm m₀ hm₀ z hz hzΩ

end GoldbachBoundaries.ThmA
