import PrimePairNB.ThmA.G20_Branches

/-!
# `exists_component_reaching_line`

Proof: `U = connectedComponentIn (W ∩ ℍ) s₁` is open and connected. It is not closed in
the connected `W` (else `W ⊆ U ⊆ ℍ`, but `W` meets `σ = 1`), so some `x ∈ W ∩ closure U` lies
outside `U`; `x ∉ ℍ` (else a ball about `x` inside `W ∩ ℍ` meets `U`, so lies in `U`), and
`Re x ≥ 1`, so `x = 1 + iy`. A ball `Δ(x, r) ⊆ W` has `Δ ∩ ℍ` convex and meeting `U`, so inside `U`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.ThmA

/-- **A component reaching the line** (the domain corollary, first half of the proof; general
topology).

Sketch. `U = connectedComponentIn (W ∩ ℍ) s₁`, open (`IsOpen.connectedComponentIn`).
`U ≠ W` since `W` meets `σ = 1`, so `U` is not closed in `W` (else clopen in connected `W`); take
`x ∈ W ∩ closure U ∖ U`. `x ∉ ℍ` (else `x` is in a component of `W ∩ ℍ` meeting `U`), and
`Re x ≥ 1` (limit of points of `ℍ`), so `x = 1 + iy`. Take `ball x r ⊆ W`; `ball x r ∩ ℍ` is convex,
meets `U` (as `x ∈ closure U`), so it lies in `U` (`IsPreconnected.subset_connectedComponentIn`). -/
theorem exists_component_reaching_line {W : Set ℂ} (hWo : IsOpen W) (hWc : IsConnected W)
    (hWL : (W ∩ lineOne).Nonempty) {s₁ : ℂ} (hs₁ : s₁ ∈ W) (hs₁H : s₁ ∈ HH) :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧ U ⊆ W ∩ HH ∧ s₁ ∈ U ∧
      ∃ y r : ℝ, 0 < r ∧ ball (1 + (y : ℂ) * I) r ⊆ W ∧ ball (1 + (y : ℂ) * I) r ∩ HH ⊆ U := by
  set F : Set ℂ := W ∩ HH with hFdef
  have hFo : IsOpen F := hWo.inter (isOpen_halfPlane 1)
  have hs₁F : s₁ ∈ F := ⟨hs₁, hs₁H⟩
  set U : Set ℂ := connectedComponentIn F s₁ with hUdef
  have hUo : IsOpen U := hFo.connectedComponentIn
  have hUc : IsConnected U := isConnected_connectedComponentIn_iff.mpr hs₁F
  have hUF : U ⊆ F := connectedComponentIn_subset F s₁
  have hs₁U : s₁ ∈ U := mem_connectedComponentIn hs₁F
  have hHHc : Convex ℝ HH := convex_halfSpace_re_gt 1
  -- any preconnected subset of `F` meeting `U` lies in `U`
  have habsorb : ∀ T : Set ℂ, IsPreconnected T → T ⊆ F → (T ∩ U).Nonempty → T ⊆ U := by
    intro T hT hTF ⟨z, hzT, hzU⟩
    have h1 := hT.subset_connectedComponentIn hzT hTF
    rwa [← connectedComponentIn_eq hzU] at h1
  refine ⟨U, hUo, hUc, hUF, hs₁U, ?_⟩
  -- a point of `W ∩ closure U` outside `U`
  obtain ⟨x, ⟨hxcl, hxW⟩, hxU⟩ : ∃ x, x ∈ closure U ∩ W ∧ x ∉ U := by
    by_contra hcon
    push Not at hcon
    have hWU : W ⊆ U :=
      hWc.isPreconnected.subset_of_closure_inter_subset hUo ⟨s₁, hs₁, hs₁U⟩ hcon
    obtain ⟨z, hzW, hzL⟩ := hWL
    have : 1 < z.re := (hUF (hWU hzW)).2
    have hz1 : z.re = 1 := hzL
    linarith
  have hxre : x.re = 1 := by
    have hge : 1 ≤ x.re := by
      have hcl : closure U ⊆ {s : ℂ | 1 ≤ s.re} :=
        closure_minimal (fun z hz => show 1 ≤ z.re from le_of_lt (hUF hz).2)
          (isClosed_le continuous_const Complex.continuous_re)
      exact hcl hxcl
    rcases hge.lt_or_eq with hgt | heq
    · exfalso
      obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.mp hFo x ⟨hxW, hgt⟩
      obtain ⟨z, hzU, hzb⟩ : (U ∩ ball x ε).Nonempty := by
        have := mem_closure_iff.mp hxcl (ball x ε) isOpen_ball (mem_ball_self hε)
        obtain ⟨z, hz1, hz2⟩ := this
        exact ⟨z, hz2, hz1⟩
      have := habsorb (ball x ε) (convex_ball x ε).isPreconnected hεF ⟨z, hzb, hzU⟩
      exact hxU (this (mem_ball_self hε))
    · exact heq.symm
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hWo x hxW
  have hx : x = 1 + (x.im : ℂ) * I := by
    apply Complex.ext <;> simp [hxre]
  refine ⟨x.im, r, hr, ?_, ?_⟩
  · rw [← hx]; exact hrW
  · rw [← hx]
    apply habsorb _ ((convex_ball x r).inter hHHc).isPreconnected
      (fun z hz => ⟨hrW hz.1, hz.2⟩)
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hxcl (ball x r) isOpen_ball (mem_ball_self hr)
    exact ⟨z, ⟨hz1, (hUF hz2).2⟩, hz2⟩

end GoldbachBoundaries.ThmA
