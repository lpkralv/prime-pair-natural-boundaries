import PrimePairNB.Paper2.M2.Far

/-! `nearBad_finite_ncard_le` (`Lambda.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Near-bad points are few** (Z1). A witness `(a, b)` of `u ∈ NearBad H Y` has `a, b ∈ SH (H + Y)` and
`u = a + b - 1`, so `NearBad H Y` is inside the image of `SH (H + Y) ×ˢ SH (H + Y)`. -/
theorem nearBad_finite_ncard_le (hZ1 : Z1) {H Y : ℝ} (hH : 0 ≤ H) (hY : 0 ≤ Y)
    (hfin : (SH (H + Y)).Finite) :
    (NearBad H Y).Finite ∧ (NearBad H Y).ncard ≤ (SH (H + Y)).ncard ^ 2 := by
  have hsub : NearBad H Y ⊆ (fun p : ℂ × ℂ => p.1 + p.2 - 1) '' (SH (H + Y) ×ˢ SH (H + Y)) := by
    rintro u ⟨hre, hre1, hYu, p, hp, h1, h2, hpH⟩
    obtain ⟨⟨ha, ha1⟩, ⟨hb, hb1⟩, ⟨hare, -⟩, ⟨hbre, -⟩⟩ := pinchPairs_other_mem hZ1 hre hp h1 h2
    have hsum : p.1 + p.2 = 1 + u := hp.2.2
    have him : p.2.im = u.im - p.1.im := by
      have := congrArg Complex.im hsum
      simp only [add_im, one_im] at this
      linarith
    refine ⟨p, ⟨⟨ha, ha1, hare, by linarith⟩, ⟨hb, hb1, hbre, ?_⟩⟩, by simp [hsum]⟩
    rw [him]
    calc |u.im - p.1.im| ≤ |u.im| + |p.1.im| := abs_sub _ _
      _ ≤ H + Y := by linarith
  have hprod : (SH (H + Y) ×ˢ SH (H + Y)).Finite := hfin.prod hfin
  refine ⟨(hprod.image _).subset hsub, ?_⟩
  calc (NearBad H Y).ncard ≤ ((fun p : ℂ × ℂ => p.1 + p.2 - 1) '' (SH (H + Y) ×ˢ SH (H + Y))).ncard :=
        Set.ncard_le_ncard hsub (hprod.image _)
    _ ≤ (SH (H + Y) ×ˢ SH (H + Y)).ncard := Set.ncard_image_le hprod
    _ = (SH (H + Y)).ncard ^ 2 := by rw [Set.ncard_prod, sq]

end GoldbachBoundaries.Paper2.M2
