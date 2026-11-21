import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.Binf_le_Bsup_le_one
import PrimePairNB.Paper2.M1.Fill.Tc_eq_T
import PrimePairNB.Paper2.M1.Fill.Tcont_props

/-!
# `eventuallyEq_Tcont_of_codiscrete`

Near
`3` (in `σ > 2` and in `σ > 2B_∞`, as `B_∞ ≤ 1`), `F = T` off a discrete set and `Tcont = T` (`Tcont_eqOn_T`), so
`F - Tcont` has order `⊤` at `3`; it is meromorphic on the connected half-plane `σ > 2B_∞` (`Tcont_props`), so its
order is `⊤` everywhere there.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Every meromorphic continuation agrees with `Tcont`** near every point of `σ > 2B_∞` (Z1, Z2, Z3): identity theorem
for meromorphic functions on the connected half-plane (`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`),
from agreement off a discrete set near `3` (`B_∞ ≤ 1`). Uses: `Tcont_props`, `Tcont_eqOn_T`,
`Binf_le_Bsup_le_one`. -/
theorem eventuallyEq_Tcont_of_codiscrete (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {F : ℂ → ℂ}
    (hF : MeromorphicOn F (halfPlane (2 * Binf))) (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) {s₀ : ℂ}
    (hs₀ : s₀ ∈ halfPlane (2 * Binf)) : F =ᶠ[𝓝[≠] s₀] Tcont := by
  have hB1 : Binf ≤ 1 := Binf_le_Bsup_le_one.1.trans Binf_le_Bsup_le_one.2
  have h3 : (3 : ℂ) ∈ halfPlane 2 := by norm_num [halfPlane]
  have h3B : (3 : ℂ) ∈ halfPlane (2 * Binf) := by
    show 2 * Binf < (3 : ℂ).re
    norm_num
    linarith
  have hn3 : halfPlane 2 ∈ 𝓝 (3 : ℂ) := (isOpen_halfPlane 2).mem_nhds h3
  have hFT3 : F =ᶠ[𝓝[≠] (3 : ℂ)] T :=
    eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hFT hn3
  have hT3 : Tcont =ᶠ[𝓝[≠] (3 : ℂ)] T :=
    Filter.mem_of_superset (nhdsWithin_le_nhds hn3) fun s hs => Tcont_eqOn_T hZ1 hZ2 hZ3 hs
  have htop3 : meromorphicOrderAt (F - Tcont) 3 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hFT3, hT3] with s h1 h2
    simp [h1, h2]
  have htop : meromorphicOrderAt (F - Tcont) s₀ = ⊤ :=
    (hF.sub (Tcont_props hZ1 hZ2 hZ3).1).meromorphicOrderAt_eq_top_of_isPreconnected
      (isPreconnected_halfPlane _) h3B hs₀ htop3
  rw [meromorphicOrderAt_eq_top_iff] at htop
  filter_upwards [htop] with s hs
  exact sub_eq_zero.mp hs

end GoldbachBoundaries.Paper2.M1
