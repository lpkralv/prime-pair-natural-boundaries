import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.rotation
import PrimePairNB.HInf.Fill.sumMc_mem

/-!
# `germFam_slope`

By `rotation` and `sumMc_mem` (statements in `Rotation.lean`), a change of slope
changes `D^θ` by a member of `𝓜`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **One slope suffices**: for any `κ'` with `q ∈ Ω_κ'`, a member of `𝔊(q)` has the form
`D^{κ'} + m + C` with that `κ'`. -/
theorem germFam_slope (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {k : ℂ → ℂ → ℂ} {top : EReal} {D : ℂ → ℂ}
    (hK : IsPinchKernel k top D) {C q : ℂ} {f : ℂ → ℂ} (h : GermFam k top C q f) {κ' : ℝ} (hκ' : q ∈ Om κ' top) :
    ∃ m ∈ MSpanK k, f =ᶠ[𝓝 q] fun v => Dth k κ' v + m v + C := by
  obtain ⟨κ, hκ, m, hm, hf⟩ := h
  rcases lt_trichotomy κ κ' with hlt | rfl | hlt
  · obtain ⟨hfin, hrot⟩ := rotation hZ1 hZ2 hZ3 hK hlt hκ hκ'
    refine ⟨m - sumMc k (sector q κ κ'), sub_mem hm (sumMc_mem k hfin), ?_⟩
    filter_upwards [hf, hrot] with v hv hr
    rw [hv, hr, Pi.sub_apply]
    ring
  · exact ⟨m, hm, hf⟩
  · obtain ⟨hfin, hrot⟩ := rotation hZ1 hZ2 hZ3 hK hlt hκ' hκ
    refine ⟨m + sumMc k (sector q κ' κ), add_mem hm (sumMc_mem k hfin), ?_⟩
    filter_upwards [hf, hrot] with v hv hr
    rw [hv, hr, Pi.add_apply]
    ring

end GoldbachBoundaries.HInf.Fill
