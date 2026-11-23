import PrimePairNB.HInf.MixBoundaryProof
import PrimePairNB.HInf.MixFollowCommon
import PrimePairNB.HInf.MixNonvacuity

noncomputable section

open Complex Filter Topology Set Metric
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- A terminal mixed-series germ cannot extend meromorphically across `Re s = 1`,
including when the path ends at a catalogue point. -/
theorem no_extension_any_path_mix (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6)
    {γ : C(unitInterval, ℂ)} (h0 : 2 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm MixSer γ g)
    (y r : ℝ) (hr : 0 < r) (h1 : γ 1 ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g (γ 1) (ball (1 + (y : ℂ) * I) r) :=
  Follow.no_extension_any_path hH hZ1 (fun _ hs => MixSer_analyticAt hs)
    (fun g s had => MixProof.boundary_mix_aux hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6
      ((MixProof.admMix_iff g s).mpr had))
    h0 hg y r hr h1

end GoldbachBoundaries.HInf.Fill
