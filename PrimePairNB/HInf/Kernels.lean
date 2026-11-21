import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch
import PrimePairNB.HInf.Fill.pinch_countable
import PrimePairNB.HInf.Fill.Jv_analyticOn
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.deriv_Xc_G
import PrimePairNB.HInf.Fill.deriv_Xc_S
import PrimePairNB.HInf.Fill.isPinchKernel_G
import PrimePairNB.HInf.Fill.isPinchKernel_S

/-!
# HInf: the two kernels, `J_{ab}`, `X_x`, `M_x`

`isPinchKernel_G` and `isPinchKernel_S` are (K1) to (K3). Reuse: `Paper2.M4b.kerG_H2a` for (K1), `Paper2.M4b.kerS_basic`,
`Paper2.M4b.hypR_kerG_WG`, `Paper2.M4b.hypR_kerS` for (K3), both already free of RH.
(K2): for `G` from (Z6), on all of `Re v > 1`. For `S` elementary from
`K(w) = (1 - w)π / sin πw` (`norm_KS_le` in `Arith.lean` has the far form), so no (Z6). So Stirling is needed for `G` only.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-- (K1) to (K3) for `G`: `𝒱 = {Re v > 1}`. -/
theorem isPinchKernel_G (hZ6 : Z6) : IsPinchKernel kerG ⊤ G :=
  @Fill.isPinchKernel_G hZ6

/-- (K1) to (K3) for `S`: `𝒱 = {1 < Re v < 3}`. The one place `Re v < 3` is used is (K1). -/
theorem isPinchKernel_S : IsPinchKernel kS 3 DS :=
  @Fill.isPinchKernel_S

end GoldbachBoundaries.HInf
