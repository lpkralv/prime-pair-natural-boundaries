import PrimePairNB.Paper2.M4b.Rising
import PrimePairNB.Paper2.M4b.Fill.DCommon
import PrimePairNB.Paper2.M4b.Fill.kerS_basic
import PrimePairNB.Paper2.M4b.Fill.E1Common

noncomputable section
open Complex
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **(R) for `G`** (no hypothesis). `WG = Wrise 1 (fun _ _ _ => 1)` (`WG_eq_Wrise`, as functions) and
`wtd (fun _ => 1) W = W`, `P = primeSum (fun _ => 1)` (`primeSum_one`). Absolute convergence:
`rising_summable_eq` (`primeWeight_one`) at `s ∈ R_L = {σ > 2}` (`idL_RL_eq`). Holomorphy: `rising_differentiableOn`
(`differentiableOn_one_cf`). Reality: for real `x`, `(p+q)^{-x}` is real (`Complex.ofReal_cpow`, `natCast` base
`≥ 0`), so `(Dser WG x).im = ∑' (·).im = 0` (`Complex.im_tsum` if summable; the junk `tsum` is `0` otherwise). The
identity: `rising_summable_eq` on `R_L ∩ D_L = {2 < σ < 3}` (`M4a.app_idL`), with the integrands equal pointwise
(`kerG_eq_krise`). -/
theorem hypR_kerG_WG : HypR Aff.idL kerG WG P := by
  rw [← primeSum_one]
  apply E1_hypR_rising primeWeight_one 1 (fun _ _ _ => 1) differentiableOn_one_cf
  · intro s pq
    simp [wtd, ← WG_eq_Wrise, WT]
  · intro z s _ _
    exact kerG_eq_krise z s
  · intro x hx pq
    have he := E1_cpow_real ((pq.1 : ℕ) + (pq.2 : ℕ)) (-x)
    simpa [WG, WT, mul_im] using he

end GoldbachBoundaries.Paper2.M4b
