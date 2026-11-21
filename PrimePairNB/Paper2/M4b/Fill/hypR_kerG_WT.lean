import PrimePairNB.Paper2.M4b.Rising
import PrimePairNB.Paper2.M4b.Fill.DCommon
import PrimePairNB.Paper2.M4b.Fill.kerS_basic
import PrimePairNB.Paper2.M4b.Fill.E1Common

noncomputable section
open Complex
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **(R) for `T`** (no hypothesis). As `hypR_kerG_WG` with `ω = log` (`primeWeight_log`, `primeSum_log`).
(Alternatively the identity is M1's `T_eq_verticalIntegral'_KerS` and the holomorphy M1's
`T_differentiableOn`.) -/
theorem hypR_kerG_WT : HypR Aff.idL kerG WT Q := by
  rw [← primeSum_log]
  apply E1_hypR_rising primeWeight_log 1 (fun _ _ _ => 1) differentiableOn_one_cf
  · intro s pq
    simp [wtd, ← WG_eq_Wrise, WT]
  · intro z s _ _
    exact kerG_eq_krise z s
  · intro x hx pq
    have he : ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-(x : ℂ))).im = 0 := by
      simpa only [ofReal_neg] using E1_cpow_real ((pq.1 : ℕ) + (pq.2 : ℕ)) (-x)
    simp only [WT, WG, mul_im, ofReal_re, ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero, he]

end GoldbachBoundaries.Paper2.M4b
