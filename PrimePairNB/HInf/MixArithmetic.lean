import PrimePairNB.HInf.MixNonvanishing
import PrimePairNB.HInf.SqMixArithmetic

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory ComplexConjugate
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

/-- At the pinch only, the moving kernel becomes the beta kernel. -/
lemma XcMix_diag (x : ℂ) : XcMix x x = -pairSum x := by
  unfold XcMix pairSum
  congr 1
  apply tsum_congr
  intro p
  have hx : x - p.1.2 = p.1.1 := by linear_combination -p.2.2.2
  simp only [hx, cP, neg_mul_neg, kerG, KerS, betaB]
  simp only [← p.2.2.2, add_sub_cancel_left]

/-- The recurrence identity also holds at positive real part. -/
lemma betaMix_eq_of_re_pos {u : ℂ} (hu : 0 < u.re) : betaMix u = 2 / u := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hGamma : Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hu
  have hrec : Gamma (1 + u) = u * Gamma u := by
    rw [add_comm, Complex.Gamma_add_one u hu0]
  simp only [betaMix, kerG, KerS, add_sub_cancel_left, add_sub_cancel_right,
    Gamma_one, one_mul, mul_one, hrec]
  field_simp
  ring

/-- Nonzero values on the dense arithmetic family; no assertion at every pinch. -/
theorem prop71_mix (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5)
    (hZ6 : Z6) (hB : Bsup < 1) (y ε : ℝ) (hε : 0 < ε) :
    (Fill.arithPoints (fun x => XcMix x x ≠ 0) y ε).Infinite := by
  apply Fill.prop71_arith_of_core (fun x => XcMix x x ≠ 0) ?_ ?_ y ε hε
  · intro x hx
    simp only [XcMix_diag, neg_ne_zero] at hx ⊢
    rw [M2.pairSum_conj hZ1]
    exact (map_ne_zero _).mpr hx
  · intro y ε hy hε hεy hε1
    apply Fill.sqMix_arith_core hZ1 hZ2 hZ4 hZ5 hB betaMix NV_mix
      (fun x => XcMix x x ≠ 0) ?_ hy hε hεy hε1
    intro Y hY
    obtain ⟨H₀, hH₀⟩ := M2.pairSum_ne_zero_of_not_nearBad hZ1 hZ2 hZ6 hB hY
    refine ⟨H₀, fun H hH u hu hu1 hre hre1 hYu hnb hexp => ?_⟩
    rw [XcMix_diag, neg_ne_zero]
    apply hH₀ H hH u hu hu1 hre hre1 hYu hnb
    convert hexp using 2
    rw [betaMix_eq_of_re_pos hre]
    ring

end GoldbachBoundaries.HInf
