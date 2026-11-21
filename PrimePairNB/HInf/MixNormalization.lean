import PrimePairNB.HInf.MixMellin
import PrimePairNB.HInf.MixSheetAnalytic
import PrimePairNB.HInf.Fill.germ_const
import PrimePairNB.Paper2.M1.Fill.one_add_cpow_neg_eq_verticalIntegral'

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.HInf.Fill
namespace GoldbachBoundaries.HInf.MixProof

/-- Mellin–Barnes representation of the mixed prime series. -/
theorem MixSer_MB {s : ℂ} {c : ℝ} (hc1 : 1 < c) (hc2 : c < s.re - 1) :
    MixSer s = VerticalIntegral' (fun z => kerG z s * P z * Q (s - z)) c := by
  have hc0 : 0 < c := by linarith
  have hcs : c < s.re := by linarith
  have h := (tsum_eq_verticalIntegral'_two_weights M4b.primeWeight_one M4b.primeWeight_log
    hc1 hc2 (M1.integrable_KerS_line hc0 hcs)
    (fun t ht => (M1.one_add_cpow_neg_eq_verticalIntegral' hc0 hcs ht).2)).2.2
  simp only [Complex.ofReal_one, one_mul, M4b.primeSum_one, M4b.primeSum_log] at h
  simp only [kerG]
  rw [← h]
  unfold MixSer Dser Wlogq WG
  apply tsum_congr
  intro pq
  rw [M4b.A_add_cpow_primes]
  ring

/-- Each mixed sheet agrees with the defining series to the right of 2. -/
theorem Dth_eq (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hK : IsPinchKernel kerG ⊤ G) (κ : ℝ) {v : ℂ} (h2 : 2 < v.re) :
    DthMix κ v = MixSer v := by
  have hv : v ∈ VInf ⊤ :=
    (mem_Om_of_two_lt hZ1 (κ := κ) ⟨by linarith, EReal.coe_lt_top _⟩ h2).1
  let c : ℝ := v.re / 2
  have hc1 : 1 < c := by dsimp [c]; linarith
  have hc2 : c < v.re - 1 := by dsimp [c]; linarith
  rw [Dth_eq_graphInt hZ1 hZ2 hZ3 hK hv (isSeparating_line hZ1 κ hc1 hc2),
    graphInt_line, MixSer_MB hc1 hc2]
  have hpt : ∀ y : ℝ, pairIntegrandMix κ v ((c : ℂ) + (y : ℂ) * I) =
      kerG ((c : ℂ) + (y : ℂ) * I) v * P ((c : ℂ) + (y : ℂ) * I) * Q (v - ((c : ℂ) + (y : ℂ) * I)) := by
    intro y
    have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
    unfold pairIntegrandMix
    rw [Pth_eq_P κ (by rw [hre]; exact hc1),
      TIdentity.Qcont_eq_Q_of_one_lt (by rw [sub_re, hre]; linarith)]
  simp only [VerticalIntegral', VerticalIntegral, hpt]

end GoldbachBoundaries.HInf.MixProof
