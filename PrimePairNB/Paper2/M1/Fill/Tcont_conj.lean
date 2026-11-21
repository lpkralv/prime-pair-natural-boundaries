import PrimePairNB.Paper2.M1.Fill.E2Common
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.Qcont_conj
import PrimePairNB.Paper2.M1.Fill.Rcoef_real_conj
import PrimePairNB.Paper2.M1.Fill.Tc_indep
import PrimePairNB.Paper2.M1.Fill.conj_mem_poleSetQ
import PrimePairNB.Paper2.M1.Fill.exists_adm_reg

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma E2_KerS_conj (s a : ℂ) : KerS (conj s) (conj a) = conj (KerS s a) := by
  simp [KerS, ← map_sub, Gamma_conj]

private lemma E2_Fdelta_conj {δ : ℝ} {a : ℂ} (ha : a ∈ Fdelta δ) : conj a ∈ Fdelta δ :=
  ⟨conj_mem_poleSetQ ha.1, by simpa using ha.2⟩

private lemma E2_Ic_real_norm (c : ℝ) (s : ℂ) : IcQ Qcont c s =
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ, KerS s (c + y * I) * Qcont (c + y * I) * Qcont (s - (c + y * I)) := by
  unfold IcQ VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, ← mul_assoc]
  congr 1
  field_simp

private lemma E2_Ic_conj (hZ1 : Z1) {δ c : ℝ} (h : AdmC δ c) {s : ℂ} (hs : s ∈ RegC δ c) :
    IcQ Qcont c (conj s) = conj (IcQ Qcont c s) := by
  rw [E2_Ic_real_norm, E2_Ic_real_norm, map_mul]
  have hc : conj (1 / (2 * Real.pi) : ℂ) = (1 / (2 * Real.pi) : ℂ) := by
    convert conj_ofReal (1 / (2 * Real.pi)) using 1 <;> push_cast <;> ring
  rw [hc, ← integral_conj]
  congr 1
  rw [← integral_neg_eq_self (fun y : ℝ => conj (KerS s (c + y * I) * Qcont (c + y * I) * Qcont (s - (c + y * I)))) volume]
  apply integral_congr_ae
  filter_upwards [] with y
  let w : ℂ := c + (-y : ℝ) * I
  have hw : w.re = c := by simp [w]
  obtain ⟨hwreg, hswreg⟩ := E2_line_regular hZ1 h hs hw
  have hwc : conj w = c + y * I := by simp [w]
  rw [← hwc, E2_KerS_conj, Qcont_conj hwreg, ← map_sub, Qcont_conj hswreg]
  simp only [map_mul, w]

private lemma E2_term_conj (hZ1 : Z1) {δ c : ℝ} (h : AdmC δ c) {s a : ℂ}
    (hs : s ∈ RegC δ c) (hP : s ∉ Pinch) (ha : a ∈ Fdelta δ) :
    nu c (conj a) (conj s) * Rcoef (conj a) * KerS (conj s) (conj a) * Qcont (conj s - conj a) =
      conj (nu c a s * Rcoef a * KerS s a * Qcont (s - a)) := by
  have hsa := E2_sub_regular hZ1 (E2_reg_re h hs) ha.1 hP
  have hr := Rcoef_real_conj hZ1 ha.1
  have hrc : conj (Rcoef a) = Rcoef a := conj_eq_iff_im.mpr hr.1
  have hn : nu c (conj a) (conj s) = conj (nu c a s) := by
    simp [nu, iverson]
  rw [hn, hr.2, E2_KerS_conj, ← map_sub, Qcont_conj hsa]
  simp only [map_mul, hrc]

/-- **Conjugation symmetry** off `Π` (Z1, Z2, Z3): `T(s̄) = conj T(s)` on `σ > 2` (termwise), and the identity theorem
on the connected set `{σ > 2B_∞} ∖ Π` (complement of a closed discrete, countable set in a half-plane); or directly
from the continuation formula with `Qcont_conj`, `Rcoef_real_conj` and `conj_mem_poleSetQ` (`F_δ` is conjugation-invariant).
Uses: `Tcont_props`, `Tcont_eqOn_T`, `conj_mem_Pinch`, `pinch_locallyFinite`. -/
theorem Tcont_conj (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {s : ℂ} (hs : s ∈ halfPlane (2 * Binf) \ Pinch) :
    Tcont (conj s) = conj (Tcont s) := by
  classical
  by_cases hB : Binf < 1
  · obtain ⟨δ, c, h, hreg⟩ := exists_adm_reg hZ1 hB hs.1
    have hregc : conj s ∈ RegC δ c := by simpa [RegC] using hreg
    have hPc : conj s ∉ Pinch := fun hp => hs.2 (by simpa using conj_mem_Pinch hp)
    rw [Tcont_eq_Tc hZ1 hZ2 hZ3 h hregc hPc, Tcont_eq_Tc hZ1 hZ2 hZ3 h hreg hs.2]
    have hF := (Fdelta_spec hZ1 δ h.1).1
    simp only [Tc, TcQ, finsum_mem_eq_finite_toFinset_sum _ hF, map_add, map_sum]
    rw [E2_Ic_conj hZ1 h hreg]
    congr 1
    apply Finset.sum_bij (fun a _ => conj a)
    · intro a ha
      exact hF.mem_toFinset.mpr (E2_Fdelta_conj (hF.mem_toFinset.mp ha))
    · intro a ha b hb he
      exact (starRingEnd ℂ).injective he
    · intro b hb
      exact ⟨conj b, hF.mem_toFinset.mpr (E2_Fdelta_conj (hF.mem_toFinset.mp hb)), by simp⟩
    · intro a ha
      simpa using E2_term_conj hZ1 h hreg hs.2 (E2_Fdelta_conj (hF.mem_toFinset.mp ha))
  · have he : ∀ z, Tcont z = T z := fun z => Tcont_eq_T_of_not (fun hh => hB hh.1)
    rw [he, he, T, T, Complex.conj_tsum]
    apply tsum_congr
    intro pq
    have hn : (0 : ℝ) ≤ ((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) := Nat.cast_nonneg _
    have harg : (↑((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hn]
      exact ne_of_lt Real.pi_pos
    have hc : conj ((↑((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ)) =
        (↑((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) := by simp
    have hp := Complex.cpow_conj (↑((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) (-s) harg
    rw [hc] at hp
    simpa only [map_mul, Complex.conj_ofReal, map_neg] using
      congrArg (fun z : ℂ => (Real.log (pq.1 : ℕ) : ℂ) * (Real.log (pq.2 : ℕ) : ℂ) * z) hp

end GoldbachBoundaries.Paper2.M1
