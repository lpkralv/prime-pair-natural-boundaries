import PrimePairNB.ThmA.Fill.ECommonF0

/-! Mellin transforms and inversion, adapted from TIdentity/G9d_MellinInversion.lean. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

lemma f0_norm_P_line {c : ℝ} (hc : 1 < c) (y : ℝ) :
    ‖P (c + y * I)‖ ≤ ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-(c : ℂ))‖ := by
  have hre : 1 < ((c : ℂ) + y * I).re := by simpa using hc
  rw [P]
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_P_terms hre)) (le_of_eq ?_)
  refine tsum_congr fun p => ?_
  rw [norm_natCast_cpow_of_pos p.prop.pos, norm_natCast_cpow_of_pos p.prop.pos]
  simp

lemma f0_integrable_Gamma_mul_P {c : ℝ} (hc : 1 < c) :
    Integrable fun y : ℝ => Gamma (c + y * I) * P (c + y * I) := by
  set K : ℝ := ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-(c : ℂ))‖
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  refine TIdentity.integrable_Gamma_mul_of_bound (by linarith) ?_ (K := K) fun y => ?_
  · rw [continuous_iff_continuousAt]
    intro y
    have hre : (c : ℂ) + y * I ∈ halfPlane 1 := by
      change 1 < ((c : ℂ) + y * I).re
      simpa using hc
    exact ((hasDerivAt_P hre).continuousAt).comp
      (f := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop)
  · calc ‖P (c + y * I)‖ ≤ K := f0_norm_P_line hc y
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * (1 + |y|) := mul_le_mul_of_nonneg_left (by linarith [abs_nonneg y]) hK0

lemma f0_eq_verticalIntegral {c t : ℝ} (hc : 1 < c) (ht : 0 < t) :
    (F0 t : ℂ) = VerticalIntegral' (fun z => Gamma z * P z * (t : ℂ) ^ (-z)) c := by
  have hmel : ∀ y : ℝ, mellin (fun t => (F0 t : ℂ)) (c + y * I) =
      Gamma (c + y * I) * P (c + y * I) := by
    intro y
    exact (mellin_F0 (by simpa using hc)).2
  have hconv : MellinConvergent (fun t => (F0 t : ℂ)) (c : ℂ) :=
    (mellin_F0 (by simpa using hc)).1
  have hvi : VerticalIntegrable (mellin (fun t => (F0 t : ℂ))) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact f0_integrable_Gamma_mul_P hc
  have hcont : ContinuousAt (fun t => (F0 t : ℂ)) t :=
    continuous_ofReal.continuousAt.comp
      (F0_continuousOn.continuousAt (Ioi_mem_nhds ht))
  rw [← mellinInv_mellin_eq c _ ht hconv hvi hcont, mellinInv, VerticalIntegral', VerticalIntegral]
  simp_rw [hmel, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc]
  congr 1
  · have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
    field_simp
    push_cast
    ring_nf
    exact mul_inv_cancel₀ hpi
  · apply integral_congr_ae
    filter_upwards [] with y
    exact mul_comm _ _

end GroupE

/-- **Mellin facts for `F₀`** (the Mellin transforms for `P` and `G`). Unconditional.

Sketch. Copy of `mellin_Fw`, `mellin_Fw_sq` and `Fw_eq_verticalIntegral'` in
`TIdentity/` with the weight `log p` removed: `mellin_convergent_and_hasSum_of_exp`
(`TIdentity/Basic.lean`) over `Nat.Primes` and over `Nat.Primes × Nat.Primes` (`F₀² = ∑_{p,q}
e^{-(p+q)t}`), then `mellinInv_mellin_eq`, with vertical integrability from the decay of `Γ`
(`norm_Gamma_mul_one_add_abs_im_pow_le`) and `|P(c+iy)| ≤ P(c)`. -/
theorem F0_mellin :
    (∀ z : ℂ, 1 < z.re → ∫ t in Ioi (0 : ℝ), (F0 t : ℂ) * (t : ℂ) ^ (z - 1) = Gamma z * P z) ∧
    (∀ s : ℂ, 2 < s.re →
      ∫ t in Ioi (0 : ℝ), ((F0 t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) = Gamma s * G s) ∧
    (∀ c t : ℝ, 1 < c → 0 < t →
      (F0 t : ℂ) = VerticalIntegral' (fun z => Gamma z * P z * (t : ℂ) ^ (-z)) c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    simpa only [mellin, smul_eq_mul, mul_comm] using (GroupE.mellin_F0 hz).2
  · intro s hs
    simpa only [mellin, smul_eq_mul, mul_comm] using (GroupE.mellin_F0_sq hs).2
  · intro c t hc ht
    exact GroupE.f0_eq_verticalIntegral hc ht

end GoldbachBoundaries.ThmA
