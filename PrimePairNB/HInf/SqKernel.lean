import PrimePairNB.HInf.SqDefs
import PrimePairNB.HInf.Fill.isPinchKernel_G

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2
namespace GoldbachBoundaries.HInf

/-- Scaling the beta kernel also scales its vertical decay rate. -/
lemma kSq_eq_scaled_kerG (z v : ℂ) : kSq z v = (1 / 2) * kerG (z / 2) (v / 2) := by
  simp [kSq, kerSq, kerG, KerS]
  ring

/-- The square kernel is holomorphic on the whole pinch half-plane. -/
lemma kSq_holo : DifferentiableOn ℂ (fun p : ℂ × ℂ => kSq p.1 p.2) (domK ⊤) := by
  rintro ⟨z, v⟩ ⟨hv, hz0, hz1⟩
  have hd1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (q.1 / 2)) (z, v) :=
    (M4b.FillD.differentiableAt_Gamma_of_re_pos (w := z / 2)
      (by simp; linarith)).comp (z, v) (by fun_prop)
  have hd2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (q.2 / 2 - q.1 / 2)) (z, v) :=
    (M4b.FillD.differentiableAt_Gamma_of_re_pos (w := v / 2 - z / 2)
      (by simp; linarith)).comp (z, v) (by fun_prop)
  have hd3 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (q.2 / 2)) (z, v) :=
    (M4b.FillD.differentiableAt_Gamma_of_re_pos (w := v / 2)
      (by simp; linarith [hv.1])).comp (z, v) (by fun_prop)
  have hne : Gamma (v / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [hv.1])
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt ℂ (fun q : ℂ × ℂ =>
    (1 / 2 : ℂ) * Gamma (q.1 / 2) * Gamma (q.2 / 2 - q.1 / 2) / Gamma (q.2 / 2)) (z, v)
  simp only [div_eq_mul_inv _ (Gamma _)]
  exact ((hd1.const_mul (1 / 2 : ℂ)).mul hd2).mul (hd3.inv hne)

lemma decay_kSq (hZ6 : Z6) (C : Set ℂ) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ v ∈ C, ∀ x y : ℝ, ε ≤ x → x ≤ v.re - ε →
      ‖kSq ((x : ℂ) + (y : ℂ) * I) v‖ ≤ M / (1 + |y|) ^ 2 := by
  obtain ⟨M, hM⟩ := Fill.decay_kerG hZ6 ((fun v : ℂ => v / 2) '' C)
    (hC.image (by fun_prop)) (ε / 2) (by linarith)
  refine ⟨2 * max M 0, fun v hv x y hx1 hx2 => ?_⟩
  have h := hM (v / 2) ⟨v, hv, rfl⟩ (x / 2) (y / 2) (by linarith)
    (by simp; linarith)
  have he : ((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I =
      ((x : ℂ) + (y : ℂ) * I) / 2 := by push_cast; ring
  rw [he] at h
  rw [kSq_eq_scaled_kerG, norm_mul]
  norm_num only [norm_div, norm_one, norm_ofNat] at *
  have hab : |y / 2| = |y| / 2 := by rw [abs_div]; norm_num
  rw [hab] at h
  calc
    1 / 2 * ‖kerG (((x : ℂ) + (y : ℂ) * I) / 2) (v / 2)‖
        ≤ 1 / 2 * (max M 0 / (1 + |y| / 2) ^ 2) := by
          gcongr
          exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    _ ≤ 2 * max M 0 / (1 + |y|) ^ 2 := by
      have hm : 0 ≤ max M 0 := le_max_right _ _
      have hy : 0 ≤ |y| := abs_nonneg _
      rw [show (1 / 2 : ℝ) * (max M 0 / (1 + |y| / 2) ^ 2) =
        max M 0 / (2 * (1 + |y| / 2) ^ 2) by field_simp]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_nonneg hm hy]

/-- Auxiliary full-domain instance, used to carry paths with arbitrary rightward excursions. -/
theorem isPinchKernel_Sq_top (hZ6 : Z6) : IsPinchKernel kSq ⊤ DSq := by
  refine ⟨le_top, kSq_holo, fun C hC _ ε hε => decay_kSq hZ6 C hC ε hε, ?_⟩
  intro v h2 h3 c hc1 hc2
  have happ : Aff.twoL.app (v / 2) = v := by simp [Aff.app, Aff.twoL]; ring
  have h := M4b.hypR_kerSq.2.2.2 (v / 2)
    ⟨by show 2 < (Aff.twoL.app (v / 2)).re; rw [happ]; exact h2,
      by show 1 < (Aff.twoL.app (v / 2)).re ∧ (Aff.twoL.app (v / 2)).re < 3
         rw [happ]; exact ⟨by linarith, h3⟩⟩ c hc1 (by rw [happ]; exact hc2)
  simpa only [happ, DSq, kSq] using h

end GoldbachBoundaries.HInf
