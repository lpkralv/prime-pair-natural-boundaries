import PrimePairNB.ThmA.G15_Kernel

/-!
# shared facts about `F₀(t) = ∑_p e^{-pt}`

Helpers live in the namespace `GoldbachBoundaries.ThmA.GroupE`.

* `F0_nonneg`, `F0_continuousOn`, `F0_le_exp`: basic properties (copy of the lemma in `TIdentity/G9a_FwBasic.lean` without the
  weight `log p`).
* `mellin_F0`, `mellin_F0_sq`: Mellin transforms of `F₀`, `F₀²`, with convergence (copies of
  `TIdentity.mellin_Fw`, `mellin_Fw_sq`).
* `differentiable_e0inf`: `e_∞` is entire (as `TIdentity.differentiable_e1`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

namespace GroupE

-- Adapted from TIdentity/Basic.lean and G9a_FwBasic.lean, with unit weights.
lemma f0_summable_exp_neg {δ : ℝ} (hδ : 0 < δ) :
    Summable fun p : Nat.Primes => Real.exp (-((p : ℕ) * δ)) := by
  have h := (Real.summable_pow_mul_exp_neg_nat_mul 0 hδ).subtype {n : ℕ | n.Prime}
  refine h.congr fun p => ?_
  dsimp only [Function.comp_apply]
  simp only [pow_zero, one_mul]
  congr 1
  ring

theorem F0_nonneg (t : ℝ) : 0 ≤ F0 t := by
  exact tsum_nonneg fun _ => (Real.exp_pos _).le

theorem F0_continuousOn : ContinuousOn F0 (Ioi 0) := by
  intro t ht
  have ht' : 0 < t / 2 := by have := mem_Ioi.mp ht; linarith
  have hcont : ContinuousOn F0 (Ioi (t / 2)) := by
    refine continuousOn_tsum (fun p => by fun_prop) (f0_summable_exp_neg ht')
      fun p x hx => ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hx' : t / 2 < x := hx
    have : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
    nlinarith
  exact (hcont.continuousAt (Ioi_mem_nhds (by have := mem_Ioi.mp ht; linarith))).continuousWithinAt

theorem F0_le_exp : ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → F0 t ≤ C * Real.exp (-t) := by
  refine ⟨Real.exp 1 * ∑' p : Nat.Primes, Real.exp (-((p : ℕ) * 1)), fun t ht => ?_⟩
  have hs1 := f0_summable_exp_neg (δ := 1) one_pos
  have hst := f0_summable_exp_neg (δ := t) (by linarith)
  rw [show Real.exp 1 * (∑' p : Nat.Primes, Real.exp (-((p : ℕ) * 1))) *
      Real.exp (-t) = ∑' p : Nat.Primes, Real.exp (-t) * (Real.exp 1 *
        Real.exp (-((p : ℕ) * 1))) by
    rw [tsum_mul_left, tsum_mul_left]; ring]
  refine Summable.tsum_le_tsum (fun p => ?_) hst ((hs1.mul_left _).mul_left _)
  have hp : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.one_lt.le
  calc Real.exp (-((p : ℕ) * t))
      ≤ Real.exp (-t + 1 + -((p : ℕ) * 1)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

theorem mellin_F0 {z : ℂ} (hz : 1 < z.re) :
    MellinConvergent (fun t => (F0 t : ℂ)) z ∧
      mellin (fun t => (F0 t : ℂ)) z = Gamma z * P z := by
  have hz0 : 0 < z.re := by linarith
  have hw : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) := fun p => by
    exact_mod_cast p.prop.pos
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun p : Nat.Primes ↦
      (1 : ℂ) * Real.exp (-((p : ℕ) : ℝ) * t)) (F0 t : ℂ) := fun t ht ↦ by
    have h := (f0_summable_exp_neg (mem_Ioi.mp ht)).hasSum
    rw [← Complex.hasSum_ofReal] at h
    convert h using 1
    · funext p
      simp only [one_mul, neg_mul]
    · rfl
  have hFc : ContinuousOn (fun t => (F0 t : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn F0_continuousOn
  have hnorm : ∀ p : Nat.Primes, ‖(1 : ℂ)‖ / ((p : ℕ) : ℝ) ^ z.re =
      ‖((p : ℕ) : ℂ) ^ (-z)‖ := fun p ↦ by
    rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re, Real.rpow_neg (Nat.cast_nonneg _)]
    simp only [norm_one, one_div]
  have h_sum : Summable fun p : Nat.Primes ↦
      ‖(1 : ℂ)‖ / ((p : ℕ) : ℝ) ^ z.re := by
    simp_rw [hnorm]; exact summable_norm_P_terms hz
  obtain ⟨hconv, hval⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp hw hz0 hF hFc h_sum
  refine ⟨hconv, ?_⟩
  rw [← hval.tsum_eq, P, ← tsum_mul_left]
  refine tsum_congr fun p ↦ ?_
  rw [ofReal_natCast, cpow_neg]
  simp only [mul_one, div_eq_mul_inv]

theorem mellin_F0_sq {s : ℂ} (hs : 2 < s.re) :
    MellinConvergent (fun t => ((F0 t ^ 2 : ℝ) : ℂ)) s ∧
      mellin (fun t => ((F0 t ^ 2 : ℝ) : ℂ)) s = Gamma s * G s := by
  -- Adapted from TIdentity/G9c_MellinFwSq.lean, with unit coefficients.
  set σ := s.re with hσ
  have hs0 : 0 < σ := by linarith
  have hpos : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) := fun p => by
    exact_mod_cast p.prop.pos
  set w : Nat.Primes × Nat.Primes → ℝ := fun pq => ((pq.1 : ℕ) : ℝ) + ((pq.2 : ℕ) : ℝ) with hwdef
  have hw : ∀ pq, 0 < w pq := fun pq => add_pos (hpos _) (hpos _)
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun pq ↦ (1 : ℂ) * Real.exp (-w pq * t))
      ((F0 t ^ 2 : ℝ) : ℂ) := fun t ht ↦ by
    have hf := f0_summable_exp_neg (mem_Ioi.mp ht)
    have hnn : ∀ p : Nat.Primes, 0 ≤ Real.exp (-((p : ℕ) * t)) := fun p => (Real.exp_pos _).le
    have hprod := hf.hasSum.mul hf.hasSum (hf.mul_of_nonneg hf hnn hnn)
    rw [← Complex.hasSum_ofReal] at hprod
    convert hprod using 1
    · funext pq
      simp only [hwdef, one_mul]
      rw [show -(((pq.1 : ℕ) : ℝ) + ((pq.2 : ℕ) : ℝ)) * t =
        -(((pq.1 : ℕ) : ℝ) * t) + -(((pq.2 : ℕ) : ℝ) * t) by ring, Real.exp_add]
    · rw [sq]; rfl
  have hFc : ContinuousOn (fun t => ((F0 t ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn (F0_continuousOn.pow 2)
  have key : ∀ x y : ℝ, 0 < x → 0 < y → x ^ (σ / 2) * y ^ (σ / 2) ≤ (x + y) ^ σ := by
    intro x y hx hy
    calc x ^ (σ / 2) * y ^ (σ / 2) = (x * y) ^ (σ / 2) := (Real.mul_rpow hx.le hy.le).symm
      _ ≤ ((x + y) ^ (2 : ℝ)) ^ (σ / 2) :=
          Real.rpow_le_rpow (by positivity) (by rw [Real.rpow_two]; nlinarith) (by linarith)
      _ = (x + y) ^ σ := by rw [← Real.rpow_mul (by positivity)]; ring_nf
  set g : Nat.Primes → ℝ := fun p => 1 / ((p : ℕ) : ℝ) ^ (σ / 2) with hg
  have hg_sum : Summable g := by
    have h := summable_norm_P_terms (z := ((σ / 2 : ℝ) : ℂ)) (by simp only [ofReal_re]; linarith)
    refine h.congr fun p => ?_
    rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re, ofReal_re,
      Real.rpow_neg (Nat.cast_nonneg _)]
    simp only [hg, one_div]
  have hg_nn : 0 ≤ g := fun p => by dsimp [g]; positivity
  have h_sum : Summable fun pq ↦ ‖(1 : ℂ)‖ / (w pq) ^ σ := by
    refine (hg_sum.mul_of_nonneg hg_sum hg_nn hg_nn).of_nonneg_of_le
      (fun pq => div_nonneg (norm_nonneg _) (by have := hw pq; positivity)) fun pq => ?_
    simp only [hwdef, hg, norm_one, div_mul_div_comm, one_mul]
    exact div_le_div_of_nonneg_left zero_le_one
      (by have := hpos pq.1; have := hpos pq.2; positivity) (key _ _ (hpos _) (hpos _))
  obtain ⟨hconv, hval⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp hw hs0 hF hFc h_sum
  refine ⟨hconv, ?_⟩
  rw [← hval.tsum_eq, G, ← tsum_mul_left]
  refine tsum_congr fun pq ↦ ?_
  have hcast : ((w pq : ℝ) : ℂ) = ((((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ)) : ℂ) := by
    simp only [hwdef]; push_cast; ring
  rw [hcast, cpow_neg]
  simp only [mul_one, div_eq_mul_inv]

theorem differentiable_e0inf : Differentiable ℂ e0inf := by
  obtain ⟨C, hC⟩ := F0_le_exp
  refine TIdentity.differentiable_integral_Ioi_cpow (C := C) ?_ fun t ht => ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (F0_continuousOn.mono fun t ht => lt_trans one_pos (mem_Ioi.mp ht))).aestronglyMeasurable
        measurableSet_Ioi
  · rw [Complex.norm_real, Real.norm_of_nonneg (F0_nonneg t)]
    exact hC t (le_of_lt ht)

end GroupE

end GoldbachBoundaries.ThmA
