import PrimePairNB.TIdentity.G9b_MellinFw
import PrimePairNB.TIdentity.G9c_MellinFwSq

/-!
# `Γ(s)T(s) = 1/(s-2) + 2m₁(s-1) + R(s) + E₂(s)` on `Re s > 2`

Uses `mellin_Fw` (at `s - 1`) and `mellin_Fw_sq`. The elementary facts about `t^r` on
`(0, 1]` are local `have`s here (the same facts are top-level lemmas in `G9e_SplitQ.lean`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- **Splitting the Mellin integral of `F²` at `t = 1`** (step (3):
`∫_0^1 F² t^{s-1} = 1/(s-2) + 2 m₁(s-1) + R(s)`), on `Re s > 2`. Unconditional.

Proof sketch. As `Gamma_mul_Q_eq_split`, from `mellin_Fw_sq`. On `(0,1]`,
`F² = t^{-2} + 2 h t^{-1} + h²`. Integrability on `(0,1]` for `Re s > 2`: `t^{s-3}` (`Re > -1`);
`h t^{s-2} = F t^{s-2} - t^{s-3}` (`F t^{(s-1)-1}` is integrable by `mellin_Fw` at `s - 1`);
`h² t^{s-1} = F² t^{s-1} - 2 F t^{s-2} + t^{s-3}`. Then `∫_0^1 t^{s-3} = 1/(s-2)`, and
`∫_0^1 h t^{-1} t^{s-1} = m₁(s - 1)` (`t^{-1} t^{s-1} = t^{s-2}` for `t > 0`). -/
theorem Gamma_mul_T_eq_split {s : ℂ} (hs : 2 < s.re) :
    Gamma s * T s = 1 / (s - 2) + 2 * m1 (s - 1) + Rr s + E2 s := by
  -- `t^r` on `(0, 1]`, `Re r > -1`: integrable, with integral `1/(r+1)`.
  have hpowI : ∀ r : ℂ, -1 < r.re → IntegrableOn (fun t : ℝ => (t : ℂ) ^ r) (Ioc (0 : ℝ) 1) :=
    fun r hr => (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' hr)
  have hpowV : ∀ r : ℂ, -1 < r.re → ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ r = 1 / (r + 1) := by
    intro r hr
    have hr1 : r + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr)]
    simp [Complex.zero_cpow hr1]
  -- For `t > 0`: `t^{s-1} = t^{s-3} t²` and `t^{(s-1)-1} = t^{s-3} t`.
  have hadd : ∀ t : ℝ, 0 < t → ∀ w : ℂ, (t : ℂ) ^ (w + 1) = (t : ℂ) ^ w * t := by
    intro t ht w
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
  have hc1 : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (s - 1 - 1) = (t : ℂ) ^ (s - 3) * t := by
    intro t ht
    rw [← hadd t ht]
    ring_nf
  have hc2 : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 3) * t * t := by
    intro t ht
    rw [← hc1 t ht, ← hadd t ht]
    ring_nf
  obtain ⟨hconv2, hmel2⟩ := mellin_Fw_sq hs
  have hs1 : 1 < (s - 1).re := by simp; linarith
  have hconv1 := (mellin_Fw hs1).1
  -- A: `t^{s-3}`.
  have hA : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 3)) (Ioc (0 : ℝ) 1) :=
    hpowI _ (by simp; linarith)
  -- B: `h(t) t^{(s-1)-1} = F(t) t^{(s-1)-1} - t^{s-3}`.
  have hB : IntegrableOn (fun t : ℝ => (hErr t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) (Ioc (0 : ℝ) 1) := by
    refine ((hconv1.mono_set Ioc_subset_Ioi_self).sub hA).congr_fun (fun t ht => ?_)
      measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    simp only [Pi.sub_apply, hErr, smul_eq_mul, hc1 t ht0]
    push_cast
    field_simp
  -- Pointwise expansion `t^{s-1} F² = h² t^{s-1} + 2 h t^{(s-1)-1} + t^{s-3}` on `(0, 1]`.
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • ((Fw t ^ 2 : ℝ) : ℂ)
      = ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)
        + 2 * ((hErr t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) + (t : ℂ) ^ (s - 3) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    simp only [hErr, smul_eq_mul, hc1 t ht0, hc2 t ht0]
    push_cast
    field_simp
    ring
  -- C: `h² t^{s-1} = t^{s-1} F² - 2 h t^{(s-1)-1} - t^{s-3}`.
  have hC : IntegrableOn (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) := by
    refine (((hconv2.mono_set Ioc_subset_Ioi_self).sub (hB.const_mul 2)).sub hA).congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply, hpt t ht]
    ring
  have hsplit : ∫ t in Ioc (0 : ℝ) 1, (((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)
        + 2 * ((hErr t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) + (t : ℂ) ^ (s - 3))
      = Rr s + 2 * m1 (s - 1) + 1 / (s - 2) := by
    have hB2 : IntegrableOn (fun t : ℝ => 2 * ((hErr t : ℂ) * (t : ℂ) ^ (s - 1 - 1)))
        (Ioc (0 : ℝ) 1) := hB.const_mul 2
    have hCB : IntegrableOn (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)
        + 2 * ((hErr t : ℂ) * (t : ℂ) ^ (s - 1 - 1))) (Ioc (0 : ℝ) 1) := hC.add hB2
    rw [integral_add hCB hA, integral_add hC hB2,
      integral_const_mul, hpowV _ (by simp; linarith)]
    simp only [m1, Rr]
    ring_nf
  rw [← hmel2, mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hconv2.mono_set Ioc_subset_Ioi_self) (hconv2.mono_set (Ioi_subset_Ioi zero_le_one)),
    setIntegral_congr_fun measurableSet_Ioc hpt, hsplit]
  have hE : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • ((Fw t ^ 2 : ℝ) : ℂ) = E2 s := by
    simp only [E2, smul_eq_mul, mul_comm]
  rw [hE]
  ring

end TIdentity

end GoldbachBoundaries
