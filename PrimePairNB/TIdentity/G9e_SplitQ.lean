import PrimePairNB.TIdentity.G9b_MellinFw

/-!
# `Γ(z)Q(z) = 1/(z-1) + m₁(z) + e₁(z)` on `Re z > 1`

Uses `mellin_Fw`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- `t ↦ t^r` is integrable on `(0, 1]` for `Re r > -1`. -/
theorem integrableOn_Ioc_cpow_of_neg_one_lt {r : ℂ} (hr : -1 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ r) (Ioc (0 : ℝ) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_cpow' hr)

/-- `∫_0^1 t^r dt = 1/(r+1)` for `Re r > -1`. -/
theorem integral_Ioc_cpow_of_neg_one_lt {r : ℂ} (hr : -1 < r.re) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ r = 1 / (r + 1) := by
  have hr1 : r + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr)]
  simp [Complex.zero_cpow hr1]

/-- For `t > 0`, `t^(w+1) = t^w * t`. -/
theorem ofReal_cpow_add_one {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t : ℂ) ^ (w + 1) = (t : ℂ) ^ w * t := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]

/-- On `(0, 1]` and `Re z > 1`: `t^{z-1} F(t)` is integrable. (From `mellin_Fw`.) -/
theorem integrableOn_Ioc_cpow_smul_Fw {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • (Fw t : ℂ)) (Ioc (0 : ℝ) 1) :=
  (mellin_Fw hz).1.mono_set Ioc_subset_Ioi_self

/-- On `(0, 1]` and `Re z > 1`: `h(t) t^{z-1}` is integrable. -/
theorem integrableOn_Ioc_hErr_mul_cpow {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun t : ℝ => (hErr t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc (0 : ℝ) 1) := by
  have h1 := integrableOn_Ioc_cpow_smul_Fw hz
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 2)) (Ioc (0 : ℝ) 1) :=
    integrableOn_Ioc_cpow_of_neg_one_lt (by simp; linarith)
  refine (h1.sub h2).congr_fun (fun t ht => ?_) measurableSet_Ioc
  have ht0 : 0 < t := ht.1
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hc : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ (z - 2) * t := by
    rw [← ofReal_cpow_add_one ht0]; ring_nf
  simp only [Pi.sub_apply, hErr, smul_eq_mul, hc]
  push_cast
  field_simp

/-- **Splitting the Mellin integral of `F` at `t = 1`** (step (2):
`∫_0^1 F t^{z-1} = Γ(z)Q(z) - e₁(z)` and `= 1/(z-1) + m₁(z)`), on `Re z > 1`. Unconditional.

Proof sketch. `mellin F z = ∫_{(0,1]} + ∫_{(1,∞)}` (`setIntegral_union`, `Ioc_union_Ioi_eq_Ioi`;
integrability from `mellin_Fw`). On `(0,1]`, `F = 1/t + h`, and `t^{z-2}` is integrable there with
`∫_0^1 t^{z-2} dt = 1/(z-1)` (`integral_cpow` with `-1 < Re(z-2)`); hence `h t^{z-1}` is integrable
on `(0, 1]` (difference of two integrable functions) and the integral splits. -/
theorem Gamma_mul_Q_eq_split {z : ℂ} (hz : 1 < z.re) :
    Gamma z * Q z = 1 / (z - 1) + m1 z + e1 z := by
  obtain ⟨hconv, hmel⟩ := mellin_Fw hz
  rw [← hmel, mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hconv.mono_set Ioc_subset_Ioi_self) (hconv.mono_set (Ioi_subset_Ioi zero_le_one))]
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 2)) (Ioc (0 : ℝ) 1) :=
    integrableOn_Ioc_cpow_of_neg_one_lt (by simp; linarith)
  have hI : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) • (Fw t : ℂ)
      = ∫ t in Ioc (0 : ℝ) 1, ((hErr t : ℂ) * (t : ℂ) ^ (z - 1) + (t : ℂ) ^ (z - 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hc : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ (z - 2) * t := by
      rw [← ofReal_cpow_add_one ht0]; ring_nf
    simp only [hErr, smul_eq_mul, hc]
    push_cast
    field_simp
    ring
  have hE : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) • (Fw t : ℂ) = e1 z := by
    simp only [e1, smul_eq_mul, mul_comm]
  rw [hI, hE, integral_add (integrableOn_Ioc_hErr_mul_cpow hz) h2,
    integral_Ioc_cpow_of_neg_one_lt (by simp; linarith)]
  simp only [m1]
  ring_nf

end TIdentity

end GoldbachBoundaries
