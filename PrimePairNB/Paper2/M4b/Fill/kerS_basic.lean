import PrimePairNB.Paper2.M4b.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- `kerS_basic`. -/

/-- (K1) for `kerS`: on `0 < σ < 1`, `0 < Re z < 2σ + 1`, both `Γ` arguments have positive real part. -/
lemma FillD.kerS_K1 : K1 Aff.twoOneL kerS := by
  rintro ⟨z, s⟩ ⟨⟨hs1, hs2⟩, hz0, hz1⟩
  have hs1' : 0 < s.re := by
    have : 1 < 2 * s.re + 1 := by simpa [twoOneL_app] using hs1
    linarith
  have hs2' : s.re < 1 := by
    have : 2 * s.re + 1 < 3 := by simpa [twoOneL_app] using hs2
    linarith
  have hz1' : z.re < 2 * s.re + 1 := by simpa [twoOneL_app] using hz1
  have hz0' : 0 < z.re := hz0
  have hw : DifferentiableAt ℂ (fun q : ℂ × ℂ => (q.1 - q.2 + 1) / 2) (z, s) :=
    by fun_prop
  have hd1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma ((q.1 - q.2 + 1) / 2)) (z, s) :=
    (FillD.differentiableAt_Gamma_of_re_pos (w := (z - s + 1) / 2) (by simp; linarith)).comp (z, s) hw
  have hd2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (2 - (q.1 - q.2 + 1) / 2)) (z, s) :=
    (FillD.differentiableAt_Gamma_of_re_pos (w := 2 - (z - s + 1) / 2) (by simp; linarith)).comp (z, s)
      (by fun_prop)
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ
    (fun q : ℂ × ℂ => (1 / 2) * (Gamma ((q.1 - q.2 + 1) / 2) * Gamma (2 - (q.1 - q.2 + 1) / 2))) (z, s)
  exact (hd1.mul hd2).const_mul _

/-- (H2b) for `kerS`, with `θ = 1` and `g(w) = ½K((w + 1)/2)`. -/
lemma FillD.kerS_H2b : H2b kerS := by
  refine ⟨fun w => (1 / 2) * KS ((w + 1) / 2), 1, ?_, ?_⟩
  · intro w _
    have ha : AnalyticAt ℂ (fun x : ℂ => (x + 1) / 2) w := by fun_prop
    have h1 := FillD.meromorphicAt_Gamma_comp ha
    have ha2 : AnalyticAt ℂ (fun x : ℂ => 2 - (x + 1) / 2) w := by fun_prop
    have h2 := FillD.meromorphicAt_Gamma_comp ha2
    exact (MeromorphicAt.const (1 / 2 : ℂ) w).mul (h1.mul h2)
  · intro z s
    simp only [kerS]
    congr 2
    push_cast; ring

/-- `Γ(1/2)² = π`. -/
lemma FillD.Gamma_one_half_sq : Gamma (1 / 2) * Gamma (1 / 2) = (Real.pi : ℂ) := by
  rw [Complex.Gamma_one_half_eq, ← cpow_add _ _ (by exact_mod_cast Real.pi_ne_zero)]
  norm_num

/-- **(K1), (H2b), (K3) and the bracket for `S`**. (K1) on `domK1` (`0 < σ < 1`, `0 < Re z < 2σ + 1`):
`Re w = (Re z - σ + 1)/2 > 0`, `Re(2 - w) = (3 - Re z + σ)/2 > 0`, so `Γ(w)Γ(2 - w)` is holomorphic. (H2b): `θ = 1`,
`g(w) = ½K((w + 1)/2)`, meromorphic on `ℂ` (`Γ = (1/Γ)⁻¹` with `1/Γ` entire, `MeromorphicAt.inv`, products and
compositions with affine maps). (K3): `Complex.Gamma_conj`. The bracket: `kerS 1 s + kerS (2s) s` with
`(1 - s + 1)/2 = 1 - s/2` and `(2s - s + 1)/2 = (s + 1)/2` (`ring_nf` under `KS`). `𝔟(0) = ½(Γ(1)Γ(1) + Γ(½)Γ(3/2))`,
`Γ(3/2) = ½Γ(½)` (`Complex.Gamma_add_one`), `Γ(½)² = π` (`Complex.Gamma_one_half_eq`, `cpow_add`). `𝔟(½) = K(¾)`,
non-zero since `Γ(¾), Γ(5/4) ≠ 0` (`Complex.Gamma_ne_zero_of_re_pos`); `½ ∈ D_L` (`Re L(½) = 2`). -/
theorem kerS_basic : K1 Aff.twoOneL kerS ∧ H2b kerS ∧ K3 Aff.twoOneL kerS ∧
    (∀ s : ℂ, bracket Aff.twoOneL kerS s = 1 / 2 * (KS (1 - s / 2) + KS ((s + 1) / 2))) ∧
    bracket Aff.twoOneL kerS 0 = 1 / 2 * (1 + Real.pi / 2) ∧ bracket Aff.twoOneL kerS (1 / 2) ≠ 0 := by
  have hbr : ∀ s : ℂ, bracket Aff.twoOneL kerS s = 1 / 2 * (KS (1 - s / 2) + KS ((s + 1) / 2)) := by
    intro s
    simp only [bracket, kerS, twoOneL_app]
    rw [show (1 - s + 1) / 2 = 1 - s / 2 by ring, show (2 * s + 1 - 1 - s + 1) / 2 = (s + 1) / 2 by ring]
    ring
  refine ⟨FillD.kerS_K1, FillD.kerS_H2b, ?_, hbr, ?_, ?_⟩
  · intro s _ z _
    simp only [kerS, KS, map_div₀, map_mul, ← Complex.Gamma_conj, map_sub, map_add, map_one, map_ofNat]
  · rw [hbr]
    have h32 : Gamma (2 - 1 / 2) = 1 / 2 * Gamma (1 / 2) := by
      rw [show (2 : ℂ) - 1 / 2 = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
    have hK1 : KS (1 - 0 / 2) = 1 := by
      simp only [KS, zero_div, sub_zero, show (2 : ℂ) - 1 = 1 by norm_num, Complex.Gamma_one, mul_one]
    have hKh : KS ((0 + 1) / 2) = Real.pi / 2 := by
      simp only [KS, zero_add]
      rw [h32, ← FillD.Gamma_one_half_sq]
      ring
    rw [hK1, hKh]
  · rw [hbr, show (1 : ℂ) - 1 / 2 / 2 = 3 / 4 by norm_num, show ((1 : ℂ) / 2 + 1) / 2 = 3 / 4 by norm_num]
    have h1 : Gamma (3 / 4) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
    have h2 : Gamma (2 - 3 / 4) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
    have hK : KS (3 / 4) ≠ 0 := mul_ne_zero h1 h2
    intro h
    apply hK
    linear_combination h

end GoldbachBoundaries.Paper2.M4b
