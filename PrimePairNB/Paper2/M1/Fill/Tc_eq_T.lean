import PrimePairNB.Paper2.M1.Fill.E1Common
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.T_eq_verticalIntegral'_KerS
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds

/-!
# `Tc_eq_T`: the continuation formula for `σ > 2`

`T(s) = I_{c₀}(s)` with `c₀ = σ/2 ∈ (1, σ - 1)`; moving the line from `c₀` to `c` passes exactly the left points
`a ∈ F_δ` with `Re a > c` and no right point (`Re(s - w) ≥ σ/2 > 1` in the strip); all indicators
`[σ - Re a < c]` vanish.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The continuation formula for `σ > 2`** (Z1, Z2, Z3). With `c₀ ∈ (1, σ - 1)`, `T(s) = I_{c₀}(s)`
(`T_eq_verticalIntegral'_KerS`, `Qcont = Q` on `Re > 1`); moving the line from `c₀` to `c` passes exactly the left
points `a ∈ F_δ` with `Re a > c` (residue `R_a K_s(a) Q(s - a)`, `hasResidue_Qcont_Rcoef`, order `≥ -1`), and no right
point (`Re(s - b) ≥ σ - 1 > c₀`); the horizontal sides vanish by `E1_norm_gs_le_far`. All indicators `[σ - Re a < c]` are
`0`. Uses: `T_eq_verticalIntegral'_KerS`, `verticalIntegral'_eq_add_sum_of_simplePoles`, `E1_norm_gs_le_far`,
`hasResidue_Qcont_Rcoef`, `meromorphicOrderAt_Qcont_ge`, `poleSetQ_re_bounds`, `Fdelta_spec`. -/
theorem Tc_eq_T (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ c : ℝ} (h : AdmC δ c) {s : ℂ} (hs : 2 < s.re) :
    Tc δ c s = T s := by
  obtain ⟨hδ, hδ1, hc1, hc2, hcne⟩ := h
  have hB := half_le_Binf hZ1
  set c₀ : ℝ := s.re / 2 with hc₀
  have hc₀1 : 1 < c₀ := by rw [hc₀]; linarith
  have hc₀2 : c₀ < s.re - 1 := by rw [hc₀]; linarith
  -- `T = I_{c₀}`
  have hT : T s = IcQ Qcont c₀ s := by
    rw [T_eq_verticalIntegral'_KerS hs hc₀1 hc₀2]
    simp only [IcQ, VerticalIntegral', VerticalIntegral]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have h1 : 1 < ((c₀ : ℂ) + t * I).re := by simpa using hc₀1
    have h2 : 1 < (s - ((c₀ : ℂ) + t * I)).re := by simp; linarith
    simp only [TIdentity.Qcont_eq_Q_of_one_lt h1, TIdentity.Qcont_eq_Q_of_one_lt h2]
  have hF := (Fdelta_spec hZ1 δ hδ).1
  set S : Finset ℂ := hF.toFinset.filter (fun a => c < a.re) with hS
  have hmemS : ∀ p, p ∈ S ↔ p ∈ Fdelta δ ∧ c < p.re := by
    intro p; simp [hS]
  have hshift := E1_shift hZ1 hZ2 hZ3 hδ (c₁ := c) (c₂ := c₀) hc1.le (by linarith)
    (s := s) (by rw [hc₀]; linarith) S (fun p => Rcoef p * KerS s p * Qcont (s - p))
    (by
      intro p hp
      obtain ⟨hpF, hpc⟩ := (hmemS p).1 hp
      exact ⟨hpc, by linarith [(poleSetQ_re_bounds hpF.1).2.1]⟩)
    (by
      rintro w ⟨hw, hwS⟩
      have hwre := (mem_reProdIm.mp hw).1
      refine (E1_differentiableAt_g ?_ ?_ ?_ ?_).differentiableWithinAt
      · linarith [hwre.1]
      · simp only [sub_re]; linarith [hwre.2]
      · intro hwP
        have hwF : w ∈ Fdelta δ := ⟨hwP, by linarith [hwre.1]⟩
        have hlt : c < w.re := lt_of_le_of_ne hwre.1 (hcne w hwF)
        exact hwS ((hmemS w).2 ⟨hwF, hlt⟩)
      · intro hP
        have := (poleSetQ_re_bounds hP).2.1
        simp only [sub_re] at this
        linarith [hwre.2])
    (by
      intro p hp
      obtain ⟨hpF, -⟩ := (hmemS p).1 hp
      have hp1 := (poleSetQ_re_bounds hpF.1).2.1
      refine E1_pole_left hpF.1 (by simp only [sub_re]; linarith) fun hP => ?_
      have := (poleSetQ_re_bounds hP).2.1
      simp only [sub_re] at this
      linarith)
  -- the finite sum over `F_δ`
  have hsum : (∑ᶠ a ∈ Fdelta δ, nu c a s * Rcoef a * KerS s a * Qcont (s - a)) =
      ∑ p ∈ S, Rcoef p * KerS s p * Qcont (s - p) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hF, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    have haF : a ∈ Fdelta δ := hF.mem_toFinset.mp ha
    have ha1 := (poleSetQ_re_bounds haF.1).2.1
    have hn : ¬ (s.re - a.re < c) := by linarith
    by_cases hca : c < a.re
    · simp [nu, iverson, hca, hn]
    · simp [nu, iverson, hca, hn]
  show IcQ Qcont c s + _ = T s
  rw [hsum, hT, hshift]
  ring

/-! Consequences of this file's lemma. -/

/-- `Tcont = T` on `σ > 2`. -/
lemma Tcont_eqOn_T (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) : EqOn Tcont T (halfPlane 2) := by
  intro s hs
  by_cases hex : Binf < 1 ∧ ∃ p : ℝ × ℝ, AdmC p.1 p.2 ∧ s ∈ RegC p.1 p.2
  · rw [Tcont_eq_choose hex]
    exact Tc_eq_T hZ1 hZ2 hZ3 hex.2.choose_spec.1 hs
  · exact Tcont_eq_T_of_not hex

end GoldbachBoundaries.Paper2.M1
