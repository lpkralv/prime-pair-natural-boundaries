import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.Binf_le_Bsup_le_one
import PrimePairNB.Paper2.M1.BNumbers
import PrimePairNB.Paper2.M1.Fill.BCommon
import PrimePairNB.Paper2.M1.Fill.finite_zeros_re_gt
import PrimePairNB.Paper2.M1.Fill.Bsup_facts
import PrimePairNB.Paper2.M1.Fill.Bsup_lt_one_of_Hinf
import PrimePairNB.Paper2.M1.Fill.Fdelta_spec
import PrimePairNB.Paper2.M1.Fill.IcQ_congr
import PrimePairNB.Paper2.M1.Fill.Ic_differentiableOn
import PrimePairNB.Paper2.M1.Fill.Ic_sub_Ic
import PrimePairNB.Paper2.M1.Fill.Qcont_conj
import PrimePairNB.Paper2.M1.Fill.Rcoef_eq_finsum
import PrimePairNB.Paper2.M1.Fill.Rcoef_inv
import PrimePairNB.Paper2.M1.Fill.Rcoef_real_conj
import PrimePairNB.Paper2.M1.Fill.T_differentiableOn
import PrimePairNB.Paper2.M1.Fill.T_eq_verticalIntegral'_KerS
import PrimePairNB.Paper2.M1.Fill.TcQ_congr
import PrimePairNB.Paper2.M1.Fill.Tc_analyticAt
import PrimePairNB.Paper2.M1.Fill.Tc_eq_T
import PrimePairNB.Paper2.M1.Fill.Tc_indep
import PrimePairNB.Paper2.M1.Fill.Tc_meromorphicAt
import PrimePairNB.Paper2.M1.Fill.Tc_mono_delta
import PrimePairNB.Paper2.M1.Fill.Tcont_conj
import PrimePairNB.Paper2.M1.Fill.Tcont_props
import PrimePairNB.Paper2.M1.Fill.conj_mem_poleSetQ
import PrimePairNB.Paper2.M1.Fill.differentiableOn_verticalIntegral'
import PrimePairNB.Paper2.M1.Fill.eventuallyEq_Tcont_of_codiscrete
import PrimePairNB.Paper2.M1.Fill.exists_adm_reg
import PrimePairNB.Paper2.M1.Fill.exists_goodHeight
import PrimePairNB.Paper2.M1.Fill.finsum_nu_eq_pairSum
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.hasResidue_Qcont_Rcoef
import PrimePairNB.Paper2.M1.Fill.hasResidue_Tc
import PrimePairNB.Paper2.M1.Fill.hasResidue_Tcont
import PrimePairNB.Paper2.M1.Fill.KernelCommon
import PrimePairNB.Paper2.M1.Fill.isOpen_RegC
import PrimePairNB.Paper2.M1.Fill.isQCont_eventuallyEq
import PrimePairNB.Paper2.M1.Fill.mellin_one_add_cpow_neg
import PrimePairNB.Paper2.M1.Fill.meromorphicOn_term
import PrimePairNB.Paper2.M1.Fill.meromorphicOrderAt_Qcont_ge
import PrimePairNB.Paper2.M1.Fill.meromorphicOrderAt_Qcont_neg_iff
import PrimePairNB.Paper2.M1.Fill.norm_KerS_mul_pow_le
import PrimePairNB.Paper2.M1.Fill.norm_Qcont_le_growth
import PrimePairNB.Paper2.M1.Fill.E1Common
import PrimePairNB.Paper2.M1.Fill.norm_negLogDerivZeta_le_strip
import PrimePairNB.Paper2.M1.Fill.norm_sigmaTail_two_le
import PrimePairNB.Paper2.M1.Fill.not_mem_poleSetQ_of_goodHeight
import PrimePairNB.Paper2.M1.Fill.one_add_cpow_neg_eq_verticalIntegral'
import PrimePairNB.Paper2.M1.Fill.pinchPairs_finite
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_le_Bsup
import PrimePairNB.Paper2.M1.Fill.pinch_locallyFinite
import PrimePairNB.Paper2.M1.Fill.poleSetQ_locallyFinite
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds
import PrimePairNB.Paper2.M1.Fill.sum_zetaMult_window_le
import PrimePairNB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles

/-!
# Targets for `Paper2/Statements.lean` from the lemmas of this directory

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a proof from the lemmas of this directory. The statements `lem_Q_i`,
`lem_Q_ii`, `lem_growthQ`, `thm_cont` and `thm_residue` close by `exact X_proof ...`.

`thm_cont` and `thm_residue` carry (Z6) in their statements; the proofs here use the polynomial Gamma decay
of the RH development instead of Stirling, so they do not use it.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `lem_Q_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_Q_i_proof (hZ1 : Z1) :
    (∀ Qc : ℂ → ℂ, IsQCont Qc →
      (∀ z ∈ halfPlane 0 \ PoleSetQ, Qc (conj z) = conj (Qc z)) ∧
      ∀ a ∈ PoleSetQ, -1 ≤ meromorphicOrderAt Qc a ∧ HasResidue Qc a (Rcoef a) ∧
        (meromorphicOrderAt Qc a < 0 ↔ Rcoef a ≠ 0)) ∧
    (∀ a ∈ PoleSetQ, (Rcoef a).im = 0 ∧ Rcoef (conj a) = Rcoef a) ∧
    Rcoef 1 = 1 ∧
    (∀ k : ℕ, 2 ≤ k → Squarefree k → Rcoef (1 / (k : ℂ)) = mu k / k) ∧
    ∀ a ∈ PoleSetQ, a.im ≠ 0 →
      Rcoef a = -∑ᶠ k ∈ {k : ℕ | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / a.re ∧
          (k : ℂ) * a ∈ NontrivialZeros}, mu k / k * (zetaMult ((k : ℂ) * a) : ℂ) := by
  refine ⟨fun Qc hQc => ⟨fun z hz => ?_, fun a ha => ?_⟩, fun a ha => Rcoef_real_conj hZ1 ha, Rcoef_one',
    fun k hk hsq => Rcoef_inv hk hsq, fun a ha him => Rcoef_eq_finsum ha him⟩
  · have h1 := (isQCont_eventuallyEq hQc).1
    have hz' : conj z ∈ halfPlane 0 \ PoleSetQ := by
      refine ⟨?_, fun h => hz.2 ?_⟩
      · have : 0 < z.re := hz.1
        show 0 < (conj z).re
        simpa using this
      · simpa using conj_mem_poleSetQ h
    rw [h1 _ hz', h1 _ hz, Qcont_conj hz]
  · have hpos : 0 < a.re := re_pos_of_mem_poleSetQ ha
    have hev := (isQCont_eventuallyEq hQc).2 a hpos
    refine ⟨?_, ?_, ?_⟩
    · rw [meromorphicOrderAt_congr hev]
      exact meromorphicOrderAt_Qcont_ge hpos
    · exact (hasResidue_Qcont_Rcoef ha).congr hev.symm
    · rw [meromorphicOrderAt_congr hev]
      exact meromorphicOrderAt_Qcont_neg_iff ha

/-- `lem_Q_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_Q_ii_proof (hZ1 : Z1) :
    (∀ z ∈ halfPlane 0, ∃ U ∈ 𝓝 z, (U ∩ PoleSetQ).Finite) ∧
    (∀ a ∈ PoleSetQ, a ≠ 1 → a.re ≤ Bsup) ∧
    ∀ a ∈ PoleSetQ, a ≠ 1 → a ∉ NontrivialZeros → a.re ≤ 1 / 2 := by
  exact ⟨poleSetQ_locallyFinite, fun a ha ha1 => poleSetQ_re_le_Bsup hZ1 ha ha1,
    fun a ha ha1 haZ => (poleSetQ_re_bounds ha).2.2 ha1 haZ⟩

/-- `Bsup < 1` under `(H_∞)`. -/
theorem lem_B_iii_proof (hH : Hinf) : Bsup < 1 := by
  exact Bsup_lt_one_of_Hinf hH

/-- `lem_growthQ` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_growthQ_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ H : ℝ, 2 ≤ H →
      (∀ ρ ∈ NontrivialZeros, H - 1 ≤ |ρ.im| → ρ.re ≤ Binf + δ) →
      ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ w : ℂ, Binf + 2 * δ ≤ w.re → H ≤ |w.im| →
        w ∉ PoleSetQ ∧ ‖Qc w‖ ≤ C * Real.log |w.im| := by
  intro δ hδ
  obtain ⟨C, hC⟩ := norm_Qcont_le_growth hZ1 hZ2 hZ3 δ hδ
  refine ⟨C, fun H hH2 hH Qc hQc w hw hwH => ?_⟩
  obtain ⟨hnot, hb⟩ := hC H ⟨hH2, hH⟩ w hw hwH
  refine ⟨hnot, ?_⟩
  have hpos : 0 < w.re := by
    have := half_le_Binf hZ1
    linarith
  rw [(isQCont_eventuallyEq hQc).1 w ⟨hpos, hnot⟩]
  exact hb

/-- `thm_cont` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_cont_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (halfPlane (2 * Binf) \ Pinch) ∧
      (∀ s ∈ halfPlane (2 * Binf), -1 ≤ meromorphicOrderAt F s) ∧
      (∀ s ∈ halfPlane (2 * Binf) \ Pinch, F (conj s) = conj (F s)) ∧
      ∀ δ : ℝ, 0 < δ → δ < (1 - Binf) / 2 → ∀ c : ℝ, Binf + 2 * δ < c → c < 1 →
        (∀ a ∈ Fdelta δ, c ≠ a.re) → ∀ Qc : ℂ → ℂ, IsQCont Qc →
        DifferentiableOn ℂ (fun s => VerticalIntegral' (fun w => KerS s w * Qc w * Qc (s - w)) c)
            {s | c + Binf + 2 * δ < s.re ∧ ∀ a ∈ Fdelta δ, s.re ≠ c + a.re} ∧
        (∀ a ∈ Fdelta δ, MeromorphicOn (fun s => Rcoef a * KerS s a * Qc (s - a)) (halfPlane a.re) ∧
          halfPlane (2 * Binf) ⊆ halfPlane a.re) ∧
        ∀ s : ℂ, c + Binf + 2 * δ < s.re → (∀ a ∈ Fdelta δ, s.re ≠ c + a.re) → s ∉ Pinch →
          F s = VerticalIntegral' (fun w => KerS s w * Qc w * Qc (s - w)) c +
            ∑ᶠ a ∈ Fdelta δ, (iverson (c < a.re) + iverson (s.re - a.re < c)) *
              Rcoef a * KerS s a * Qc (s - a) := by
  have _ := hZ6  -- (Z6) is not needed here (polynomial Gamma decay)
  obtain ⟨hmero, hana, hord⟩ := Tcont_props hZ1 hZ2 hZ3
  refine ⟨Tcont, hmero, Tcont_eqOn_T hZ1 hZ2 hZ3, hana, hord, fun s hs => Tcont_conj hZ1 hZ2 hZ3 hs, ?_⟩
  intro δ hδ hδ1 c hc1 hc2 hcF Qc hQc
  have hadm : AdmC δ c := ⟨hδ, hδ1, hc1, hc2, hcF⟩
  refine ⟨?_, fun a ha => ⟨meromorphicOn_term hQc ha.1, halfPlane_two_Binf_subset hZ1 ha.1⟩, ?_⟩
  · refine (Ic_differentiableOn hZ1 hZ2 hZ3 hadm).congr ?_
    intro s hs
    exact IcQ_congr hZ1 hQc hadm hs
  · intro s hs1 hs2 hsP
    have hs : s ∈ RegC δ c := ⟨hs1, hs2⟩
    rw [Tcont_eq_Tc hZ1 hZ2 hZ3 hadm hs hsP]
    exact (TcQ_congr hZ1 hQc hadm hs hsP).symm

/-- `thm_residue` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_residue_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    (pinchPairs s₀).Finite ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) →
        F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        HasResidue F s₀ (pairSum s₀) ∧ (s₀ ∉ Pinch → 0 ≤ meromorphicOrderAt F s₀) := by
  have _ := hZ6  -- (Z6) is not needed here (polynomial Gamma decay)
  refine ⟨pinchPairs_finite hZ1 hs₀, fun F hF hFT => ?_⟩
  have hev := eventuallyEq_Tcont_of_codiscrete hZ1 hZ2 hZ3 hF hFT hs₀
  refine ⟨(hasResidue_Tcont hZ1 hZ2 hZ3 hs₀).congr hev.symm, fun hP => ?_⟩
  rw [meromorphicOrderAt_congr hev]
  exact ((Tcont_props hZ1 hZ2 hZ3).2.1 s₀ ⟨hs₀, hP⟩).meromorphicOrderAt_nonneg

end GoldbachBoundaries.Paper2.M1
