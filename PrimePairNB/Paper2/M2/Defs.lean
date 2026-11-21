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
# Definitions for the proof of the boundary theorem for `T` (Paper, Theorem 1.1)

The files of this directory prove the statements of `Paper2/Statements.lean` behind Theorem 1.1: `lem_Q_iii`,
`lem_rigidity`, `lem_rigidity_converse`, `thm_single`, `lem_far`, `lem_far_abs`, `thm_boundary` (and the counting
proposition `prop_Lambda_proof` used in the proof of `thm_boundary`). Nothing here imports `Paper2/Statements.lean`;
the targets restate its statements verbatim. The files in dependency order: `QCount` (`lem_Q_iii_proof`), `Rigidity`
(`lem_rigidity_proof`, `lem_rigidity_converse_proof`), `Single` (`thm_single_proof`), `Far` (`lem_far_proof`,
`lem_far_abs_proof`), `Lambda` (`prop_Lambda_proof`), `Skeleton` (`thm_boundary_proof`).

## Objects

* `SH H = {a ∈ Σ_Q ∖ {1} : Re a > 1 - B, |Im a| ≤ H}`, the set `𝒮_H` of the proof of the boundary theorem.
* `NearBad H Y`: the points `u` (`0 < Re u ≤ 1`, `|Im u| ≤ Y`) having an ordered pair `(a, b) ≠ (1, u), (u, 1)` in
  `Σ_Q²` with `a + b = 1 + u` and `|Im a| ≤ H` (the *near-bad* pairs, as a set of points `u`).
* `rigPairs z`: the pairs `(ρ, q)` of the converse of the rigidity lemma (Paper, Lemma 3.2) whose zero `ζ*` is `z`.
* `pairOf q w = (q w / (2 q Re w), q)`: the pair `(ρ, q)` recovered from `ρ' = w` (`k = 2q Re ρ'`, `ρ = qρ'/k`).
* `qOfDen d`: the recipe `q = d` (`d` odd), `q = d/2` (`d` even) of the rigidity lemma.
* `LambdaSet y ε`: the set of `prop_Lambda_proof`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `𝒮_H = {a ∈ Σ_Q ∖ {1} : Re a > 1 - B, |Im a| ≤ H}` (proof of the boundary theorem). -/
def SH (H : ℝ) : Set ℂ := {a | a ∈ PoleSetQ ∧ a ≠ 1 ∧ 1 - Bsup < a.re ∧ |a.im| ≤ H}

/-- The points `u` with `0 < Re u ≤ 1`, `|Im u| ≤ Y` that have a competing pair below height `H`: an ordered pair
`(a, b) ∈ Σ_Q²`, `a + b = 1 + u`, other than `(1, u)`, `(u, 1)`, with `|Im a| ≤ H`. A good pair `(ρ, q)` is
*near-bad* exactly when `ρ/q ∈ NearBad H Y`. -/
def NearBad (H Y : ℝ) : Set ℂ :=
  {u | 0 < u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ Y ∧
    ∃ p ∈ pinchPairs (1 + u), p ≠ (1, u) ∧ p ≠ (u, 1) ∧ |p.1.im| ≤ H}

/-- The pairs `(ρ, q)` of the rigidity lemma (converse; Paper, Lemma 3.2) with `ζ* = z`: `ρ = 1/2 + iγ` a zero, `γ > 0`, `q` prime, and a
representation `(ρ', k) ≠ (ρ, q)` of `ρ/q` with `zetaStar ρ' k q = z`. The same set as in `lem_rigidity_converse`. -/
def rigPairs (z : ℂ) : Set (ℂ × ℕ) :=
  {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
    ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}

/-- The pair `(ρ, q)` recovered from `q` and `ρ' = w`: `k = 2q Re w`, `ρ = q w / k`. -/
def pairOf (q : ℕ) (w : ℂ) : ℂ × ℕ := ((q : ℂ) * w / ((2 * q * w.re : ℝ) : ℂ), q)

/-- The recipe of the rigidity lemma (Paper, Lemma 3.2): `q = d` if `d` is odd, `q = d/2` if `d` is even. -/
def qOfDen (d : ℕ) : ℕ := if Odd d then d else d / 2

/-- The set of `prop_Lambda_proof`: points `s₀ = 1 + ρ/q` (`ρ` a zero on the critical line, `q` prime) in
`Δ(1 + iy, ε)` with `𝓡(s₀) ≠ 0`. -/
def LambdaSet (y ε : ℝ) : Set ℂ :=
  {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
    s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSum s₀ ≠ 0}

/-- The RH development's `Qcont` is a continuation of `Q` in the sense of `IsQCont` (the proof of `exists_isQCont` in
`Paper2/Statements.lean`, which this file may not import). -/
lemma isQCont_Qcont : IsQCont Qcont := by
  refine ⟨fun z hz => meromorphicAt_Qcont hz, fun z hz => ?_, fun z hz => ?_⟩
  · have hz' : 1 < z.re := hz
    show Qcont z = Q z
    rw [Q_eq_tsum_moebius_zeta hz']
    simp only [Qcont, sigmaTerm, negLogDerivZeta, neg_div]
  · have h0 : 0 < z.re := hz.1
    have h := analyticAt_Qcont_sub_sum h0 ∅
      (fun n _ hmu => regular_of_not_mem_poleSetQ h0 hz.2 hmu)
    simpa using h

/-- A set that contains finite subsets of every size is infinite. -/
lemma infinite_of_forall_le_ncard {α : Type*} {s : Set α}
    (h : ∀ N : ℕ, ∃ t ⊆ s, t.Finite ∧ N ≤ t.ncard) : s.Infinite := by
  intro hs
  obtain ⟨t, hts, -, hN⟩ := h (s.ncard + 1)
  have := Set.ncard_le_ncard hts hs
  omega

end GoldbachBoundaries.Paper2.M2
