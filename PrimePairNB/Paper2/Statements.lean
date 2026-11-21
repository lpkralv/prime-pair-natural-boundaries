import PrimePairNB.Paper2.Defs
import PrimePairNB.Statements
import PrimePairNB.Paper2.M1.Skeleton
import PrimePairNB.Paper2.M2.Skeleton
import PrimePairNB.TIdentity.Assembly
import PrimeNumberTheoremAnd.Consequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim
import PrimePairNB.Paper2.M4a.Defs
import PrimePairNB.SigmaFinite
import PrimePairNB.Density
import PrimePairNB.Paper2.M4a.Fill.segment_subset_Str
import PrimePairNB.Paper2.M4a.Fill.BCommon
import PrimePairNB.Paper2.M4a.Fill.hasDerivAt_Jseg_of_H2b
import PrimePairNB.Paper2.M4a.Fill.DCommon
import PrimePairNB.Paper2.M4b.Rising
import PrimePairNB.Paper2.M4b.Fill.DCommon
import PrimePairNB.Paper2.M4b.Fill.kerS_basic
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WG
import PrimePairNB.Paper2.M4b.Fill.hypR_kerG_WT
import PrimePairNB.Paper2.M4b.Fill.E1Common
import PrimePairNB.Paper2.M4b.Fill.hypR_kerSq
import PrimePairNB.Paper2.M4b.Fill.hypR_kerS
import PrimePairNB.Paper2.M1.Fill.KernelCommon
import PrimePairNB.Paper2.M1.Fill.one_add_cpow_neg_eq_verticalIntegral'
import PrimePairNB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles
import PrimePairNB.Paper2.M1.Fill.BCommon
import PrimePairNB.Paper2.M6.Fill.isOpen_OmegaP
import PrimePairNB.Paper2.M6.Fill.BCommon

/-!
# Statements the paper cites

This file states the results of the paper's Sections 2-4 that are cited by name (Lemmas 2.1, 2.2, 3.2, 3.4, Theorems
1.1, 3.3, 4.1, 4.2), each as a Lean `theorem` whose docstring gives the statement in words and its formalization. The
release README gives the table from the paper's results to these declarations. `Hinf` and the classical inputs
(Z1)–(Z6) are `Prop` definitions in `Paper2/Defs.lean`, each an explicit premise exactly where the proof uses it.
There are no `axiom`s.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2

open GoldbachBoundaries

/-! ## 1. Sanity lemmas -/

/-- Sanity (non-vacuity of `IsQCont`, the hypothesis of every statement that quantifies over continuations of
`Q`): the RH development's `Qcont z = ∑ μ(n) (-ζ'/ζ)(nz)` is one, unconditionally. -/
theorem exists_isQCont : ∃ Qc : ℂ → ℂ, IsQCont Qc := by
  refine ⟨Qcont, fun z hz => meromorphicAt_Qcont hz, fun z hz => ?_, fun z hz => ?_⟩
  · have hz' : 1 < z.re := hz
    show Qcont z = Q z
    rw [Q_eq_tsum_moebius_zeta hz']
    simp only [Qcont, sigmaTerm, negLogDerivZeta, neg_div]
  · have h0 : 0 < z.re := hz.1
    have h := analyticAt_Qcont_sub_sum h0 ∅
      (fun n _ hmu => regular_of_not_mem_poleSetQ h0 hz.2 hmu)
    simpa using h

/-! ## 2. Preliminaries -/

/-- **Paper, Lemma 2.1 (i)** (unconditional): `Q` is meromorphic on `Re z > 0`, real on `(0, ∞)` off its poles, with
`Q(z̄) = conj Q(z)`. Its poles are simple and lie in `Σ_Q`, and the residue at `a ∈ Σ_Q` is `R_a`, so the poles of `Q`
are exactly the points of `Σ_Q` with `R_a ≠ 0`. Each `R_a` is real, `R_ā = R_a`, `R_1 = 1` and `R_{1/k} = μ(k)/k`; for
non-real `a` the sum defining `R_a` runs over the squarefree `k < 1/Re a` for which `ka` is a zero.

Lean: for *every* continuation `Qc` of `Q` (`IsQCont`: meromorphic on `Re z > 0`, the series on `Re z > 1`,
analytic off `Σ_Q`; one exists, `exists_isQCont`): conjugation symmetry off `Σ_Q` (which gives "real on
`(0,∞)` off its poles", since the real points of `Σ_Q` are poles), order `≥ -1` and residue `R_a` at each
`a ∈ Σ_Q`, and a pole at `a ∈ Σ_Q` exactly when `R_a ≠ 0`. Then the facts about the numbers `R_a`. `R_1 = 1`
is also proved outright (`Paper2.M1.Rcoef_one'`). Hypothesis (Z1) for the reality statements (multiplicity of `ρ̄`). -/
theorem lem_Q_i (hZ1 : Z1) :
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
  exact M1.lem_Q_i_proof hZ1

/-- **Paper, Lemma 2.1 (ii)** (unconditional): `Σ_Q` is locally finite in `Re z > 0`. Every point of `Σ_Q ∖ {1}` has real
part at most `B = sup_ρ β`, and every point of `Σ_Q` that is neither `1` nor a zero has real part at most `1/2`.

Lean: (Z1) is a premise because the bound `1/k ≤ 1/2 ≤ B` needs a zero with `β ≥ 1/2` (from `1 - ρ̄`). -/
theorem lem_Q_ii (hZ1 : Z1) :
    (∀ z ∈ halfPlane 0, ∃ U ∈ 𝓝 z, (U ∩ PoleSetQ).Finite) ∧
    (∀ a ∈ PoleSetQ, a ≠ 1 → a.re ≤ Bsup) ∧
    ∀ a ∈ PoleSetQ, a ≠ 1 → a ∉ NontrivialZeros → a.re ≤ 1 / 2 := by
  exact M1.lem_Q_ii_proof hZ1

/-- **Paper, Lemma 2.1 (iii)** (unconditional): for `ε ∈ (0, 1)` there is `C(ε)` such that `|R_a| ≤ C(ε) log(|Im a| + 3)`
for every `a ∈ Σ_Q` with `Re a ≥ ε`, and for every real `t` at most `C(ε) log(|t| + 3)` points `a ∈ Σ_Q` have
`Re a ≥ ε` and `t ≤ Im a ≤ t + 1`.

Lean: "at most `N` points" is stated as `Set.Finite` plus a bound on `Set.ncard` (a bare `ncard` bound would be
vacuous for an infinite set). Hypotheses (Z2), and (Z1): the proof uses the multiplicity bound
`m(ρ) ≤ 2C₁ log(|γ|+3)` that the paper derives from (Z2) at negative heights as well, while Lean's `Z2` counts only
zeros with `0 < γ ≤ t`, so the bound at `γ < 0` needs `m(ρ̄) = m(ρ)`, which is (Z1). -/
theorem lem_Q_iii (hZ1 : Z1) (hZ2 : Z2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ,
      (∀ a ∈ PoleSetQ, ε ≤ a.re → ‖Rcoef a‖ ≤ C * Real.log (|a.im| + 3)) ∧
      ∀ t : ℝ, {a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.Finite ∧
        ({a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.ncard : ℝ) ≤
          C * Real.log (|t| + 3) := by
  exact M2.lem_Q_iii_proof hZ1 hZ2

/-! ## 3. The weighted series `T` without RH -/

/-- **Paper, Lemma 2.2** (unconditional): let `δ > 0` and let `H ≥ 2` be such that every zero with `|γ| ≥ H - 1` has
`β ≤ B_∞ + δ`. There is a constant `C_δ`, depending only on `δ`, such that `|Q(w)| ≤ C_δ log |Im w|` for
`Re w ≥ B_∞ + 2δ`, `|Im w| ≥ H`.

Lean: `C` is chosen after `δ` and before `H` ("depending only on `δ`"). `Q` is any continuation `Qc` (`IsQCont`);
the region contains no point of `Σ_Q` (asserted, so the bound is about genuine values of `Qc`). Hypotheses (Z2),
(Z3) (the proof's), and (Z1) (through `B_∞ ≥ 1/2`, used for the terms `k ≥ 2`). -/
theorem lem_growthQ (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ H : ℝ, 2 ≤ H →
      (∀ ρ ∈ NontrivialZeros, H - 1 ≤ |ρ.im| → ρ.re ≤ Binf + δ) →
      ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ w : ℂ, Binf + 2 * δ ≤ w.re → H ≤ |w.im| →
        w ∉ PoleSetQ ∧ ‖Qc w‖ ≤ C * Real.log |w.im| := by
  exact M1.lem_growthQ_proof hZ1 hZ2 hZ3

/-- **Paper, Theorem 4.1** (unconditional): `T` continues to a single-valued meromorphic function on `σ > 2B_∞`, real on
the real axis, with `T(s̄) = conj T(s)`; its poles there are simple and lie in `Π`. More precisely, for
`0 < δ < (1 - B_∞)/2`, `F = F_δ` and `c ∈ (B_∞ + 2δ, 1)` with `c ≠ Re a` for `a ∈ F`, and every `s` with
`σ > c + B_∞ + 2δ` and `σ ≠ c + Re a` (`a ∈ F`), one has
`T(s) = I_c(s) + ∑_{a ∈ F} ([Re a > c] + [σ - Re a < c]) R_a K_s(a) Q(s - a)`, where
`I_c(s) = (1/2πi) ∫_{(c)} K_s(w) Q(w) Q(s - w) dw` is holomorphic on that set and each term of the sum is
meromorphic on `σ > Re a`.

Lean: some `F`, meromorphic on `σ > 2B_∞`, equal to the series `T` on `σ > 2`, analytic off `Π`, of order
`≥ -1` everywhere (poles simple), with `F(s̄) = conj F(s)` off `Π` ("real on the real axis" is this at real
points). The representation is part of the same `∃ F`, so it is asserted pointwise only where every function in
it is analytic: `F` off `Π`, and the continuation `Qc` of `Q` (any `IsQCont`) off `Σ_Q` (for `s ∉ Π` in the
region, `s - a ∉ Σ_Q` and the line integrand avoids `Σ_Q`). Hypotheses (Z1), (Z2), (Z3) (growth of `Q`,
the growth bound for `Q`), (Z6) (kernel bound). -/
theorem thm_cont (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
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
  exact M1.thm_cont_proof hZ1 hZ2 hZ3 hZ6

/-- **Paper, Theorem 4.2** (unconditional): let `Re s₀ > 2B_∞`. Then the set of ordered pairs `(a, b) ∈ Σ_Q × Σ_Q` with
`a + b = s₀` is finite, and `Res_{s=s₀} T = ∑_{a+b=s₀} R_a R_b B(a, b)` with `B(a, b) = Γ(a)Γ(b)/Γ(s₀)`, the pair
`(a, a)`, if present, counted once. In particular `s₀` is a regular point of `T` when `s₀ ∉ Π`.

Lean: "`T`" is every meromorphic `F` on `σ > 2B_∞` agreeing with the series off a discrete subset of `σ > 2`
(such `F` exist by `thm_cont`; residues and orders do not depend on the choice). "Regular" is order `≥ 0`.
Hypotheses as for `thm_cont`. -/
theorem thm_residue (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    (pinchPairs s₀).Finite ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) →
        F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        HasResidue F s₀ (pairSum s₀) ∧ (s₀ ∉ Pinch → 0 ≤ meromorphicOrderAt F s₀) := by
  exact M1.thm_residue_proof hZ1 hZ2 hZ3 hZ6 hs₀

/-- **Paper, Lemma 3.2**, first part (unconditional): let `ρ = 1/2 + iγ` be a zero with `γ > 0`, let `q` be a prime and
`u = ρ/q`. Every representation `(ρ', k) ≠ (ρ, q)` of `u` has `gcd(k, q) = 1`, `1 ≤ k < 2q`, `k ≠ q` and
`Re ρ' = k/(2q) ≠ 1/2`. Put `ζ* = ρ'` if `k > q` and `ζ* = 1 - ρ̄'` if `k < q`. Then `ζ*` is a zero with
`Re ζ* > 1/2` and `0 < Im ζ* < 2γ`, and the reduced denominator `d` of the rational number `Re ζ*` lies in `{q, 2q}`.

Lean: `ζ* = zetaStar ρ' k q`. "The reduced denominator of the rational number `Re ζ*`" is `r.den` for a rational `r`
equal to `Re ζ*` (`ℚ` is normalised, so `r.den` is the reduced denominator; the existence of `r` is part of the
claim). Hypothesis (Z1) (`1 - ρ̄'` is a zero; `Re ρ' < 1`). -/
theorem lem_rigidity (hZ1 : Z1) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hre : ρ.re = 1 / 2)
    (him : 0 < ρ.im) {q : ℕ} (hq : q.Prime) :
    ∀ ρ' : ℂ, ∀ k : ℕ, IsRep (ρ / (q : ℂ)) ρ' k → (ρ', k) ≠ (ρ, q) →
      Nat.Coprime k q ∧ 1 ≤ k ∧ k < 2 * q ∧ k ≠ q ∧ ρ'.re = (k : ℝ) / (2 * q) ∧ ρ'.re ≠ 1 / 2 ∧
      zetaStar ρ' k q ∈ NontrivialZeros ∧ 1 / 2 < (zetaStar ρ' k q).re ∧
      0 < (zetaStar ρ' k q).im ∧ (zetaStar ρ' k q).im < 2 * ρ.im ∧
      ∃ r : ℚ, (r : ℝ) = (zetaStar ρ' k q).re ∧ (r.den = q ∨ r.den = 2 * q) := by
  exact M2.lem_rigidity_proof hZ1 hρ hre him hq

/-- **Paper, Lemma 3.2**, the converse: `ζ*` determines `q` (`q = d` if `d` is odd, `q = d/2` if `d` is even), and then
`(ρ, q)` is one of at most two pairs.

Lean: for a point `z` whose real part is the rational `r` (reduced denominator `d = r.den`), the set of pairs
`(ρ, q)` as in the first part (`ρ = 1/2 + iγ` a zero, `γ > 0`, `q` prime) having a representation
`(ρ', k) ≠ (ρ, q)` of `ρ/q` with `ζ* = z`: every such pair has `q = d` (`d` odd) or `q = d/2` (`d` even), and there
are at most two (finite, `ncard ≤ 2`). Hypothesis (Z1). -/
theorem lem_rigidity_converse (hZ1 : Z1) (z : ℂ) (r : ℚ) (hr : (r : ℝ) = z.re) :
    (∀ p ∈ {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z},
      p.2 = if Odd r.den then r.den else r.den / 2) ∧
    {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}.Finite ∧
    {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}.ncard ≤ 2 := by
  exact M2.lem_rigidity_converse_proof hZ1 z r hr

/-- **Paper, Theorem 3.3** (unconditional): let `y > 0`, `0 < ε < y`, `J = (y - ε/2, y + ε/2)`, and for `X ≥ 3` let
`M = M(X) = ⌈2 log X/A₀⌉` with `A₀` as in (Z4) and
`𝓟(X) = {(ρ, q) : ρ = 1/2 + iγ a zero, X/M < γ ≤ X, q prime, γ/q ∈ J}`. Call `(ρ, q) ∈ 𝓟(X)` *good* if `(ρ, q)` is the
only representation of `u = ρ/q`. There are `c₂ = c₂(y, ε) > 0` and `X₀` such that for `X ≥ X₀`: (a) `|𝓟(X)| ≥ c₂X²/log²X`
and at most `4X log(2X)` pairs of `𝓟(X)` are not good, so at least `½c₂X²/log²X` are good; (b) for every good pair,
`|u - iy| < ε`, `Re u = 1/(2q)`, `R_u = m(ρ)/q ≠ 0` and `|2R_u/u| = 2m(ρ)/|ρ| ≥ 2/(X + 1)`; (c) distinct pairs in
`𝓟(X)` give distinct points `u`.

Lean: `A₀` and `t₀` are any witnesses of (Z4), passed explicitly (`hN0`), since `M` depends on `A₀`. Counts are
`Set.ncard` together with `Set.Finite`. Hypotheses (Z1) (the proof uses `1 - ρ̄`), (Z2), (Z5). -/
theorem thm_single (hZ1 : Z1) (hZ2 : Z2) (hZ5 : Z5) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 3 ≤ X →
      (singlePairs A₀ y ε X).Finite ∧
      c₂ * X ^ 2 / Real.log X ^ 2 ≤ ((singlePairs A₀ y ε X).ncard : ℝ) ∧
      (({p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ≤
        4 * X * Real.log (2 * X) ∧
      c₂ / 2 * X ^ 2 / Real.log X ^ 2 ≤
        (({p | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ∧
      (∀ p ∈ singlePairs A₀ y ε X, IsSingleRep p.1 p.2 →
        ‖p.1 / (p.2 : ℂ) - y * I‖ < ε ∧ (p.1 / (p.2 : ℂ)).re = 1 / (2 * p.2) ∧
        Rcoef (p.1 / (p.2 : ℂ)) = (zetaMult p.1 : ℂ) / p.2 ∧ Rcoef (p.1 / (p.2 : ℂ)) ≠ 0 ∧
        ‖2 * Rcoef (p.1 / (p.2 : ℂ)) / (p.1 / (p.2 : ℂ))‖ = 2 * zetaMult p.1 / ‖p.1‖ ∧
        2 / (X + 1) ≤ 2 * zetaMult p.1 / ‖p.1‖) ∧
      InjOn (fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) (singlePairs A₀ y ε X) := by
  exact M2.thm_single_proof hZ1 hZ2 hZ5 hA₀ hN0 hy hε hεy

/-- **Paper, Lemma 3.4** (hypothesis `B < 1`): let `Y > 0` and `s₀ = 1 + v` with `0 < Re v ≤ 1`, `|Im v| ≤ Y`. Every
ordered pair `(a, b) ∈ Σ_Q²` with `a + b = s₀` other than `(1, v)` and `(v, 1)` has `a, b ∈ Σ_Q ∖ {1}` and
`Re a, Re b ∈ (1 - B, B]`. There is `H₀ = H₀(B, Y) ≥ 2Y + 2` such that for every `H ≥ H₀` and every such `s₀` the sum of
`|R_a R_b B(a, b)|` over these pairs with `|Im a| > H` is at most `e^{-H}`.

Lean: `H₀` is chosen after `Y` and before `H` and `v` (uniform in `s₀`). The sum is a `tsum` of norms over the subtype
of such pairs, stated with its `Summable` (a non-summable `tsum` is `0`, which would make the bound vacuous).
`B(a, b) = betaB a b = Γ(a)Γ(b)/Γ(a+b)`, and `a + b = s₀` has real part `> 1`, so `Γ(s₀) ≠ 0`. Hypotheses (Z1), (Z2)
(through Paper, Lemma 2.1 (ii), (iii)) and (Z6) (the proof's). -/
theorem lem_far (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    (∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y → ∀ p ∈ pinchPairs (1 + v), p ≠ (1, v) → p ≠ (v, 1) →
      p.1 ∈ PoleSetQ \ {1} ∧ p.2 ∈ PoleSetQ \ {1} ∧
        p.1.re ∈ Ioc (1 - Bsup) Bsup ∧ p.2.re ∈ Ioc (1 - Bsup) Bsup) ∧
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ ≤ Real.exp (-H) := by
  exact M2.lem_far_proof hZ1 hZ2 hZ6 hB hY

/-- **Paper, Lemma 3.4**, last sentence: the full sum `∑_{a+b=s₀} R_a R_b B(a, b)` converges absolutely.

Lean: for every `s₀ = 1 + v` with `0 < Re v ≤ 1` (every `Y`), `Summable` of the norms over all ordered pairs; this is
the absolute convergence of `𝓡(s₀) = pairSum s₀` (the pair sum in the residue formula). Hypotheses as for `lem_far`. -/
theorem lem_far_abs (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) :
    ∀ v : ℂ, 0 < v.re → v.re ≤ 1 →
      Summable fun p : pinchPairs (1 + v) => ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ := by
  exact M2.lem_far_abs_proof hZ1 hZ2 hZ6 hB

/-- **Paper, Theorem 1.1**: assume `(H_∞)`. Then `T` is a single-valued meromorphic function on `ℍ`, and for every
`y ∈ ℝ` and `ε > 0` the disc about `1 + iy` of radius `ε` contains infinitely many poles of `T`. Consequently, for no
`y ∈ ℝ` and `r > 0` is there a meromorphic function `f` on the disc of radius `r` about `1 + iy` with `f = T` on the
disc intersected with `ℍ`: the line `σ = 1` is a natural boundary of `T`.

Lean: for every `F` meromorphic on `ℍ` agreeing with the series off a discrete
subset of `σ > 2` (non-vacuous by the first conjunct). Poles are points of `ℍ` of order `< 0`. The disc of radius `ε` about `1 + iy` is `ball (1 + y * I) ε`.
Hypotheses `(H_∞)` (the paper's), and (Z1), (Z2), (Z3), (Z4), (Z5), (Z6) (through Paper, Theorems 4.1, 4.2 and 3.3 and
Lemma 3.4). -/
theorem thm_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      (∀ y ε : ℝ, 0 < ε →
        {s | s ∈ ball (1 + (y : ℂ) * I) ε ∧ s ∈ HH ∧ meromorphicOrderAt F s < 0}.Infinite) ∧
      IsNaturalBoundary F HH lineOne := by
  exact M2.thm_boundary_proof hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6


end GoldbachBoundaries.Paper2
