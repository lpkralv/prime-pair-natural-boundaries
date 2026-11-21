import PrimePairNB.Defs
import PrimePairNB.Series
import PrimePairNB.LogDerivZeta
import PrimePairNB.ResidueAPI
import PrimePairNB.ZetaRealNonvanishing

/-!
# The meromorphic continuation of `Q` to `Re z > 0`

Under RH, `Q` continues meromorphically to `Re z > 0` with the poles and residues described below. We continue `Q` by the Möbius series
`Qcont z = ∑_{n ≥ 1} μ(n) A(n z)`, `A = -ζ'/ζ` (`negLogDerivZeta`), which equals `Q` on `Re z > 1`
(`hasSum_Q_moebius_zeta`).

Method.

1. *Tail bound* (`norm_negLogDerivZeta_le`): for `Re w ≥ 2`,
   `|A(w)| ≤ C · 4 · 2^{-Re w}` with `C = ∑_m Λ(m) m^{-2}`. Hence on `Re z ≥ d > 0` the terms with
   `n d ≥ 2` are bounded by `4C (2^{-d})^n`, a convergent geometric series.
2. *Local decomposition*: near `a` with `Re a > 0`, `Qcont = ∑_{n < N} μ(n) A(n ·) + tail_N`, and the
   tail is holomorphic on `Re z > Re a / 2` (Weierstrass M-test,
   `differentiableOn_tsum_of_summable_norm`). The general lemma `analyticAt_Qcont_sub_sum`: if every
   term outside a finite set `S` with `μ(n) ≠ 0` is regular at `a`, then `Qcont - ∑_{n ∈ S}` term is
   analytic at `a`.
3. *Meromorphy*: take `S = {n < M}` with `M Re a ≥ 2`.
4. *Analyticity off `Σ`* (no RH needed): a term with `μ(n) ≠ 0` is singular at `z` only if
   `n z = 1` or `ζ(n z) = 0`; both put `z` in `Σ` (`regular_of_not_mem_poleSetQ`).
5. *Residues*: at each point of `Σ` exactly one term is singular (under RH for `ρ/n`); its residue
   comes from `HasResidue.comp_natCast_mul`, and the rest is analytic. The residue function is
   chosen by uniqueness of residues (`sigmaRes`), so no case analysis on overlapping descriptions
   of `Σ` is needed.

`Qcont` is a plain `tsum`; it is never redefined at the poles. Every pole statement is on a
punctured neighbourhood (`HasResidue`, `meromorphicOrderAt`), so the junk value at a pole is
irrelevant.
-/

noncomputable section

open Complex Filter Topology Set Metric ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GoldbachBoundaries

/-! ## 0. RH puts zeros in the right half-plane on the critical line (local copy) -/

/-- Under Mathlib's `RiemannHypothesis`, a zero with positive real part has real part `1/2`. -/
theorem sigmaMero_re_eq_half (hRH : RiemannHypothesis) {s : ℂ} (hz : riemannZeta s = 0)
    (hre : 0 < s.re) : s.re = 1 / 2 := by
  refine hRH s hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hz

/-! ## 1. A bound for `A = -ζ'/ζ` on `Re w ≥ 2` -/

/-- `C = ∑_m Λ(m) m^{-2}`. -/
def vmConst : ℝ := ∑' m : ℕ, Λ m * (m : ℝ) ^ (-(2 : ℝ))

lemma vmConst_nonneg : 0 ≤ vmConst :=
  tsum_nonneg fun _ => mul_nonneg vonMangoldt_nonneg (by positivity)

/-- `A(w)` is the von Mangoldt L-series on `Re w > 1`. -/
lemma negLogDerivZeta_eq_LSeries {w : ℂ} (hw : 1 < w.re) : negLogDerivZeta w = L ↗Λ w := by
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw, negLogDerivZeta, neg_div]

/-- For `m ≥ 2`, `x ≥ 2`: `m^{-x} ≤ m^{-2} · 4 · 2^{-x}`. -/
lemma rpow_neg_le_of_two_le {m : ℝ} (hm : 2 ≤ m) {x : ℝ} (hx : 2 ≤ x) :
    m ^ (-x) ≤ m ^ (-(2 : ℝ)) * (4 * (2 : ℝ) ^ (-x)) := by
  have hm0 : 0 < m := by linarith
  have h1 : m ^ (-x) = m ^ (-(2 : ℝ)) * m ^ (-(x - 2)) := by
    rw [← Real.rpow_add hm0]; ring_nf
  have h2 : m ^ (-(x - 2)) ≤ (2 : ℝ) ^ (-(x - 2)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hm (by linarith)
  have h3 : (2 : ℝ) ^ (-(x - 2)) = 4 * (2 : ℝ) ^ (-x) := by
    rw [show -(x - 2) = (2 : ℝ) + (-x) by ring, Real.rpow_add (by norm_num)]
    norm_num
  rw [h1, ← h3]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Tail bound.** For `Re w ≥ 2`, `‖A(w)‖ ≤ C · (4 · 2^{-Re w})`. -/
theorem norm_negLogDerivZeta_le {w : ℂ} (hw : 2 ≤ w.re) :
    ‖negLogDerivZeta w‖ ≤ vmConst * (4 * (2 : ℝ) ^ (-w.re)) := by
  rw [negLogDerivZeta_eq_LSeries (by linarith), LSeries]
  refine tsum_of_norm_bounded
    ((summable_vonMangoldt_rpow (by norm_num : (1 : ℝ) < 2)).hasSum.mul_right _) fun m => ?_
  rw [norm_term_eq]
  split_ifs with hm
  · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity)) (by positivity)
  · rcases lt_or_ge m 2 with h | h
    · have : m = 1 := by omega
      subst this
      simp
    · have hm' : (2 : ℝ) ≤ m := by exact_mod_cast h
      simp only [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg m), mul_assoc]
      exact mul_le_mul_of_nonneg_left (rpow_neg_le_of_two_le hm' hw) vonMangoldt_nonneg

/-- `2^{-x} ≤ (2^{-d})^n` when `n d ≤ x`. -/
lemma two_rpow_neg_le {d x : ℝ} {n : ℕ} (h : n * d ≤ x) :
    (2 : ℝ) ^ (-x) ≤ ((2 : ℝ) ^ (-d)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma two_rpow_neg_lt_one {d : ℝ} (hd : 0 < d) : (2 : ℝ) ^ (-d) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- A tail index `N ≥ N₀` with `N d ≥ 2`. -/
lemma exists_tail_index {d : ℝ} (hd : 0 < d) (N₀ : ℕ) : ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ (N : ℝ) * d := by
  refine ⟨max N₀ ⌈2 / d⌉₊, le_max_left _ _, ?_⟩
  have h1 : 2 / d ≤ (⌈2 / d⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈2 / d⌉₊ : ℝ) ≤ ((max N₀ ⌈2 / d⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  rw [div_le_iff₀ hd] at h1
  nlinarith

lemma re_natCast_mul (n : ℕ) (z : ℂ) : ((n : ℂ) * z).re = n * z.re := by simp

/-- A point with real part `> 1` is neither `1` nor a zero of `ζ`. -/
lemma ne_one_and_zeta_ne_zero_of_one_lt_re {w : ℂ} (h : 1 < w.re) :
    w ≠ 1 ∧ riemannZeta w ≠ 0 :=
  ⟨fun h' => by rw [h'] at h; simp at h, riemannZeta_ne_zero_of_one_lt_re h⟩

/-! ## 2. The terms `μ(n) A(n z)` and the continuation `Qcont` -/

/-- Term `n` of the Möbius series for `Q`: `μ(n) A(n z)`. -/
def sigmaTerm (n : ℕ) (z : ℂ) : ℂ := mu n * negLogDerivZeta (n * z)

/-- The continuation of `Q`: `Qcont z = ∑_n μ(n) A(n z)` (the `n = 0` term is `0`). -/
def Qcont (z : ℂ) : ℂ := ∑' n : ℕ, sigmaTerm n z

/-- The tail `∑_{m ≥ 0} μ(m + N) A((m + N) z)`. -/
def sigmaTail (N : ℕ) (z : ℂ) : ℂ := ∑' m : ℕ, sigmaTerm (m + N) z

lemma sigmaTerm_of_mu_eq_zero {n : ℕ} (h : mu n = 0) : sigmaTerm n = fun _ => 0 :=
  funext fun z => by simp [sigmaTerm, h]

/-- A term is analytic at `z` when `n z` is neither `1` nor a zero of `ζ`. -/
lemma analyticAt_sigmaTerm {n : ℕ} {z : ℂ} (h1 : (n : ℂ) * z ≠ 1)
    (h2 : riemannZeta ((n : ℂ) * z) ≠ 0) : AnalyticAt ℂ (sigmaTerm n) z := by
  have hA := analyticAt_negLogDerivZeta h1 h2
  have hlin : AnalyticAt ℂ (fun z : ℂ => (n : ℂ) * z) z := analyticAt_const.mul analyticAt_id
  exact analyticAt_const.mul (hA.comp hlin)

lemma analyticAt_sigmaTerm_of_one_lt {n : ℕ} {z : ℂ} (h : 1 < ((n : ℂ) * z).re) :
    AnalyticAt ℂ (sigmaTerm n) z :=
  analyticAt_sigmaTerm (ne_one_and_zeta_ne_zero_of_one_lt_re h).1
    (ne_one_and_zeta_ne_zero_of_one_lt_re h).2

/-- Every term is meromorphic everywhere. -/
lemma meromorphicAt_sigmaTerm (n : ℕ) (z : ℂ) : MeromorphicAt (sigmaTerm n) z := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => (n : ℂ) * z) z := analyticAt_const.mul analyticAt_id
  exact analyticAt_const.meromorphicAt.mul
    ((meromorphicAt_negLogDerivZeta _).comp_analyticAt hlin)

/-- Term bound: for `Re z ≥ d` and `n d ≥ 2`, `‖μ(n) A(n z)‖ ≤ 4C (2^{-d})^n`. -/
lemma norm_sigmaTerm_le {d : ℝ} {n : ℕ} (hn : 2 ≤ n * d) {z : ℂ} (hz : d ≤ z.re) :
    ‖sigmaTerm n z‖ ≤ vmConst * 4 * ((2 : ℝ) ^ (-d)) ^ n := by
  have hx : (n : ℝ) * d ≤ ((n : ℂ) * z).re := by
    rw [re_natCast_mul]; exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg n)
  calc ‖sigmaTerm n z‖ ≤ 1 * ‖negLogDerivZeta (n * z)‖ := by
        rw [sigmaTerm, norm_mul]; gcongr; exact norm_mu_le_one n
    _ ≤ vmConst * (4 * (2 : ℝ) ^ (-((n : ℂ) * z).re)) := by
        rw [one_mul]; exact norm_negLogDerivZeta_le (by linarith)
    _ ≤ vmConst * (4 * ((2 : ℝ) ^ (-d)) ^ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (two_rpow_neg_le hx) (by norm_num)) vmConst_nonneg
    _ = _ := by ring

lemma summable_tail_bound {d : ℝ} (hd : 0 < d) (N : ℕ) :
    Summable (fun m : ℕ => vmConst * 4 * ((2 : ℝ) ^ (-d)) ^ (m + N)) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => ((2 : ℝ) ^ (-d)) ^ n) N).mpr
    (summable_geometric_of_lt_one (by positivity) (two_rpow_neg_lt_one hd))
  exact h.mul_left _

lemma two_le_shift {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 2 ≤ (N : ℝ) * d) (m : ℕ) :
    2 ≤ ((m + N : ℕ) : ℝ) * d := by
  push_cast
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- The Möbius series converges at every `z` with `Re z > 0`. -/
lemma summable_sigmaTerm {z : ℂ} (hz : 0 < z.re) : Summable (fun n => sigmaTerm n z) := by
  obtain ⟨N, -, hN⟩ := exists_tail_index hz 0
  refine (summable_nat_add_iff N).mp ?_
  exact Summable.of_norm_bounded (summable_tail_bound hz N)
    fun m => norm_sigmaTerm_le (two_le_shift hz hN m) le_rfl

/-- `Qcont = (first N terms) + tail_N` on `Re z > 0`. -/
lemma Qcont_eq_sum_add_tail (N : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Qcont z = ∑ n ∈ Finset.range N, sigmaTerm n z + sigmaTail N z :=
  ((summable_sigmaTerm hz).sum_add_tsum_nat_add N).symm

/-- The tail is holomorphic on `Re z > d` once `N d ≥ 2` (Weierstrass M-test). -/
lemma differentiableOn_sigmaTail {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 2 ≤ (N : ℝ) * d) :
    DifferentiableOn ℂ (sigmaTail N) {z | d < z.re} := by
  show DifferentiableOn ℂ (fun w => ∑' m : ℕ, sigmaTerm (m + N) w) _
  refine differentiableOn_tsum_of_summable_norm (summable_tail_bound hd N) (fun m z hz => ?_)
    (isOpen_lt continuous_const continuous_re)
    (fun m z hz => norm_sigmaTerm_le (two_le_shift hd hN m) (le_of_lt hz))
  have hz' : d < z.re := hz
  have h2 := two_le_shift hd hN m
  have hre : 1 < (((m + N : ℕ) : ℂ) * z).re := by
    rw [re_natCast_mul]
    have : ((m + N : ℕ) : ℝ) * d ≤ ((m + N : ℕ) : ℝ) * z.re :=
      mul_le_mul_of_nonneg_left hz'.le (Nat.cast_nonneg _)
    linarith
  exact (analyticAt_sigmaTerm_of_one_lt hre).differentiableAt.differentiableWithinAt

/-! ## 3. The local structure lemma -/

/-- **Local structure.** If, outside a finite set `S`, every term with `μ(n) ≠ 0` is regular at
`a` (`n a ≠ 1`, `ζ(n a) ≠ 0`), then `Qcont - ∑_{n ∈ S} μ(n) A(n ·)` is analytic at `a`. -/
theorem analyticAt_Qcont_sub_sum {a : ℂ} (ha : 0 < a.re) (S : Finset ℕ)
    (hS : ∀ n ∉ S, mu n ≠ 0 → (n : ℂ) * a ≠ 1 ∧ riemannZeta ((n : ℂ) * a) ≠ 0) :
    AnalyticAt ℂ (fun z => Qcont z - ∑ n ∈ S, sigmaTerm n z) a := by
  set d := a.re / 2 with hd
  have hd0 : 0 < d := by positivity
  obtain ⟨N, hN0, hN⟩ := exists_tail_index hd0 (S.sup id + 1)
  have hSN : S ⊆ Finset.range N := fun n hn =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)) hN0)
  have hU : {z : ℂ | d < z.re} ∈ 𝓝 a :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by show d < a.re; linarith)
  have hTail : AnalyticAt ℂ (sigmaTail N) a := (differentiableOn_sigmaTail hd0 hN).analyticAt hU
  have hFin : AnalyticAt ℂ (fun z => ∑ n ∈ Finset.range N \ S, sigmaTerm n z) a := by
    refine Finset.analyticAt_fun_sum _ fun n hn => ?_
    have hnS : n ∉ S := (Finset.mem_sdiff.mp hn).2
    by_cases hmu : mu n = 0
    · rw [sigmaTerm_of_mu_eq_zero hmu]; exact analyticAt_const
    · obtain ⟨h1, h2⟩ := hS n hnS hmu
      exact analyticAt_sigmaTerm h1 h2
  refine (hFin.add hTail).congr ?_
  filter_upwards [hU] with z hz
  have hz' : d < z.re := hz
  have hz0 : 0 < z.re := by linarith
  rw [Qcont_eq_sum_add_tail N hz0, ← Finset.sum_sdiff hSN]
  simp only [Pi.add_apply]
  ring

/-! ## 4. Meromorphy on `Re z > 0` -/

/-- `Qcont` is meromorphic at every point of `Re z > 0`. -/
theorem meromorphicAt_Qcont {a : ℂ} (ha : 0 < a.re) : MeromorphicAt Qcont a := by
  obtain ⟨M, -, hM⟩ := exists_tail_index ha 0
  have hS : ∀ n ∉ Finset.range M, mu n ≠ 0 →
      (n : ℂ) * a ≠ 1 ∧ riemannZeta ((n : ℂ) * a) ≠ 0 := by
    intro n hn _
    have hnM : (M : ℝ) ≤ n := by exact_mod_cast (by simpa using hn : M ≤ n)
    apply ne_one_and_zeta_ne_zero_of_one_lt_re
    rw [re_natCast_mul]
    nlinarith
  have h := analyticAt_Qcont_sub_sum ha _ hS
  have hsum : MeromorphicAt (fun z => ∑ n ∈ Finset.range M, sigmaTerm n z) a :=
    MeromorphicAt.fun_sum fun n _ => meromorphicAt_sigmaTerm n a
  convert hsum.add h.meromorphicAt using 1
  funext z
  simp only [Pi.add_apply]
  ring

/-! ## 5. Where terms are singular -/

lemma squarefree_of_mu_ne_zero {n : ℕ} (h : mu n ≠ 0) : Squarefree n :=
  moebius_ne_zero_iff_squarefree.mp fun h0 => h (by simp [mu, h0])

lemma mu_ne_zero_of_squarefree {n : ℕ} (h : Squarefree n) : mu n ≠ 0 := by
  simp only [mu, ne_eq, Int.cast_eq_zero]
  exact moebius_ne_zero_iff_squarefree.mpr h

/-- Off `Σ` (and in `Re z > 0`), every term with `μ(n) ≠ 0` is regular. No RH needed. -/
theorem regular_of_not_mem_poleSetQ {z : ℂ} (hz : 0 < z.re) (hzS : z ∉ PoleSetQ) {n : ℕ}
    (hmu : mu n ≠ 0) : (n : ℂ) * z ≠ 1 ∧ riemannZeta ((n : ℂ) * z) ≠ 0 := by
  have hsq := squarefree_of_mu_ne_zero hmu
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hsq.ne_zero
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hsq.ne_zero
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 : (n : ℂ) * z ≠ 1 := by
    intro h
    have hz' : z = 1 / (n : ℂ) := by rw [eq_div_iff hn0]; linear_combination h
    apply hzS
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have : n = 1 := by omega
      subst this
      exact Or.inl (Or.inl (by simp [hz']))
    · exact Or.inl (Or.inr ⟨n, h2, hsq, hz'⟩)
  refine ⟨h1, fun hζ => hzS ?_⟩
  refine Or.inr ⟨n, hn1, hsq, (n : ℂ) * z, ⟨hζ, ?_, ?_⟩, ?_⟩
  · rw [re_natCast_mul]; positivity
  · by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hζ
  · field_simp

lemma one_div_natCast_re_pos {k : ℕ} (hk : k ≠ 0) : 0 < (1 / (k : ℂ)).re := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [show (1 / (k : ℂ)) = ((1 / (k : ℝ) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  positivity

/-- `Σ` lies in `Re z > 0` (no RH needed). -/
lemma re_pos_of_mem_poleSetQ {a : ℂ} (ha : a ∈ PoleSetQ) : 0 < a.re := by
  rcases ha with (ha | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩
  · rw [mem_singleton_iff.mp ha]; norm_num
  · exact one_div_natCast_re_pos (by omega)
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Complex.div_natCast_re]
    exact div_pos hρ.2.1 hn'

/-- At `1/k` (`k ≥ 2`), the terms with `n ≠ k`, `n ≠ 0` are regular. -/
lemma regular_inv {k n : ℕ} (hk : 2 ≤ k) (hnk : n ≠ k) (hn : n ≠ 0) :
    (n : ℂ) * (1 / (k : ℂ)) ≠ 1 ∧ riemannZeta ((n : ℂ) * (1 / (k : ℂ))) ≠ 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hw : (n : ℂ) * (1 / (k : ℂ)) = (((n : ℝ) / k : ℝ) : ℂ) := by push_cast; ring
  rw [hw]
  refine ⟨fun h => hnk ?_, ?_⟩
  · have h' : (n : ℝ) / k = 1 := by exact_mod_cast h
    rw [div_eq_one_iff_eq hkR.ne'] at h'
    exact_mod_cast h'
  · by_cases h1 : 1 ≤ (n : ℝ) / k
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h1)
    · push Not at h1
      exact riemannZeta_ne_zero_of_mem_Ioo ⟨div_pos hnR hkR, h1⟩

/-- Under RH, at `ρ/n` the terms with `n' ≠ n`, `n' ≠ 0` are regular. -/
lemma regular_zero (hRH : RiemannHypothesis) {n n' : ℕ} (hn : 1 ≤ n) (hn' : n' ≠ 0)
    (hne : n' ≠ n) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    (n' : ℂ) * (ρ / n) ≠ 1 ∧ riemannZeta ((n' : ℂ) * (ρ / n)) ≠ 0 := by
  have hρre : ρ.re = 1 / 2 := sigmaMero_re_eq_half hRH hρ.1 hρ.2.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast Nat.pos_of_ne_zero hn'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn'0 : (n' : ℂ) ≠ 0 := by exact_mod_cast hn'
  have hre : ((n' : ℂ) * (ρ / n)).re = n' * (1 / 2) / n := by
    rw [re_natCast_mul, Complex.div_natCast_re, hρre]
    ring
  refine ⟨fun h => ?_, fun hζ => ?_⟩
  · have hρeq : ρ = (n : ℂ) / n' := by
      rw [eq_div_iff hn'0]
      field_simp at h
      linear_combination h
    have him : ρ.im = 0 := by rw [hρeq]; simp [Complex.div_natCast_im]
    have : ρ = 1 / 2 := Complex.ext (by simp [hρre]) (by simp [him])
    exact riemannZeta_one_half_ne_zero (this ▸ hρ.1)
  · have h2 := sigmaMero_re_eq_half hRH hζ (by rw [hre]; positivity)
    rw [hre] at h2
    apply hne
    have : (n' : ℝ) = n := by field_simp at h2; linarith
    exact_mod_cast this

/-! ## 6. Residues -/

/-- **Single singular term.** If at `a` (`Re a > 0`) only the term `n₀` can be singular, and `A`
has residue `c` at `n₀ a`, then `Qcont` has residue `μ(n₀) c / n₀` at `a`. -/
theorem hasResidue_Qcont_of_single {a c : ℂ} (ha : 0 < a.re) {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (hA : HasResidue negLogDerivZeta ((n₀ : ℂ) * a) c)
    (hS : ∀ n, n ≠ n₀ → mu n ≠ 0 → (n : ℂ) * a ≠ 1 ∧ riemannZeta ((n : ℂ) * a) ≠ 0) :
    HasResidue Qcont a (mu n₀ * (c / n₀)) := by
  have hn0 : (n₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : n₀ ≠ 0)
  have h1 := (hA.comp_natCast_mul hn₀).const_mul (mu n₀)
  rw [mul_div_cancel_left₀ a hn0] at h1
  have h2 := analyticAt_Qcont_sub_sum ha {n₀}
    (fun n hn hmu => hS n (by simpa using hn) hmu)
  refine (h1.add_analyticAt h2).congr (Eventually.of_forall fun z => ?_)
  simp [sigmaTerm]

/-- `Res_1 Qcont = 1`. -/
theorem hasResidue_Qcont_one : HasResidue Qcont 1 1 := by
  have h := hasResidue_Qcont_of_single (a := 1) (c := 1) (n₀ := 1) (by norm_num) le_rfl
    (by simpa using hasResidue_negLogDerivZeta_one) fun n hn hmu => ?_
  · simpa [mu] using h
  · have hn0 : n ≠ 0 := (squarefree_of_mu_ne_zero hmu).ne_zero
    apply ne_one_and_zeta_ne_zero_of_one_lt_re
    have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    simp only [mul_one, natCast_re]
    linarith

/-- `Res_{1/k} Qcont = μ(k)/k` for `k ≥ 2` (zero when `k` is not squarefree). -/
theorem hasResidue_Qcont_inv {k : ℕ} (hk : 2 ≤ k) :
    HasResidue Qcont (1 / (k : ℂ)) (mu k / k) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h := hasResidue_Qcont_of_single (a := 1 / (k : ℂ)) (c := 1) (n₀ := k)
    (one_div_natCast_re_pos (by omega)) (by omega)
    (by rw [mul_one_div_cancel hk0]; exact hasResidue_negLogDerivZeta_one)
    fun n hn hmu => regular_inv hk hn (squarefree_of_mu_ne_zero hmu).ne_zero
  simpa [div_eq_mul_inv] using h

/-- Under RH, `Res_{ρ/n} Qcont = -μ(n) m(ρ)/n` for `n ≥ 1` and `ρ` a non-trivial zero. -/
theorem hasResidue_Qcont_zero (hRH : RiemannHypothesis) {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) :
    HasResidue Qcont (ρ / (n : ℂ)) (-(mu n * (zetaMult ρ : ℂ)) / n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hre : 0 < (ρ / (n : ℂ)).re := by
    rw [Complex.div_natCast_re]; exact div_pos hρ.2.1 (by exact_mod_cast hn)
  have h := hasResidue_Qcont_of_single (a := ρ / (n : ℂ)) (c := -(zetaMult ρ : ℂ)) (n₀ := n)
    hre hn
    (by
      rw [show (n : ℂ) * (ρ / n) = ρ by field_simp]
      exact (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hρ).1)
    fun n' hn' hmu => regular_zero hRH hn (squarefree_of_mu_ne_zero hmu).ne_zero hn' hρ
  convert h using 1
  ring

open Classical in
/-- The residue function of `Qcont`, chosen by uniqueness of residues (`0` where none exists). -/
def sigmaRes (a : ℂ) : ℂ := if h : ∃ c, HasResidue Qcont a c then h.choose else 0

lemma sigmaRes_eq {a c : ℂ} (h : HasResidue Qcont a c) : sigmaRes a = c := by
  unfold sigmaRes
  split_ifs with hex
  · exact hex.choose_spec.unique h
  · exact absurd ⟨c, h⟩ hex

/-- Under RH, at each point of `Σ`, `Qcont` has a non-zero residue. -/
theorem exists_hasResidue_Qcont_ne_zero (hRH : RiemannHypothesis) {a : ℂ} (ha : a ∈ PoleSetQ) :
    ∃ c, c ≠ 0 ∧ HasResidue Qcont a c := by
  rcases ha with (ha | ⟨k, hk, hsq, rfl⟩) | ⟨n, hn, hsq, ρ, hρ, rfl⟩
  · rw [mem_singleton_iff.mp ha]; exact ⟨1, one_ne_zero, hasResidue_Qcont_one⟩
  · exact ⟨mu k / k, div_ne_zero (mu_ne_zero_of_squarefree hsq)
      (by exact_mod_cast (by omega : k ≠ 0)), hasResidue_Qcont_inv hk⟩
  · refine ⟨_, ?_, hasResidue_Qcont_zero hRH hn hρ⟩
    have hm : (zetaMult ρ : ℂ) ≠ 0 := by
      have := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hρ).2
      exact_mod_cast (by omega : zetaMult ρ ≠ 0)
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mu_ne_zero_of_squarefree hsq) hm))
      (by exact_mod_cast (by omega : n ≠ 0))

/-! ## 7. The continuation of `Q`: poles and residues -/

/-- **Poles and residues of `Q`.** Under RH, `Q` continues to a meromorphic function on `Re z > 0`,
analytic off `Σ`, with a simple pole at each point of `Σ` and residues as in `HasSigmaResidues`. -/
theorem lem_Sigma_i_ii_proof (hRH : RiemannHypothesis) :
    ∃ Qc : ℂ → ℂ, MeromorphicOn Qc (halfPlane 0) ∧ EqOn Qc Q (halfPlane 1) ∧
      AnalyticOnNhd ℂ Qc (halfPlane 0 \ PoleSetQ) ∧
      (∀ a ∈ PoleSetQ, meromorphicOrderAt Qc a = -1) ∧
      ∃ res : ℂ → ℂ, (∀ a ∈ PoleSetQ, HasResidue Qc a (res a)) ∧ HasSigmaResidues res ∧
        ∀ a ∈ PoleSetQ, res a ≠ 0 := by
  refine ⟨Qcont, fun z hz => meromorphicAt_Qcont hz, fun z hz => ?_, fun z hz => ?_,
    fun a ha => ?_, sigmaRes, fun a ha => ?_, ⟨?_, ?_, ?_⟩, fun a ha => ?_⟩
  · have hz' : 1 < z.re := hz
    rw [← (hasSum_Q_moebius_zeta hz').tsum_eq, Qcont]
    refine tsum_congr fun n => ?_
    simp [sigmaTerm, negLogDerivZeta, neg_div]
  · obtain ⟨hz0, hzS⟩ := hz
    simpa using analyticAt_Qcont_sub_sum hz0 ∅
      fun n _ hmu => regular_of_not_mem_poleSetQ hz0 hzS hmu
  · obtain ⟨c, hc, h⟩ := exists_hasResidue_Qcont_ne_zero hRH ha
    rw [h.meromorphicOrderAt_eq_neg_one (meromorphicAt_Qcont (re_pos_of_mem_poleSetQ ha)) hc]
    rfl
  · obtain ⟨c, -, h⟩ := exists_hasResidue_Qcont_ne_zero hRH ha
    rw [sigmaRes_eq h]; exact h
  · exact sigmaRes_eq hasResidue_Qcont_one
  · intro k hk _; exact sigmaRes_eq (hasResidue_Qcont_inv hk)
  · intro n hn _ ρ hρ; exact sigmaRes_eq (hasResidue_Qcont_zero hRH hn hρ)
  · obtain ⟨c, hc, h⟩ := exists_hasResidue_Qcont_ne_zero hRH ha
    rw [sigmaRes_eq h]; exact hc

end GoldbachBoundaries
