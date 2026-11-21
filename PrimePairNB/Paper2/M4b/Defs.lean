import PrimePairNB.Paper2.M4a.Defs
import PrimePairNB.SigmaFinite
import PrimePairNB.Density
import PrimePairNB.Paper2.M4a.Fill.segment_subset_Str
import PrimePairNB.Paper2.M4a.Fill.BCommon
import PrimePairNB.Paper2.M4a.Fill.hasDerivAt_Jseg_of_H2b
import PrimePairNB.Paper2.M4a.Fill.DCommon
import PrimePairNB.Paper2.M2.Skeleton
import PrimePairNB.Paper2.M1.Skeleton
import PrimePairNB.TIdentity.Assembly
import PrimeNumberTheoremAnd.Consequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The meromorphic continuation and the hypothesis checks of Section 4: definitions and small facts

This file and its companions prove the meromorphic continuation of the double prime series to `ℍ_L` and the hypothesis
checks of the examples. It imports the `M4a` and `M2` skeletons (and through them `M1` and
the RH development). Nothing imports `Paper2/Statements.lean`.

## Objects

* `primeSum ω z = ∑_p ω(p) p^{-z}`: `P` for `ω = 1`, `Q` for `ω = log` (`primeSum_one`), so one
  Mellin–Barnes lemma serves both (R) for `D` and (R) for `D^log`. `PrimeWeight ω`: `ω ≥ 0` and the series converges
  absolutely on `Re z > 1`. `wtd ω W` multiplies a weight by `ω(p)ω(q)`.
* `kMB a μ ν z = a⁻¹ K_ν((z + μ)/a)`: the Mellin–Barnes kernel of `t^μ (1 + t^a)^{-ν}`. It covers every kernel of
  this directory: `K_s(z)` (`a = 1`, `μ = 0`, `ν = s`), `Γ(z+i)Γ(s-z+j)/Γ(s+i+j)` (`a = 1`, `μ = i`, `ν = s+i+j`), the kernel of
  `(p²+q²)^{-s}` (`a = 2`, `μ = 0`, `ν = s`) and that of `S` (`a = 2`, `μ = 1 - s`, `ν = 2`).
* `Wrise N cf`, `krise N cf`: finite combinations `∑ c_{ij}(s) p^i q^j (p+q)^{-s-i-j}` and their kernels
  `∑ c_{ij}(s) Γ(z+i)Γ(s-z+j)/Γ(s+i+j)`; `W_G`, `W₀`, `W_H` are instances.
* `Ilog A k c s = (1/2πi) ∫_{(c)} k(z,s) Q(z) Q(L(s) - z) dz` with the RH development's continuation `Qcont`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Prime sums and weights -/

/-- `∑_p ω(p) p^{-z}`. -/
def primeSum (ω : ℕ → ℝ) (z : ℂ) : ℂ := ∑' p : Nat.Primes, (ω (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)

/-- `ω ≥ 0`, and `∑_p ω(p) p^{-z}` converges absolutely on `Re z > 1`. -/
def PrimeWeight (ω : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ ω n) ∧
    ∀ z : ℂ, 1 < z.re → Summable fun p : Nat.Primes => ‖(ω (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖

/-- The weight multiplied by `ω(p)ω(q)`. -/
def wtd (ω : ℕ → ℝ) (W : ℂ → ℕ → ℕ → ℂ) (s : ℂ) (p q : ℕ) : ℂ := (ω p : ℂ) * (ω q : ℂ) * W s p q

lemma primeSum_log : primeSum (fun n => Real.log n) = Q := rfl

lemma primeSum_one : primeSum (fun _ => 1) = P := by
  funext z; simp [primeSum, P]

lemma primeWeight_one : PrimeWeight (fun _ => 1) :=
  ⟨fun _ => zero_le_one, fun _ hz => by simpa using summable_norm_P_terms hz⟩

lemma primeWeight_log : PrimeWeight (fun n => Real.log n) :=
  ⟨fun n => Real.log_natCast_nonneg n, fun _ hz => summable_norm_Q_terms hz⟩

/-! ## Mellin–Barnes kernels -/

/-- `a⁻¹ K_ν((z + μ)/a)`, the Mellin–Barnes kernel of `t^μ (1 + t^a)^{-ν}`. -/
def kMB (a : ℕ) (μ ν z : ℂ) : ℂ := ((a : ℂ))⁻¹ * KerS ν ((z + μ) / a)

/-- `∑_{i,j<N} c_{ij}(s) p^i q^j (p+q)^{-s-i-j}`. -/
def Wrise (N : ℕ) (cf : ℕ → ℕ → ℂ → ℂ) (s : ℂ) (p q : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    cf i j s * (p : ℂ) ^ i * (q : ℂ) ^ j * (((p + q : ℕ) : ℂ)) ^ (-(s + i + j))

/-- Its kernel `∑_{i,j<N} c_{ij}(s) Γ(z+i)Γ(s-z+j)/Γ(s+i+j)` (the kernel of `p^iq^j(p+q)^{-s-i-j}` is
`Γ(z+i)Γ(s-z+j)/Γ(s+i+j)`, proof that the examples satisfy (R)). -/
def krise (N : ℕ) (cf : ℕ → ℕ → ℂ → ℂ) (z s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    cf i j s * (Gamma (z + i) * Gamma (s - z + j) / Gamma (s + i + j))

/-! ## The objects of the continuation -/

/-! ## Regions -/

lemma idL_HL_eq : Aff.idL.HL = HH := by ext s; simp [Aff.HL, M4a.app_idL, halfPlane]

lemma idL_RL_eq : Aff.idL.RL = halfPlane 2 := by ext s; simp [Aff.RL, M4a.app_idL, halfPlane]

lemma twoL_app (s : ℂ) : Aff.twoL.app s = 2 * s := by simp [Aff.app, Aff.twoL]

lemma twoOneL_app (s : ℂ) : Aff.twoOneL.app s = 2 * s + 1 := by simp [Aff.app, Aff.twoOneL]

/-! ## The kernels of the examples: facts with short proofs (copies of the sanity lemmas of
`Paper2/Statements.lean`, which this file does not import) -/

/-- `K_s(z)` is jointly holomorphic on `{0 < Re z < Re s}`. -/
lemma differentiableOn_kerG' :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => kerG p.1 p.2) {p | 0 < p.1.re ∧ p.1.re < p.2.re} := by
  intro p hp
  obtain ⟨h1, h2⟩ := hp
  have hG : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Gamma w := fun w hw =>
    differentiableAt_Gamma _ (fun m h => by rw [h] at hw; simp at hw; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
  have hs : 0 < p.2.re := by linarith
  have hsz : 0 < (p.2 - p.1).re := by simp; linarith
  have hd1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma q.1) p :=
    (hG _ h1).comp p differentiableAt_fst
  have hd2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (q.2 - q.1)) p :=
    (hG _ hsz).comp p (differentiableAt_snd.sub differentiableAt_fst)
  have hd3 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma q.2) p := (hG _ hs).comp p differentiableAt_snd
  have hne : Gamma p.2 ≠ 0 := Gamma_ne_zero_of_re_pos hs
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma q.1 * Gamma (q.2 - q.1) / Gamma q.2) p
  simp only [div_eq_mul_inv]
  exact (hd1.mul hd2).mul (hd3.inv hne)

lemma kerG_H2a : H2a Aff.idL kerG := by
  refine differentiableOn_kerG'.mono ?_
  rintro ⟨z, s⟩ ⟨-, hz0, hz1⟩
  simp [Aff.app, Aff.idL] at hz1 ⊢
  exact ⟨hz0, hz1⟩

end GoldbachBoundaries.Paper2.M4b
