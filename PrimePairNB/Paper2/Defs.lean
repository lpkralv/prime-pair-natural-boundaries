import PrimePairNB.Defs

/-!
# Definitions for `T` without RH and for the class of double prime series

The residues `R_a` of `Q`, the pinch set, the numbers `B` and `B_∞`, the classical inputs (Z1)–(Z7), representations
of zeros, admissible germs, and the class data (affine map, kernel, weight). The definitions of the RH development
(`P`, `Q`, `G`, `T`, `NontrivialZeros`, `zetaMult`, `PoleSetQ`, `catalogue`, `HasResidue`, `IsTerminalGerm`,
`IsNaturalBoundary`, ...) are reused unchanged. Its `IsAdmissibleGerm` is specific to `G`, `ℍ ∖ 𝒞` and `σ > 2`;
`IsAdmissibleGermOn` below generalises it to other series, regions and start sets.

## Junk-value discipline

`tsum`, `∑ᶠ`, `Set.ncard`, Bochner integrals and `sSup`/`iInf` all return junk (`0`) when the sum, set or
integral is not summable, finite, integrable or bounded. Every definition below is used only where the object is
genuine, and every statement that relies on a count or a sum being finite says so (`Set.Finite`, `Summable`,
`Integrable`), so that a junk `0` can never make a statement true. Continuations are quantified functions that
agree with the series on a half-plane of convergence; residues are `HasResidue` (punctured neighbourhood);
boundaries compare functions off a discrete set. A pointwise formula is asserted only at points where every
function in it is analytic.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2

open GoldbachBoundaries

/-! ## 1. Zeros, the residues `R_a` of `Q`, the pinch set (Section 2 of the paper) -/

/-- `ord_w ζ`: `m(w) if `w` is a non-trivial zero, `-1` at `w = 1`, `0` otherwise. -/
def ordZeta (w : ℂ) : ℤ := by
  classical exact if w = 1 then -1 else if w ∈ NontrivialZeros then (zetaMult w : ℤ) else 0

/-- `R_a = -∑_{k ≥ 1} μ(k)/k · ord_{ka} ζ`. The index is `k + 1`, `k : ℕ`. For
`Re a > 0` only finitely many terms are non-zero (the paper's remark after the display), so the `tsum` is a
finite sum there. Used only for `a ∈ Σ_Q`. -/
def Rcoef (a : ℂ) : ℂ :=
  -∑' k : ℕ, mu (k + 1) / ((k + 1 : ℕ) : ℂ) * (ordZeta (((k + 1 : ℕ) : ℂ) * a) : ℂ)

/-- `c_a = -R_a`, the coefficient of `log(z - a)` in `P` near `a` (Section 4). -/
def cP (a : ℂ) : ℂ := -Rcoef a

/-- The pinch set `Π = Σ_Q + Σ_Q`. -/
def Pinch : Set ℂ := {s | ∃ a ∈ PoleSetQ, ∃ b ∈ PoleSetQ, s = a + b}

/-- The ordered pairs `(a, b) ∈ Σ_Q²` with `a + b = s₀`. As a set of ordered pairs, `(a, a)` occurs once,
which is the paper's "the pair `(a,a)`, if present, counted once". -/
def pinchPairs (s₀ : ℂ) : Set (ℂ × ℂ) := {p | p.1 ∈ PoleSetQ ∧ p.2 ∈ PoleSetQ ∧ p.1 + p.2 = s₀}

/-- `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`. -/
def betaB (a b : ℂ) : ℂ := Gamma a * Gamma b / Gamma (a + b)

/-- The pair sum `𝓡(s₀) = ∑_{(a,b) ∈ Σ_Q², a+b = s₀} R_a R_b B(a,b)` . A `tsum` over the subtype of pairs: when the set of pairs is finite it is the finite sum;
`𝓡(s₀) ≠ 0` implies summability (a non-summable `tsum` is `0`). -/
def pairSum (s₀ : ℂ) : ℂ :=
  ∑' p : pinchPairs s₀, Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2

/-- The Mellin–Barnes kernel `K_s(w) = Γ(w)Γ(s - w)/Γ(s)`. -/
def KerS (s w : ℂ) : ℂ := Gamma w * Gamma (s - w) / Gamma s

/-- The Iverson bracket `[A]` as a complex number. -/
def iverson (A : Prop) : ℂ := by classical exact if A then 1 else 0

/-! ## 2. The numbers `B`, `B_∞`, the hypothesis `(H_∞)`, the sets `F_δ` (Section 3) -/

/-- `B = sup_ρ β`. (`NontrivialZeros` is infinite and its real parts lie in `(0,1)`, so this is a genuine
supremum.) -/
def Bsup : ℝ := sSup (re '' NontrivialZeros)

/-- `B_∞ = lim_{t→∞} sup{β : |γ| ≥ t}`. The sup is non-increasing in `t`, so the limit is the infimum over
`t`; each sup is in `[0, 1]` (junk `sSup ∅ = 0` cannot occur, since there are zeros of every height), so the
infimum is over a set bounded below by `0`. -/
def Binf : ℝ := ⨅ t : ℝ, sSup (re '' {ρ | ρ ∈ NontrivialZeros ∧ t ≤ |ρ.im|})

/-- `(H_∞)`, in the paper's gloss "for every `δ > 0` only finitely many zeros have `β > 1/2 + δ`". This is
equivalent to `B_∞ = 1/2` once there are infinitely many zeros with `β ≥ 1/2` (`half_le_Binf`). -/
def Hinf : Prop := ∀ δ : ℝ, 0 < δ → {ρ | ρ ∈ NontrivialZeros ∧ 1 / 2 + δ < ρ.re}.Finite

/-- `F_δ = {a ∈ Σ_Q : Re a > B_∞ + δ}`. -/
def Fdelta (δ : ℝ) : Set ℂ := {a | a ∈ PoleSetQ ∧ Binf + δ < a.re}

/-! ## 3. The continuation of `Q` -/

/-- `Qc` is *the* continuation of `Q` to `Re z > 0` as a function: meromorphic there, equal to the series
on `Re z > 1`, and analytic off `Σ_Q`. The last clause pins `Qc` down pointwise off `Σ_Q` (identity
theorem on the connected set `{Re z > 0} ∖ Σ_Q`), so a formula that evaluates `Qc` off `Σ_Q` does not
depend on the choice. Non-vacuous: `exists_isQCont` in `Statements.lean`. -/
def IsQCont (Qc : ℂ → ℂ) : Prop :=
  MeromorphicOn Qc (halfPlane 0) ∧ EqOn Qc Q (halfPlane 1) ∧
    AnalyticOnNhd ℂ Qc (halfPlane 0 \ PoleSetQ)

/-! ## 4. The classical inputs (Z1)–(Z7), and two inputs the list does not name

Each is a `Prop`, true by the cited classical theorem and not proved here, and appears as an explicit
hypothesis exactly on the statements whose proofs (in the paper) use it. None is an `axiom`. -/

/-- (Z1), the part not already proved. The paper's (Z1) has four clauses: `0 < β < 1` (here true by the
definition of `NontrivialZeros`), `ζ(1 + it) ≠ 0` (Mathlib, `riemannZeta_ne_zero_of_one_le_re`),
`ζ(x) ≠ 0` for `0 < x < 1` (the RH development, `riemannZeta_ne_zero_of_mem_Ioo`), and the symmetry:
`ρ̄` and `1 - ρ̄` are zeros of the same multiplicity as `ρ`. Only the symmetry is left as a hypothesis
(`conj_mem_nontrivialZeros` in the RH development proves that `ρ̄` is a zero, not the multiplicity). -/
def Z1 : Prop :=
  ∀ ρ ∈ NontrivialZeros,
    (conj ρ ∈ NontrivialZeros ∧ zetaMult (conj ρ) = zetaMult ρ) ∧
      (1 - conj ρ ∈ NontrivialZeros ∧ zetaMult (1 - conj ρ) = zetaMult ρ)

/-- `N(t)`: the number of zeros with `0 < γ ≤ t`, counted with multiplicity. The set is finite (zeros are
discrete and avoid a neighbourhood of `1`), so `∑ᶠ` is the finite sum. -/
def Nzero (t : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}, (zetaMult ρ : ℝ)

/-- (Z2), Riemann–von Mangoldt: `N(t) = (t/2π) log(t/2π) - t/2π + O(log t)` as `t → ∞`, and
`N(t+1) - N(t) ≤ C₁ log(t+3)` for all `t ≥ 0`. (The paper's further consequences, "hence ...", are derived
from these two.) -/
def Z2 : Prop :=
  (∃ C : ℝ, ∀ᶠ t in atTop,
      |Nzero t - (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi))| ≤
        C * Real.log t) ∧
    ∃ C₁ : ℝ, ∀ t : ℝ, 0 ≤ t → Nzero (t + 1) - Nzero t ≤ C₁ * Real.log (t + 3)

/-- (Z3), the local expansion of `ζ'/ζ`: for `-1 ≤ Re z ≤ 2`, `|Im z| ≥ 2`,
`ζ'/ζ(z) = ∑_{|γ - Im z| ≤ 1} m(ρ)/(z - ρ) + O(log |Im z|)` uniformly. Asserted at points with `ζ(z) ≠ 0`
(at a zero both sides have a pole; the identity is one of meromorphic functions). -/
def Z3 : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 →
    ‖deriv riemannZeta z / riemannZeta z -
        ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1}, (zetaMult ρ : ℂ) / (z - ρ)‖ ≤
      C * Real.log |z.im|

/-- `N₀(t)`: the number of distinct zeros `1/2 + iγ` with `0 < γ ≤ t`. -/
def N0 (t : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ 0 < ρ.im ∧ ρ.im ≤ t}

/-- (Z4), Hardy–Littlewood: `N₀(t) ≥ A₀ t` for `t ≥ t₀`, some `A₀ > 0`. (A junk `ncard` would be `0`, which
makes this false, not vacuous.) -/
def Z4 : Prop := ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ t₀ : ℝ, ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)

/-- (Z5), the prime number theorem in the paper's form: for fixed `θ > 0` there is `x₀(θ)` such that for
`x ≥ x₀(θ)` the interval `(x, (1+θ)x)` contains at least `θx/(2 log x)` primes. (It follows from the theorem `pi_alt` of PrimeNumberTheoremAnd, but that derivation is not in any library.) -/
def Z5 : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ x₀ : ℝ, ∀ x ≥ x₀,
    θ * x / (2 * Real.log x) ≤ ({p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < (1 + θ) * x}.ncard : ℝ)

/-- (Z6), Stirling: for `0 < x₁ ≤ x₂` there is `C` with `|Γ(x+iy)| ≤ C(1+|y|)^{x₂} e^{-π|y|/2}` on
`x₁ ≤ x ≤ x₂`. (The paper's second sentence, `1/Γ` entire, is Mathlib's `differentiable_one_div_Gamma`.) -/
def Z6 : Prop :=
  ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ ≤ x₂ → ∃ C : ℝ, ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ,
    ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ x₂ * Real.exp (-(Real.pi * |y| / 2))

/-! ## 5. Representations and single-representation points (Section 3.4) -/

/-- `(ρ, k)` is a *representation* of `u`: `ρ` a zero, `k ≥ 1` squarefree, `ρ/k = u`. -/
def IsRep (u ρ : ℂ) (k : ℕ) : Prop :=
  ρ ∈ NontrivialZeros ∧ 1 ≤ k ∧ Squarefree k ∧ ρ / (k : ℂ) = u

/-- `(ρ, q)` is the only representation of `ρ/q` (the paper's *good* pair). -/
def IsSingleRep (ρ : ℂ) (q : ℕ) : Prop :=
  ∀ ρ' : ℂ, ∀ k : ℕ, IsRep (ρ / (q : ℂ)) ρ' k → ρ' = ρ ∧ k = q

/-- The zero `ζ*` of the rigidity lemma (Paper, Lemma 3.2) attached to a representation `(ρ', k)` of `ρ/q`: `ρ'` if `k > q`,
`1 - ρ̄'` if `k < q`. (The lemma shows `k ≠ q` for every representation other than `(ρ, q)`, so the `else` branch
is used only for `k < q`.) -/
def zetaStar (ρ' : ℂ) (k q : ℕ) : ℂ := if q < k then ρ' else 1 - conj ρ'

/-- `M(X) = ⌈2 log X / A₀⌉`. -/
def Mfun (A₀ X : ℝ) : ℕ := ⌈2 * Real.log X / A₀⌉₊

/-- `𝓟(X)` of Paper, Theorem 3.3: pairs `(ρ, q)` with `ρ = 1/2 + iγ` a zero, `X/M < γ ≤ X`,
`q` prime and `γ/q ∈ J = (y - ε/2, y + ε/2)`. -/
def singlePairs (A₀ y ε X : ℝ) : Set (ℂ × ℕ) :=
  {p | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ X / (Mfun A₀ X : ℝ) < p.1.im ∧ p.1.im ≤ X ∧
    p.2.Prime ∧ p.1.im / (p.2 : ℝ) ∈ Ioo (y - ε / 2) (y + ε / 2)}

/-! ## 6. Branches -/

/-- `g` is an *admissible germ* at `s₁` of `F` for the region `Ω` and the start set `S`: the terminal germ at
`s₁` of a continuation of `F` along a path in `Ω` that starts in `S` (the continuation is part of
`IsTerminalGerm`, which matches the paper's "along which the continuation exists"). The RH development's
`IsAdmissibleGerm g s₁` is `IsAdmissibleGermOn G (HH \ catalogue) (halfPlane 2) g s₁`. -/
def IsAdmissibleGermOn (F : ℂ → ℂ) (Ω S : Set ℂ) (g : ℂ → ℂ) (s₁ : ℂ) : Prop :=
  ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Ω) ∧ γ 0 ∈ S ∧ γ 1 = s₁ ∧ IsTerminalGerm F γ g

/-! ## 7. The prime-sum error and its Mellin transform (Section 3.7) -/

/-! ## 8. The class of Section 4: affine map, regions, kernel hypotheses -/

/-- The affine map `L(s) = ℓ s + ℓ₀`, `ℓ > 0`, `ℓ₀ ∈ ℝ`. -/
structure Aff where
  ell : ℝ
  ell0 : ℝ
  ell_pos : 0 < ell

namespace Aff

/-- `L(s) = ℓ s + ℓ₀`. -/
def app (A : Aff) (s : ℂ) : ℂ := (A.ell : ℂ) * s + A.ell0

/-- `ℍ_L = {Re L(s) > 1}`. -/
def HL (A : Aff) : Set ℂ := {s | 1 < (A.app s).re}

/-- `D_L = {1 < Re L(s) < 3}`. -/
def DL (A : Aff) : Set ℂ := {s | 1 < (A.app s).re ∧ (A.app s).re < 3}

/-- `R_L = {Re L(s) > 2}`. -/
def RL (A : Aff) : Set ℂ := {s | 2 < (A.app s).re}

/-- `Str(s) = {0 < Re z < Re L(s)}`. -/
def Str (A : Aff) (s : ℂ) : Set ℂ := {z | 0 < z.re ∧ z.re < (A.app s).re}

/-- The open set `{(z, s) : s ∈ D_L, z ∈ Str(s)} ⊆ ℂ²` of (K1). -/
def domK1 (A : Aff) : Set (ℂ × ℂ) := {p | p.2 ∈ A.DL ∧ p.1 ∈ A.Str p.2}

/-- The open set `{(z, s) : s ∈ ℍ_L, z ∈ Str(s)}` of (H2a). -/
def domH2a (A : Aff) : Set (ℂ × ℂ) := {p | p.2 ∈ A.HL ∧ p.1 ∈ A.Str p.2}

/-- `L(s) = s`. -/
def idL : Aff := ⟨1, 0, one_pos⟩

/-- `L(s) = 2s` (sums of two squares). -/
def twoL : Aff := ⟨2, 0, two_pos⟩

/-- `L(s) = 2s + 1` (the series `S`). -/
def twoOneL : Aff := ⟨2, 1, two_pos⟩

end Aff

/-- (K1) Holomorphy: `k` is holomorphic on `{(z, s) : s ∈ D_L, z ∈ Str(s)} ⊆ ℂ²` (joint, i.e. Fréchet,
complex differentiability). The kernel is written `k z s` for the paper's `k(z, s)`. -/
def K1 (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun p : ℂ × ℂ => k p.1 p.2) A.domK1

/-- (K3) Reality, on the (conjugation-invariant) domain of (K1): `k(z̄, s̄) = conj k(z, s)`. -/
def K3 (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  ∀ s ∈ A.DL, ∀ z ∈ A.Str s, k (conj z) (conj s) = conj (k z s)

/-- The double prime series `∑_{p,q} W_s(p,q)` (the weight is `W s p q`). -/
def Dser (W : ℂ → ℕ → ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' pq : Nat.Primes × Nat.Primes, W s (pq.1 : ℕ) (pq.2 : ℕ)

/-- (R) The series: `∑_{p,q} W_s(p,q)` converges absolutely on `R_L`, its sum is holomorphic on `R_L` and real
on `R_L ∩ ℝ`, and it equals the integral `(1/2πi) ∫_{(c)} k(z,s) F(z) F(L(s) - z) dz` for every
`s ∈ R_L ∩ D_L` and every `c ∈ (1, Re L(s) - 1)`. `F = P` gives (R) for `D`, `F = Q` for
`D^log`. On such a line both factors are the convergent prime sums. -/
def HypR (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (F : ℂ → ℂ) : Prop :=
  (∀ s ∈ A.RL, Summable fun pq : Nat.Primes × Nat.Primes => ‖W s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
    DifferentiableOn ℂ (Dser W) A.RL ∧
    (∀ x : ℝ, (x : ℂ) ∈ A.RL → (Dser W x).im = 0) ∧
    ∀ s ∈ A.RL ∩ A.DL, ∀ c : ℝ, 1 < c → c < (A.app s).re - 1 →
      Dser W s = VerticalIntegral' (fun z => k z s * F z * F (A.app s - z)) c

/-- `J_{ab}(s) = ∫_a^{L(s)-b} k(z,s) dz` over the straight segment, written in its parametrised form
`(L(s) - a - b) ∫_0^1 k(a + t(L(s) - a - b), s) dt` (Mathlib has no segment integral). -/
def Jseg (A : Aff) (k : ℂ → ℂ → ℂ) (a b s : ℂ) : ℂ :=
  (A.app s - a - b) * ∫ t in (0 : ℝ)..1, k (a + (t : ℂ) * (A.app s - a - b)) s

/-- (H2a): `k` is holomorphic on `{(z, s) : s ∈ ℍ_L, z ∈ Str(s)}`. -/
def H2a (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun p : ℂ × ℂ => k p.1 p.2) A.domH2a

/-- (H2b): `k(z, s) = g(z - θ s)` with `g` meromorphic on `ℂ` and `θ ∈ ℝ`. -/
def H2b (k : ℂ → ℂ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, ∃ θ : ℝ, MeromorphicOn g univ ∧ ∀ z s, k z s = g (z - θ * s)

/-- The bracket `𝔟(s) = k(1, s) + k(L(s) - 1, s)`. -/
def bracket (A : Aff) (k : ℂ → ℂ → ℂ) (s : ℂ) : ℂ := k 1 s + k (A.app s - 1) s

/-- The catalogue `𝒞_L = {s ∈ ℍ_L : L(s) ∈ Σ + Σ}`. -/
def catalogueL (A : Aff) : Set ℂ := {s | s ∈ A.HL ∧ A.app s ∈ Pinch}

/-! ## 9. The series of the examples and of Sections 4.8–4.10 -/

/-- Kernel of the Goldbach series `G`: `k(z, s) = K_s(z)`, `L(s) = s`. -/
def kerG (z s : ℂ) : ℂ := KerS s z

/-- Weight of `G`: `(p+q)^{-s}`. -/
def WG (s : ℂ) (p q : ℕ) : ℂ := (((p + q : ℕ) : ℂ)) ^ (-s)

/-- Kernel of `∑(p²+q²)^{-s}`: `½ Γ(z/2) Γ(s - z/2)/Γ(s)`, `L(s) = 2s`. -/
def kerSq (z s : ℂ) : ℂ := (1 / 2) * Gamma (z / 2) * Gamma (s - z / 2) / Gamma s

/-- Weight `(p² + q²)^{-s}`. -/
def WSq (s : ℂ) (p q : ℕ) : ℂ := (((p ^ 2 + q ^ 2 : ℕ) : ℂ)) ^ (-s)

/-- `K(w) = Γ(w) Γ(2 - w)`. -/
def KS (w : ℂ) : ℂ := Gamma w * Gamma (2 - w)

/-- Kernel of `S`: `½ K((z - s + 1)/2)`, `L(s) = 2s + 1`. -/
def kerS (z s : ℂ) : ℂ := (1 / 2) * KS ((z - s + 1) / 2)

/-- Weight of `S`: `p^{1-s} q^{2-s} (p² + q²)^{-2}`. -/
def WS (s : ℂ) (p q : ℕ) : ℂ :=
  (p : ℂ) ^ (1 - s) * (q : ℂ) ^ (2 - s) * ((((p ^ 2 + q ^ 2 : ℕ) : ℂ)) ^ 2)⁻¹

/-- The log weight `log p log q (p+q)^{-s}` of `T`. -/
def WT (s : ℂ) (p q : ℕ) : ℂ := (Real.log p : ℂ) * (Real.log q : ℂ) * WG s p q

end GoldbachBoundaries.Paper2
