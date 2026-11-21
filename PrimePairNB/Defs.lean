import Mathlib
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Definitions (natural boundaries of prime-only Goldbach Dirichlet series)

Every object of the paper that the main statements mention is defined here: the series
`P`, `Q`, `G`, `T`; the non-trivial zeros and their multiplicity `m(ρ)`; the pole set `Σ` of `Q`;
the catalogue `𝒞`; the slanted cuts and slit discs; analytic continuation along a path; branches
(admissible germs); and the natural-boundary predicate.

## Junk-value discipline

`tsum` returns `0` where a series is not summable, so `P`, `Q`, `G`, `T` below carry meaningless
values off their half-planes of absolute convergence (`Re z > 1` for `P`, `Q`; `Re s > 2` for `G`, `T`).
No statement in `Statements.lean` evaluates them anywhere else. Continuations are always
existentially (or universally) quantified functions that agree with the series on the half-plane
of convergence; boundary statements compare functions only off a discrete set
(`=ᶠ[codiscreteWithin _]`) or on a punctured neighbourhood (`=ᶠ[𝓝[≠] _]`), never pointwise at a
possible pole.

## Relation to PrimeNumberTheoremAnd (PNT+)

* `zetaMult ρ` is `(riemannZeta.order ρ).toNat` for PNT+'s `riemannZeta.order`
  (`PrimeNumberTheoremAnd/IEANTN/ZetaDefinitions.lean`), written out here so that we do not
  import that module, which pulls in a long, not yet compiled, import chain. The two agree by `rfl`
  once both are in scope.
* `NontrivialZeros` is the same set as PNT+'s `Kadiri.NontrivialZeros`
  (`riemannZeta.zeroes_rect (Ioo 0 1) univ`), written out for the same reason.
* Residues are stated with `HasResidue` (a `Tendsto` of `(s - a) * f s` on the punctured
  neighbourhood), which is junk-free, rather than with PNT+'s `residue`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-! ## Half-planes and the line `σ = 1` -/

/-- The open right half-plane `{s : Re s > a}`. -/
def halfPlane (a : ℝ) : Set ℂ := {s | a < s.re}

/-- The paper's `ℍ = {s : σ > 1}`. -/
abbrev HH : Set ℂ := halfPlane 1

/-- The line `σ = 1`, i.e. the points `1 + iy`, `y ∈ ℝ`. -/
def lineOne : Set ℂ := {s | s.re = 1}

lemma isOpen_halfPlane (a : ℝ) : IsOpen (halfPlane a) :=
  isOpen_lt continuous_const Complex.continuous_re

/-! ## The series

`p, q` run over primes; sums over pairs are over *ordered* pairs `(p, q)`, as in the paper
(`r(n)` counts ordered representations). -/

/-- The prime zeta function `P(z) = ∑_p p^{-z}`. Meaningful for `Re z > 1` only. -/
def P (z : ℂ) : ℂ := ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-z)

/-- `Q(z) = ∑_p log p · p^{-z} = -P'(z)`: the *prime-only* series, not the von Mangoldt series
`-ζ'/ζ = ∑ Λ(n) n^{-z}`. Meaningful for `Re z > 1` only. -/
def Q (z : ℂ) : ℂ := ∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)

/-- The Goldbach Dirichlet series `G(s) = ∑_{p,q} (p+q)^{-s}`. Meaningful for `Re s > 2` only. -/
def G (s : ℂ) : ℂ :=
  ∑' pq : Nat.Primes × Nat.Primes, (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-s)

/-- The weighted series `T(s) = ∑_{p,q} log p · log q · (p+q)^{-s}`. Meaningful for `Re s > 2`
only. -/
def T (s : ℂ) : ℂ :=
  ∑' pq : Nat.Primes × Nat.Primes,
    (Real.log (pq.1 : ℕ) : ℂ) * (Real.log (pq.2 : ℕ) : ℂ) *
      (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ^ (-s)

/-! ## Zeros of ζ, multiplicity -/

/-- The non-trivial zeros of `ζ`: zeros in the critical strip `0 < Re ρ < 1`.
(Same set as PNT+'s `Kadiri.NontrivialZeros`.) The paper's "non-trivial zero" is the classical
notion; the critical-strip form is equivalent to "zero that is not a negative even integer"
because `ζ ≠ 0` on `Re s ≥ 1`, off the real axis on `Re s ≤ 0` (functional equation), and on the
real half-line `(-∞, 0]` except at `-2, -4, …` (`ζ(0) = -1/2`; at the other non-positive reals the
functional equation gives a non-zero value). We use the strip form because it needs no theorem to
state. -/
def NontrivialZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The multiplicity `m(ρ)` of a zero: `meromorphicOrderAt riemannZeta ρ`, converted to `ℕ`
(`⊤ ↦ 0`, negative ↦ `0`; neither case occurs at a non-trivial zero, see
`one_le_zetaMult` in `Statements.lean`). Definitionally `(riemannZeta.order ρ).toNat` in PNT+. -/
def zetaMult (ρ : ℂ) : ℕ := ((meromorphicOrderAt riemannZeta ρ).untopD 0).toNat

/-- `μ(n)` as a complex number. -/
abbrev mu (n : ℕ) : ℂ := ((ArithmeticFunction.moebius n : ℤ) : ℂ)

/-! ## The pole set `Σ` of `Q` and the catalogue `𝒞` -/

/-- The paper's `Σ = {1} ∪ {1/k : k ≥ 2 squarefree} ∪ {ρ/n : n ≥ 1 squarefree}`
(`ρ` a non-trivial zero). Under RH this is the pole set of `Q` on `Re z > 0`. -/
def PoleSetQ : Set ℂ :=
  {1} ∪ {z | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ z = 1 / (k : ℂ)} ∪
    {z | ∃ n : ℕ, 1 ≤ n ∧ Squarefree n ∧ ∃ ρ ∈ NontrivialZeros, z = ρ / (n : ℂ)}

/-- The catalogue:
`𝒞 = {2} ∪ {1 + 1/k : k ≥ 2 squarefree} ∪ {1 + ρ/n : n ≥ 1 squarefree}`.
The paper writes "under RH" before the display; the set itself is defined without RH. -/
def catalogue : Set ℂ :=
  {2} ∪ {s | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ s = 1 + 1 / (k : ℂ)} ∪
    {s | ∃ n : ℕ, 1 ≤ n ∧ Squarefree n ∧ ∃ ρ ∈ NontrivialZeros, s = 1 + ρ / (n : ℂ)}

/-- The numbers attached to catalogue points by the paper: `1` at `2`, `2μ(k)` at `1 + 1/k`,
and `-2μ(n)m(ρ)/ρ` at `1 + ρ/n`. A function `v` *has the catalogue values* if `v α` is the
number attached to `α` in each of the three cases. These are the residues of `T` (`cor_T_poles`)
and the coefficients `X'_α(α)` of `G` (`thm_A`). Under RH each `α ∈ 𝒞` has exactly one
representation, so the three clauses do not conflict. -/
def HasCatalogueValues (v : ℂ → ℂ) : Prop :=
  v 2 = 1 ∧
  (∀ k : ℕ, 2 ≤ k → Squarefree k → v (1 + 1 / (k : ℂ)) = 2 * mu k) ∧
  (∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros,
    v (1 + ρ / (n : ℂ)) = -(2 * mu n * (zetaMult ρ : ℂ)) / ρ)

/-- The residues of `Q` on `Σ` from the meromorphic continuation of `Q`: writing `Res_a Q = -λ_a`, the paper has
`λ_1 = -1`, `λ_{1/k} = -μ(k)/k`, `λ_{ρ/n} = μ(n)m(ρ)/n`. So `Res_1 Q = 1`, `Res_{1/k} Q = μ(k)/k`,
`Res_{ρ/n} Q = -μ(n)m(ρ)/n`. -/
def HasSigmaResidues (res : ℂ → ℂ) : Prop :=
  res 1 = 1 ∧
  (∀ k : ℕ, 2 ≤ k → Squarefree k → res (1 / (k : ℂ)) = mu k / k) ∧
  (∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros,
    res (ρ / (n : ℂ)) = -(mu n * (zetaMult ρ : ℂ)) / n)

/-! ## Residues at simple poles -/

/-- `HasResidue f a c`: `(s - a) f(s) → c` as `s → a`, `s ≠ a`. At a pole of order at most one
this says the residue of `f` at `a` is `c`. It looks only at the punctured neighbourhood, so the
value `f a` (junk at a pole) plays no role. -/
def HasResidue (f : ℂ → ℂ) (a c : ℂ) : Prop :=
  Tendsto (fun s => (s - a) * f s) (𝓝[≠] a) (𝓝 c)

/-! ## Slanted cuts and slit discs -/

/-- The slant direction `v = 1 + iκ`. -/
def slantDir (κ : ℝ) : ℂ := 1 + (κ : ℂ) * I

/-- The paper's `cut_α = {α - t v : 0 ≤ t < Re α - 1}` for the direction `v`. -/
def cut (v α : ℂ) : Set ℂ := {s | ∃ t : ℝ, 0 ≤ t ∧ t < α.re - 1 ∧ s = α - (t : ℂ) * v}

/-- A slit disc about `α`: the disc `Δ(α, r)` with `cut_α` removed. -/
def slitDisc (v α : ℂ) (r : ℝ) : Set ℂ := ball α r \ cut v α

/-- The paper's `Log_α(s) = Log((s - α)/v)` (principal branch). Its cut is the half-line
`α - [0, ∞) v`, which inside `ℍ` is `cut_α`. It is a branch of `log(s - α)` up to the constant
`log v`. -/
def logAt (v α s : ℂ) : ℂ := Complex.log ((s - α) / v)

/-! ## Analytic continuation along a path; branches

No Mathlib notion fits, so we state a minimal germ-chain definition ourselves (the shape of
TauCeti's `IsAnalyticContinuationAlong`, written independently): a continuous path
`γ : [0,1] → ℂ`, a family of functions `f t` with `f t` analytic at `γ t`, and, for `t'` near
`t`, the germs of `f t'` and `f t` at `γ t'` coincide. This is the classical "chain of function
elements" definition (e.g. Conway, *Functions of One Complex Variable I*, IX.2), with discs replaced
by germs. -/

/-- `f` is an analytic continuation along the path `γ` (germ-chain form). -/
structure IsContinuationAlong (γ : C(unitInterval, ℂ)) (f : unitInterval → ℂ → ℂ) : Prop where
  analyticAt : ∀ t, AnalyticAt ℂ (f t) (γ t)
  locallyEq : ∀ t, ∀ᶠ t' in 𝓝 t, f t' =ᶠ[𝓝 (γ t')] f t

/-- `F` continues analytically along `γ`: some continuation along `γ` starts with the germ of `F`
at `γ 0`. -/
def ContinuesAlong (F : ℂ → ℂ) (γ : C(unitInterval, ℂ)) : Prop :=
  ∃ f : unitInterval → ℂ → ℂ, IsContinuationAlong γ f ∧ f 0 =ᶠ[𝓝 (γ 0)] F

/-- `g` represents a terminal germ (at `γ 1`) of a continuation of `F` along `γ`. -/
def IsTerminalGerm (F : ℂ → ℂ) (γ : C(unitInterval, ℂ)) (g : ℂ → ℂ) : Prop :=
  ∃ f : unitInterval → ℂ → ℂ, IsContinuationAlong γ f ∧ f 0 =ᶠ[𝓝 (γ 0)] F ∧
    g =ᶠ[𝓝 (γ 1)] f 1

/-- A *branch* (paper: *admissible germ*) of `G` at `s₁`: the terminal germ at `s₁` of the
continuation of `G` along a path in `ℍ ∖ 𝒞` that starts in `σ > 2` (see the paper's introduction). A germ is represented by any function `g` with that germ at `s₁`. -/
def IsAdmissibleGerm (g : ℂ → ℂ) (s₁ : ℂ) : Prop :=
  ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ HH \ catalogue) ∧ 2 < (γ 0).re ∧ γ 1 = s₁ ∧
    IsTerminalGerm G γ g

/-! ## Natural boundaries -/

/-- `F`, given on the open set `U`, has no meromorphic extension across `z₀`: for no `r > 0` is
there a meromorphic `f` on `Δ(z₀, r)` equal to `F` on `Δ(z₀, r) ∩ U` off a discrete set. -/
def NoMeromorphicExtensionAt (F : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → ¬ ∃ f : ℂ → ℂ, MeromorphicOn f (ball z₀ r) ∧
    f =ᶠ[codiscreteWithin (ball z₀ r ∩ U)] F

/-- `L` is a natural boundary of `F` (given on `U`) in the sense of the natural boundary of `T`: no point of
`L` has a disc on which `F` extends meromorphically. -/
def IsNaturalBoundary (F : ℂ → ℂ) (U L : Set ℂ) : Prop :=
  ∀ z₀ ∈ L, NoMeromorphicExtensionAt F U z₀

/-- The germ `g` at `s₁` extends to a meromorphic function on `W`: `s₁ ∈ W` and some `f`
meromorphic on `W` agrees with `g` on a punctured neighbourhood of `s₁` (equivalent to agreeing on
a full neighbourhood, since changing a meromorphic function at one point keeps it meromorphic).
The clause `s₁ ∈ W` matters: without it, `W = ∅` would satisfy the predicate for every `g`. -/
def GermExtendsMeromorphically (g : ℂ → ℂ) (s₁ : ℂ) (W : Set ℂ) : Prop :=
  s₁ ∈ W ∧ ∃ f : ℂ → ℂ, MeromorphicOn f W ∧ f =ᶠ[𝓝[≠] s₁] g

end GoldbachBoundaries
