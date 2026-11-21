import PrimePairNB.Defs
import PrimePairNB.SigmaMeromorphic
import PrimePairNB.SigmaFinite
import PrimePairNB.Density
import PrimePairNB.TIdentity.Assembly

/-!
# Theorem on `G`: definitions

Definitions for the proof that `G` continues along paths in `ℍ ∖ 𝒞`, has the stated local form, and has
the line `σ = 1` as a natural boundary.

Everything in `GoldbachBoundaries/ThmA/` lives in the namespace `GoldbachBoundaries.ThmA`, so that
it can be imported by `Statements.lean` without name clashes (`IsGoodSlant` is
re-declared here with the body of `Statements.lean`'s; the two are definitionally equal).

## The objects, as defined here

Throughout `v = slantDir κ = 1 + iκ`.

* `Omega κ` is the paper's `Ω_ℍ = ℍ ∖ ⋃_α cut_α`; `upperPart`/`lowerPart` are the `±` parts of a disc
  centred on a cut (the `+` side of `cut_α` is the side in the direction `+iv`, i.e.
  `Im((s - α)/v) > 0`); `IsCutDisc` is the paper's disc `V` of the access lemma (meets no other cut, no
  catalogue point, stays in `ℍ`).
* `segInt f z₁ z₂ = ∫_{[z₁,z₂]} f` (straight segment), `Kern s w = Γ(w)Γ(s-w)/Γ(s)` (`K_s`), `J a b`
  (`J_{ab}`), `X α` (`X_α = 2λ₁λ_a J_{1a}`; with `λ₁ = -1`, `λ_a = -Res_a Q` this is
  `2·Res_a(Q)·J_{1a}`), `Mon α = 2πi X α` (`M_α`), `MSpan` (finite integer combinations of the `M_α`).
* `Eaux` is the paper's `E` (holomorphic part of `P` on `H_{1/2}`), `Pv κ` the slanted branch `P_v`.
* `wb κ b = 1 - (1-b)v` (`w_b`). The segment `𝒮 = 𝒮_b` is parametrised as `x = 1 - u v`,
  `u ∈ [0, 1-b]`; `∫_𝒮 f(x) dx = v ∫_0^{1-b} f(1 - u v) du`.
* **Continuation of `P` along `s - 𝒮` as an explicit integral**: `PsegA κ b A s u`
  is `A(s - w_b) + v ∫_u^{1-b} Q(s - 1 + u' v) du'`, i.e. the anchor value `A(s - w_b)` minus the
  integral of `Q = -P'` from `s - w_b` to `s - 1 + u v` along the straight segment. With `A = Pv κ` this
  is the paper's `P^{[s]}(s - x)`. `N1A κ b A` is the paper's `N₁^♮` with anchor function `A`
  (`N1nat = N1A (Pv κ)`); replacing `A` is exactly the paper's "replace the anchor value" (the access lemma
  case (iii)). No monodromy theorem is needed: every homotopy statement becomes a property of an
  explicit parametric integral.
* `Yf` (`Y`), `Dc` (`𝒟`, as the iterated integral `∫_𝒮 Γ(x) Y(s-x) dx`), `phiD` (the paper's `φ`),
  `N1ser` (`N₁` with the Dirichlet series `P`), `Htil` (`H̃_b`, chosen by `decomp_exists`), `Gb`
  (`G^♮_b`), `Gnat` (`G^♮`, using `b = bOf s`).
* For the decomposition (the `F₀` splitting, the decomposition): `F0` (`F₀`), `Lf` (`L`), `h0` (`h₀`),
  `Eb`, `CauchyS` (`∫_𝒮 dx/(z-x)`), `e0inf` (`e_∞`), `Sseg` (the set `𝒮`).
* `IsPrincipalSheet κ Gn` packages what the later results use about `G^♮`: holomorphy on `Ω_ℍ`,
  `= G` on `σ > 2`, the local model, and the access lemma. Everything downstream (jump,
  branches, boundary) is proved for an arbitrary `Gn` with this property.
* `IsBranch κ Gn p f`: near `p`, at every point of `Ω_ℍ`, the germ of `f` is `Gn + m` with
  `m ∈ MSpan` (the paper's family `𝔉_p` of the branch proposition).
* `UniformFamily B U`: the abstract hypothesis under which germ families continue along every path
  in `U` (abstracted from the proof of the branch proposition).

## Junk values

`Qcont`, `Pv`, `logAt` are junk on their singular sets; `intervalIntegral` and `VerticalIntegral'`
are `0` on non-integrable integrands; `Γ` is junk at its poles. Every lemma that evaluates one of
these objects does so only where it is genuinely defined (stated in its hypotheses); see the
docstring of each lemma.

The oriented interval formulas (`N1A`, `N1ser`, `Yf`, `Dc`, `Lf`, `CauchyS`, all of the form
`v ∫_0^{1-b} … du`) are the paper's integrals over `𝒮` only for the paper's parameter range
(`b < 1`, in fact `b ∈ (1/2, 1)` or `(0, 1)` as each lemma states). For `b ≥ 1` the interval
`[0, 1-b]` is a point or reversed, and the formulas no longer mean what their docstrings say.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-- Copy of `Statements.lean`'s `IsGoodSlant` (same body, so definitionally equal): `κ ∈ (-1,1) ∖ {0}`
and, with `v = 1 + iκ`, no two distinct points of `𝒞` differ by a real multiple of `v`. -/
def IsGoodSlant (κ : ℝ) : Prop :=
  κ ≠ 0 ∧ |κ| < 1 ∧
    ∀ α ∈ catalogue, ∀ α' ∈ catalogue, α ≠ α' → ∀ t : ℝ, α - α' ≠ (t : ℂ) * slantDir κ

/-! ## Geometry of the slanted cuts -/

/-- The paper's `Ω_ℍ = ℍ ∖ ⋃_{α ∈ 𝒞} cut_α`. -/
def Omega (κ : ℝ) : Set ℂ := HH \ ⋃ α ∈ catalogue, cut (slantDir κ) α

/-- The `+` part `V⁺` of the disc `V = Δ(s₀, r)` centred on `cut_α`: the side in direction `+iv`. -/
def upperPart (κ : ℝ) (α s₀ : ℂ) (r : ℝ) : Set ℂ :=
  {s | s ∈ ball s₀ r ∧ 0 < ((s - α) / slantDir κ).im}

/-- The `-` part `V⁻`. -/
def lowerPart (κ : ℝ) (α s₀ : ℂ) (r : ℝ) : Set ℂ :=
  {s | s ∈ ball s₀ r ∧ ((s - α) / slantDir κ).im < 0}

/-- The disc `Δ(s₀, r)` (with `s₀ ∈ cut_α`) is a disc as in the access lemma: it lies in `ℍ`, does not
contain `α`, and meets no other cut (hence no catalogue point, as `α' ∈ cut_{α'}`).

The predicate itself does not require `0 < r` or `s₀ ∈ cut_α`; callers supply these as separate
hypotheses. -/
def IsCutDisc (κ : ℝ) (α s₀ : ℂ) (r : ℝ) : Prop :=
  ball s₀ r ⊆ HH ∧ α ∉ ball s₀ r ∧
    ∀ α' ∈ catalogue, α' ≠ α → Disjoint (ball s₀ r) (cut (slantDir κ) α')

/-! ## The kernel and the coefficients `X_α` (the kernel lemma, the local model) -/

/-- Integral of `f` along the straight segment `[z₁, z₂]`. -/
def segInt (f : ℂ → ℂ) (z₁ z₂ : ℂ) : ℂ :=
  (z₂ - z₁) * ∫ τ in (0 : ℝ)..1, f (z₁ + (τ : ℂ) * (z₂ - z₁))

/-- The Mellin–Barnes kernel `K_s(w) = Γ(w)Γ(s-w)/Γ(s)`. -/
def Kern (s w : ℂ) : ℂ := Gamma w * Gamma (s - w) / Gamma s

/-- `J_{ab}(s) = ∫_a^{s-b} K_s(w) dw` along the straight segment. -/
def J (a b s : ℂ) : ℂ := segInt (Kern s) a (s - b)

/-- The coefficient `X_α` of the local model: `X_2 = J_{11}` and, for `α = 1 + a ≠ 2`,
`X_α = 2λ₁λ_a J_{1a} = 2 Res_a(Q) J_{1a}` (`λ₁ = -1`, `λ_a = -Res_a Q`). Does not depend on `κ`. -/
def X (α s : ℂ) : ℂ := if α = 2 then J 1 1 s else 2 * sigmaRes (α - 1) * J 1 (α - 1) s

/-- The monodromy `M_α = 2πi X_α`. -/
def Mon (α : ℂ) : ℂ → ℂ := fun s => 2 * (Real.pi : ℂ) * I * X α s

/-- Finite integer combinations `∑ ν_α M_α` (the paper's `∑ ν_{α'} M_{α'}`). -/
def MSpan : AddSubgroup (ℂ → ℂ) := AddSubgroup.closure (Mon '' catalogue)

/-! ## The slanted branch `P_v` -/

/-- The paper's `E`: holomorphic on `H_{1/2}`, `= P + Log(z-1)` on `ℍ` (exists under RH; chosen,
`0` if it does not exist). -/
def Eaux : ℂ → ℂ :=
  open Classical in
  if h : ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (halfPlane (1 / 2)) ∧
      ∀ z ∈ HH, E z = P z + Complex.log (z - 1) then h.choose else 0

/-- The paper's `P_v(z) = -Log_v(z-1) + E(z)`, with `Log_v(z-1) = Log((z-1)/v) + Log v` (the branch
of `log(z-1)` cut along `1 - [0,∞)v` that is principal on `ℍ`, for `|κ| < 1`). -/
def Pv (κ : ℝ) (z : ℂ) : ℂ := Eaux z - (logAt (slantDir κ) 1 z + Complex.log (slantDir κ))

/-! ## The decomposition and the principal sheet -/

/-- `w_b = 1 - (1-b)v`, the far end of `𝒮_b`. -/
def wb (κ b : ℝ) : ℂ := 1 - ((1 - b : ℝ) : ℂ) * slantDir κ

/-- The set `𝒮_b = {1 - u v : 0 ≤ u ≤ 1-b}`. -/
def Sseg (κ b : ℝ) : Set ℂ := {z | ∃ u ∈ Icc (0 : ℝ) (1 - b), z = 1 - (u : ℂ) * slantDir κ}

/-- `𝒮 + 𝒮 = {2 - w v : 0 ≤ w ≤ 2(1-b)}`. -/
def segSS (κ b : ℝ) : Set ℂ := {s | ∃ w ∈ Icc (0 : ℝ) (2 * (1 - b)), s = 2 - (w : ℂ) * slantDir κ}

/-- `P` continued along the segment `s - 𝒮` from the anchor value `A(s - w_b)`, evaluated at
`s - x`, `x = 1 - u v`: `A(s - w_b) + v ∫_u^{1-b} Q(s - 1 + u' v) du'` (since `P' = -Q`).
This is an anchored primitive: it represents the continuation of `P` along `s - 𝒮` only when `A`
supplies the right branch of `P` at the anchor `s - w_b`; for any other `A` it is just the formula. -/
def PsegA (κ b : ℝ) (A : ℂ → ℂ) (s : ℂ) (u : ℝ) : ℂ :=
  A (s - wb κ b) + slantDir κ * ∫ u' in u..(1 - b), Qcont (s - 1 + (u' : ℂ) * slantDir κ)

/-- `N₁` with anchor function `A`: `∫_𝒮 Γ(x)Γ(s-x) P^{[s]}(s-x) dx` (for `b < 1`; see the module
docstring on the oriented interval formulas). Inherits the caveat of `PsegA`: it is the paper's `N₁`
only when `A` supplies the right branch of `P` at the anchor `s - w_b`. -/
def N1A (κ b : ℝ) (A : ℂ → ℂ) (s : ℂ) : ℂ :=
  slantDir κ * ∫ u in (0 : ℝ)..(1 - b),
    Gamma (1 - (u : ℂ) * slantDir κ) * Gamma (s - 1 + (u : ℂ) * slantDir κ) * PsegA κ b A s u

/-- The paper's `N₁^♮` (anchor function `P_v`). -/
abbrev N1nat (κ b : ℝ) : ℂ → ℂ := N1A κ b (Pv κ)

/-- The paper's `N₁` of the decomposition, with the Dirichlet series `P` (meaningful for `σ > 2` and
`0 < b < 1`; at `b = 0` the far end `w_0 = 1 - v = -iκ` of `𝒮` is the pole `0` of `Γ` when `κ = 0`). -/
def N1ser (κ b : ℝ) (s : ℂ) : ℂ :=
  slantDir κ * ∫ u in (0 : ℝ)..(1 - b),
    Gamma (1 - (u : ℂ) * slantDir κ) * Gamma (s - 1 + (u : ℂ) * slantDir κ) *
      P (s - 1 + (u : ℂ) * slantDir κ)

/-- The paper's `Y(z) = ∫_𝒮 Γ(x)/(z-x) dx` (meaningful for `z ∉ 𝒮` and `0 < b < 1`; at `b = 0` the far end `w_0 = 1 - v = -iκ` of `𝒮` is the pole `0` of `Γ` when `κ = 0`). -/
def Yf (κ b : ℝ) (z : ℂ) : ℂ :=
  slantDir κ * ∫ u in (0 : ℝ)..(1 - b), Gamma (1 - (u : ℂ) * slantDir κ) / (z - 1 + (u : ℂ) * slantDir κ)

/-- The paper's `𝒟(s) = ∬ Γ(x)Γ(y)/(s-x-y) = ∫_𝒮 Γ(x) Y(s-x) dx` (meaningful for `s ∉ 𝒮 + 𝒮` and
`0 < b < 1`; at `b = 0` the far end `w_0 = 1 - v = -iκ` of `𝒮` is the pole `0` of `Γ` when `κ = 0`). -/
def Dc (κ b : ℝ) (s : ℂ) : ℂ :=
  slantDir κ * ∫ u in (0 : ℝ)..(1 - b),
    Gamma (1 - (u : ℂ) * slantDir κ) * Yf κ b (s - 1 + (u : ℂ) * slantDir κ)

/-- The paper's `φ(w) = ∫_{u+u'=w, 0≤u,u'≤1-b} Γ(1-uv)Γ(1-u'v) du` (the access lemma (ii)), for
`0 ≤ w ≤ 2(1-b)` only. Outside that range the bounds `max 0 (w-(1-b))` and `min w (1-b)` cross, and
the interval integral is a signed junk value, not the (empty) slice integral `0`. -/
def phiD (κ b : ℝ) (w : ℝ) : ℂ :=
  ∫ u in (max 0 (w - (1 - b)))..(min w (1 - b)),
    Gamma (1 - (u : ℂ) * slantDir κ) * Gamma (1 - ((w - u : ℝ) : ℂ) * slantDir κ)

/-- The paper's `H̃_b`, chosen from `decomp_exists` (`0` if no such function exists). -/
def Htil (κ b : ℝ) : ℂ → ℂ :=
  open Classical in
  if h : ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (halfPlane (2 * b)) ∧
      ∀ s : ℂ, 2 < s.re → Gamma s * G s = 2 * N1ser κ b s - Dc κ b s + H s then h.choose else 0

/-- The paper's `G^♮_b = (2N₁^♮ - 𝒟 + H̃_b)/Γ`. -/
def Gb (κ b : ℝ) (s : ℂ) : ℂ := (2 * N1nat κ b s - Dc κ b s + Htil κ b s) / Gamma s

/-- A choice of `b ∈ (1/2, 1)` with `2b < σ`, for `σ > 1`. -/
def bOf (s : ℂ) : ℝ := (1 / 2 + min (s.re / 2) 1) / 2

/-- The principal sheet `G^♮` (the principal-sheet proposition): `G^♮_b` with `b = bOf s`. -/
def Gnat (κ : ℝ) (s : ℂ) : ℂ := Gb κ (bOf s) s

/-! ## Objects of the `F₀` splitting and the decomposition -/

/-- `F₀(t) = ∑_p e^{-pt}` (meaningful for `t > 0`). -/
def F0 (t : ℝ) : ℝ := ∑' p : Nat.Primes, Real.exp (-((p : ℕ) * t))

/-- `L(t) = ∫_𝒮 Γ(x) t^{-x} dx` (for `0 < b < 1`; at `b = 0` the far end `w_0 = 1 - v = -iκ` of `𝒮` is the pole `0` of `Γ` when `κ = 0`). -/
def Lf (κ b : ℝ) (t : ℝ) : ℂ :=
  slantDir κ * ∫ u in (0 : ℝ)..(1 - b),
    Gamma (1 - (u : ℂ) * slantDir κ) * (t : ℂ) ^ (-(1 - (u : ℂ) * slantDir κ))

/-- `h₀(t) = (2πi)⁻¹ ∫_{(b)} Γ(z) P_v(z) t^{-z} dz`. -/
def h0 (κ b : ℝ) (t : ℝ) : ℂ := VerticalIntegral' (fun z => Gamma z * Pv κ z * (t : ℂ) ^ (-z)) b

/-- `E_b(z) = E(z) - Log_v(z - w_b)`, holomorphic on `Re z > b` under RH and for `b ≥ 1/2` only
(`Eaux` is the paper's `E` only under RH, and gives no regularity below `Re z = 1/2`). It equals `P_v` minus
`∫_𝒮 dx/(z-x)` only off `𝒮` (`Pv_eq_Eb_add` asks for `z` off the ray `1 - [0,∞)v`) and for the
paper's range of `b` (`b < 1`). -/
def Eb (κ b : ℝ) (z : ℂ) : ℂ :=
  Eaux z - (Complex.log ((z - wb κ b) / slantDir κ) + Complex.log (slantDir κ))

/-- `∫_𝒮 dx/(z - x)` (meaningful for `z ∉ 𝒮` and `b < 1`). -/
def CauchyS (κ b : ℝ) (z : ℂ) : ℂ :=
  slantDir κ * ∫ u in (0 : ℝ)..(1 - b), 1 / (z - 1 + (u : ℂ) * slantDir κ)

/-- `e_∞(z) = ∫_1^∞ F₀(t) t^{z-1} dt` (entire). -/
def e0inf (z : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (F0 t : ℂ) * (t : ℂ) ^ (z - 1)

/-! ## Packaged properties of the principal sheet -/

/-- What the later results use about the principal sheet `Gn` (for the slope `κ`):
holomorphy on `Ω_ℍ`, agreement with `G` on `σ > 2`, the local model at every
`α ∈ 𝒞`, and the access discs at every point of every cut. -/
structure IsPrincipalSheet (κ : ℝ) (Gn : ℂ → ℂ) : Prop where
  analyticOn : AnalyticOnNhd ℂ Gn (Omega κ)
  eq_G : EqOn Gn G (halfPlane 2)
  local_form : ∀ α ∈ catalogue, ∃ r : ℝ, 0 < r ∧ r ≤ α.re - 1 ∧
    slitDisc (slantDir κ) α r ⊆ Omega κ ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball α r) ∧
      EqOn Gn (fun s => X α s * logAt (slantDir κ) α s + H s) (slitDisc (slantDir κ) α r)
  access : ∀ α ∈ catalogue, ∀ s₀ ∈ cut (slantDir κ) α, s₀ ≠ α →
    ∃ r : ℝ, 0 < r ∧ IsCutDisc κ α s₀ r ∧
      ∃ Gp : ℂ → ℂ, AnalyticOnNhd ℂ Gp (ball s₀ r) ∧ EqOn Gp Gn (upperPart κ α s₀ r)

/-- `f` is a branch at `p` in the sense of the branch proposition: analytic at `p`, and near `p` its germ
at every point of `Ω_ℍ` is that of `Gn + ∑ ν_α M_α`.

The second clause is vacuous at a point `p` with a neighbourhood that misses `Ω_ℍ`; `IsBranch` is
used only at points of `ℍ ∖ 𝒞`. -/
def IsBranch (κ : ℝ) (Gn : ℂ → ℂ) (p : ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f p ∧ ∀ᶠ q in 𝓝 p, q ∈ Omega κ → ∃ m ∈ MSpan, f =ᶠ[𝓝 q] fun s => Gn s + m s

/-- A germ family `B` (pairs point/function) is *uniform* on `U` if every `p ∈ U` has a disc on
which every member of the family at a point of the disc is represented by a function holomorphic
on the whole disc and in the family at every point of the disc (the discs `V_p` of
the branch proposition). -/
def UniformFamily (B : ℂ → (ℂ → ℂ) → Prop) (U : Set ℂ) : Prop :=
  ∀ p ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ q ∈ ball p r, ∀ f : ℂ → ℂ, B q f →
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball p r) ∧ F =ᶠ[𝓝 q] f ∧ ∀ q' ∈ ball p r, B q' F

/-! ## Paths -/

/-- Concatenation of two paths `γ₁`, `γ₂` with `γ₂ 0 = γ₁ 1` (`Path.trans`). -/
def concatPath (γ₁ γ₂ : C(unitInterval, ℂ)) (h : γ₂ 0 = γ₁ 1) : C(unitInterval, ℂ) :=
  ((⟨γ₁, rfl, rfl⟩ : Path (γ₁ 0) (γ₁ 1)).trans (⟨γ₂, h, rfl⟩ : Path (γ₁ 1) (γ₂ 1))).toContinuousMap

/-- `s ↦ s t` on `[0,1]`. -/
def scaleMap (t : unitInterval) : C(unitInterval, unitInterval) :=
  ⟨fun s => ⟨(s : ℝ) * t, unitInterval.mul_mem s.2 t.2⟩, by fun_prop⟩

end GoldbachBoundaries.ThmA
