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
# HInf: definitions for the natural boundary of `G` and `S` under `(H_∞)`

Everything here has a real proof or no proof obligation; the main statements are in the other files of `HInf/`.

Reused without change: `P`, `Q`, `G`, `Qcont`, `PoleSetQ`, `Pinch` (`Σ + Σ`), `pinchPairs`, `cP`, `Binf`, `Bsup`, `Hinf`, `slantDir`, `pairSum`, `KS`, `kerG`, `kerS`, `WS`, `Dser`,
`Aff`, `catalogueL`, `IsAdmissibleGermOn`, `GermExtendsMeromorphically`, (Z1) to (Z6).

## Direction as a slope

The direction `e = e^{iθ}`, `θ ∈ (-π/2, π/2)`, is written here as the slope `κ = tan θ`, with direction vector
`slantDir κ = 1 + iκ = e / cos θ`, as in `ThmA`. The two parametrisations are the same set of cuts, and `θ < θ'` iff
`κ < κ'`. Trigonometry disappears: `Re (slantDir κ) = 1`, so a point moves east by `t` in real part when it moves by
`t · slantDir κ`. `ThmA.IsGoodSlant` also asks `κ ≠ 0` and `|κ| < 1`; nothing here does.

`Log_θ(y) = iθ + Log(y/e)` is `logK κ y = Log(y / slantDir κ) + Log(slantDir κ)`: the same function,
because `Log(y/v) = Log(y/e) - log|v|` and `Log v = log|v| + iθ` (with `|v| = 1 / cos θ`).

## Two cases, one notation

`v` is the pinch variable. `G`: `v = s`, kernel `kerG`, `top = ⊤`. `S`: `v = 2s + 1`, kernel `kS`, `top = 3`. The domain
`𝒱 = {1 < Re v < top}` is `Vt top`, and `𝒱_∞ = 𝒱 ∩ {Re v > 2B_∞}` is `VInf top`.

## Junk values

`Pth κ` is junk where its segment meets a pole of `Qcont`, that is off `Uth κ`. `graphInt` is `0` on a non-integrable
integrand. `Dth` is `0` where no separating graph exists, that is off `Om κ top` (`exists_separating_iff`). `Xc k x` is a
`tsum` over the subtype `pinchPairs x`; it is the finite sum when `Re x > 2B_∞` (`pinchPairs_finite`), and it is used
only there. `Gamma` is junk at its poles; `kerG`, `kS` are read only inside `0 < Re z < Re v`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf

/-! ## Direction, height, abscissa -/

/-- The `θ`-height `h(w) = Im(w/e)`, up to the positive factor between `e` and `slantDir κ`. Two points are on
one `θ`-line iff they have the same `hgt` (`w' - w ∈ ℝ · slantDir κ`). -/
def hgt (κ : ℝ) (w : ℂ) : ℝ := (w / slantDir κ).im

/-- The `θ`-abscissa `x(w) = Re(w/e)`, up to the same factor. East is increasing `absc`. -/
def absc (κ : ℝ) (w : ℂ) : ℝ := (w / slantDir κ).re

/-- `Log_θ`: a branch of `log y` with cut `y ∈ -[0,∞) · slantDir κ`, equal to the principal `Log` on `Re y > 0`. -/
def logK (κ : ℝ) (y : ℂ) : ℂ := Complex.log (y / slantDir κ) + Complex.log (slantDir κ)

/-- The full ray running west from `a` in direction `κ`: `a - [0,∞) · slantDir κ`. -/
def rayW (κ : ℝ) (a : ℂ) : Set ℂ := {z | ∃ t : ℝ, 0 ≤ t ∧ z = a - (t : ℂ) * slantDir κ}

/-- `κ` is **generic**: no two distinct points of `Σ`, and no two distinct points of `Σ + Σ`, lie on one
`κ`-line. Only `X = (Σ + Σ) ∩ {Re v > 2B_∞}` is needed; here it is asked of all of `Σ + Σ`, which is still true
for all but countably many `κ` (`generic_cocountable`) and does not depend on `B_∞`. -/
def IsGenericSlope (κ : ℝ) : Prop :=
  (∀ a ∈ PoleSetQ, ∀ a' ∈ PoleSetQ, a ≠ a' → ∀ t : ℝ, a - a' ≠ (t : ℂ) * slantDir κ) ∧
    ∀ x ∈ Pinch, ∀ x' ∈ Pinch, x ≠ x' → ∀ t : ℝ, x - x' ≠ (t : ℂ) * slantDir κ

/-! ## Regions and cuts -/

/-- `𝒱 = {1 < Re v < top}`. `top = ⊤` for `G`, `top = 3` for `S`. -/
def Vt (top : EReal) : Set ℂ := {v | 1 < v.re ∧ (v.re : EReal) < top}

/-- `𝒱_∞ = 𝒱 ∩ {Re v > 2B_∞}`. Under `(H_∞)` and (Z1), `VInf top = Vt top` (`VInf_eq_of_Hinf`). -/
def VInf (top : EReal) : Set ℂ := {v | v ∈ Vt top ∧ 2 * Binf < v.re}

/-- The `Ω_θ = 𝒱_∞ ∖ ⋃_{x ∈ X} L_x`. A pinch `x` with `Re x ≤ 2B_∞` has its ray outside `𝒱_∞`, so the union may
run over all of `Pinch`. -/
def Om (κ : ℝ) (top : EReal) : Set ℂ := VInf top \ ⋃ x ∈ Pinch, rayW κ x

/-- The `U_θ = {Re z > 0} ∖ ⋃_{a ∈ Σ} ℓ_a`. -/
def Uth (κ : ℝ) : Set ℂ := halfPlane 0 \ ⋃ a ∈ PoleSetQ, rayW κ a

/-! ## The branch `P^θ` -/

/-- The `P^θ`, as an explicit formula: `P^θ(z) = P(z + 2w) + w ∫_0^2 Q(z + τ w) dτ`, `w = slantDir κ`.
For `Re z > 0` the point `z + 2w` has real part `> 2`, so `P` is the convergent series. On `Uth κ` the segment stays in
`Uth κ`, where `Qcont` is holomorphic. It stands in for the primitive of `-Q` on the simply connected `U_θ`,
so no simple-connectivity argument is needed. -/
def Pth (κ : ℝ) (z : ℂ) : ℂ :=
  P (z + 2 * slantDir κ) + slantDir κ * ∫ τ in (0 : ℝ)..2, Qcont (z + (τ : ℂ) * slantDir κ)

/-! ## Graphs over height -/

/-- A `κ`-graph `h ↦ slantDir κ · (ξ(h) + ih)`: `ξ` continuous, piecewise differentiable with bounded derivative, and for
`|h| ≥ T` the graph is the vertical line `Re z = c` (`ξ(h) = c + κh`, since `Re(graph) = ξ(h) - κh`). Only these properties
are used. -/
structure SlantGraph (κ : ℝ) where
  ξ : ℝ → ℝ
  cont : Continuous ξ
  c : ℝ
  T : ℝ
  tail : ∀ h : ℝ, T ≤ |h| → ξ h = c + κ * h
  brk : Finset ℝ
  diff : ∀ h : ℝ, h ∉ brk → DifferentiableAt ℝ ξ h
  lip : ∃ L : ℝ, ∀ h : ℝ, h ∉ brk → |deriv ξ h| ≤ L

/-- The point of the graph at height `h`. -/
def SlantGraph.pt {κ : ℝ} (Γ : SlantGraph κ) (h : ℝ) : ℂ := slantDir κ * ((Γ.ξ h : ℂ) + (h : ℂ) * I)

/-- `(2πi)⁻¹ ∫_Γ f(z) dz`, as a Bochner integral over the height. On the line `Re z = c` it is PNT+'s
`VerticalIntegral' f c` (`graphInt_line`). -/
def graphInt {κ : ℝ} (Γ : SlantGraph κ) (f : ℂ → ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ h : ℝ, f (Γ.pt h) * (slantDir κ * (((deriv Γ.ξ h : ℝ) : ℂ) + I))

/-- The line `Re z = c` as a `κ`-graph. -/
def SlantGraph.line (κ c : ℝ) : SlantGraph κ where
  ξ := fun h => c + κ * h
  cont := by fun_prop
  c := c
  T := 0
  tail := fun _ _ => rfl
  brk := ∅
  diff := fun _ _ => by fun_prop
  lip := ⟨|κ|, fun h _ => by
    have : deriv (fun h : ℝ => c + κ * h) h = κ := by
      simp
    rw [this]⟩

/-- The convex interpolation of two graphs, at parameter `l`, as a point at height `h`. -/
def interpPt {κ : ℝ} (Γ₀ Γ₁ : SlantGraph κ) (l h : ℝ) : ℂ :=
  slantDir κ * ((((1 - l) * Γ₀.ξ h + l * Γ₁.ξ h : ℝ) : ℂ) + (h : ℂ) * I)

/-- A **separating `κ`-graph for `v`**: real parts stay in a compact subset of `(0, Re v)`; the tails are the
line `Re z = c`, `B_∞ < c < Re v - B_∞`; every `a ∈ Σ` is strictly west of the graph on its `κ`-line; every right point
`v - b`, `b ∈ Σ`, is strictly east. -/
structure IsSeparating {κ : ℝ} (v : ℂ) (Γ : SlantGraph κ) : Prop where
  re_mem : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ h : ℝ, ε₁ ≤ (Γ.pt h).re ∧ (Γ.pt h).re ≤ v.re - ε₁
  tail_c : Binf < Γ.c ∧ Γ.c < v.re - Binf
  left : ∀ a ∈ PoleSetQ, absc κ a < Γ.ξ (hgt κ a)
  right : ∀ b ∈ PoleSetQ, Γ.ξ (hgt κ (v - b)) < absc κ (v - b)

/-! ## The kernels -/

/-- The domain of (K1): `{(z, v) : v ∈ 𝒱, 0 < Re z < Re v}`. -/
def domK (top : EReal) : Set (ℂ × ℂ) := {p | p.2 ∈ Vt top ∧ 0 < p.1.re ∧ p.1.re < p.2.re}

/-- What the sheet construction uses about a kernel `k z v` and a series `D` in the variable `v`.
* `holo` is (K1).
* `decay` is the part of (K2) used: uniform decay `(1 + |y|)^{-2}`. The bound `A(1+|t|)^A e^{-π|t|/2}` implies it.
* `mb` is (K3), on `2 < Re v < 3` only. For `G` that is `Paper2.M4b.hypR_kerG_WG`; the identity theorem then gives all of
  `σ > 2` (`Dth_eq_G`). Nothing more than `2 < Re v < 3` is assumed. -/
structure IsPinchKernel (k : ℂ → ℂ → ℂ) (top : EReal) (D : ℂ → ℂ) : Prop where
  three_le : (3 : EReal) ≤ top
  holo : DifferentiableOn ℂ (fun p : ℂ × ℂ => k p.1 p.2) (domK top)
  decay : ∀ C : Set ℂ, IsCompact C → C ⊆ Vt top → ∀ ε₀ : ℝ, 0 < ε₀ → ∃ M : ℝ, ∀ v ∈ C, ∀ x y : ℝ,
    ε₀ ≤ x → x ≤ v.re - ε₀ → ‖k ((x : ℂ) + (y : ℂ) * I) v‖ ≤ M / (1 + |y|) ^ 2
  mb : ∀ v : ℂ, 2 < v.re → v.re < 3 → ∀ c : ℝ, 1 < c → c < v.re - 1 →
    D v = VerticalIntegral' (fun z => k z v * P z * P (v - z)) c

/-- The `f₀` in the variable `v = 2s + 1`: `kS z v = ½ K((2z - v + 3)/4)`, which is `kerS z ((v-1)/2)`. -/
def kS (z v : ℂ) : ℂ := kerS z ((v - 1) / 2)

/-- `S(s) = ∑_{p,q} p^{1-s} q^{2-s} (p²+q²)^{-2}`, the series. Absolutely convergent on `σ > 1/2`. -/
abbrev Sser : ℂ → ℂ := Dser WS

/-- `S` in the variable `v`: `D(v) = S((v - 1)/2)`. -/
def DS (v : ℂ) : ℂ := Sser ((v - 1) / 2)

/-! ## The sheet `D^θ`, the coefficients, the monodromy -/

/-- The integrand of `D^θ`: both factors are the one fixed branch `P^θ`. -/
def pairIntegrand (k : ℂ → ℂ → ℂ) (κ : ℝ) (v z : ℂ) : ℂ := k z v * Pth κ z * Pth κ (v - z)

/-- The `D^θ(v) = (2πi)⁻¹ ∫_Γ 𝒦(z,v) P^θ(z) P^θ(v-z) dz`, `Γ` any separating graph (`Dth_eq_graphInt`); `0` if
there is none. -/
def Dth (k : ℂ → ℂ → ℂ) (κ : ℝ) (v : ℂ) : ℂ := by
  classical
  exact if h : ∃ Γ : SlantGraph κ, IsSeparating v Γ then graphInt h.choose (pairIntegrand k κ v) else 0

/-- `J_{ab}(v) = ∫_a^{v-b} 𝒦(z,v) dz` along the straight segment. The same parametrisation as `Paper2.Jseg` (`Jseg A k a b
s = Jv (…) a b (A.app s)` once `k` is rewritten in `v`). -/
def Jv (k : ℂ → ℂ → ℂ) (a b v : ℂ) : ℂ :=
  (v - a - b) * ∫ t in (0 : ℝ)..1, k (a + (t : ℂ) * (v - a - b)) v

/-- `X_x(v) = ∑_{a + b = x} c(a) c(b) J_{ab}(v)`, over ordered pairs in `Σ²`. Finite when `Re x > 2B_∞`. -/
def Xc (k : ℂ → ℂ → ℂ) (x v : ℂ) : ℂ :=
  ∑' p : pinchPairs x, cP p.1.1 * cP p.1.2 * Jv k p.1.1 p.1.2 v

/-- `M_x = 2πi X_x`. -/
def Mc (k : ℂ → ℂ → ℂ) (x : ℂ) : ℂ → ℂ := fun v => 2 * (Real.pi : ℂ) * I * Xc k x v

/-- The catalogue `X = (Σ + Σ) ∩ {Re v > 2B_∞}`. -/
def Xcat : Set ℂ := {x | x ∈ Pinch ∧ 2 * Binf < x.re}

/-- The `𝓜`: the integer span of the `M_x`, `x ∈ X`. -/
def MSpanK (k : ℂ → ℂ → ℂ) : AddSubgroup (ℂ → ℂ) := AddSubgroup.closure (Mc k '' Xcat)

/-- The `𝔊(q)`, with the constant `C` fixed: germs at `q` of `D^θ + m + C` for some `θ` with `q ∈ Ω_θ` and some
`m ∈ 𝓜`. -/
def GermFam (k : ℂ → ℂ → ℂ) (top : EReal) (C : ℂ) (q : ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ κ : ℝ, q ∈ Om κ top ∧ ∃ m ∈ MSpanK k, f =ᶠ[𝓝 q] fun v => Dth k κ v + m v + C

/-- The open sector in `rotation`: `v₁ + t · slantDir κ''`, `t > 0`, `κ < κ'' < κ'`. -/
def sector (v₁ : ℂ) (κ κ' : ℝ) : Set ℂ :=
  {x | ∃ t : ℝ, 0 < t ∧ ∃ κ'' ∈ Ioo κ κ', x = v₁ + (t : ℂ) * slantDir κ''}

/-- The sum over the catalogue points in a set (finite in every use), as a function of `v`. -/
def sumMc (k : ℂ → ℂ → ℂ) (A : Set ℂ) (v : ℂ) : ℂ := ∑ᶠ x ∈ A ∩ Xcat, Mc k x v

/-! ## The arithmetic sums -/

/-- The `Σ_S` at `x = 1 + u`: `∑_{a + b = x} c(a) c(b) K((a - b + 3)/4)`, written with `R_a R_b = c(a) c(b)` as
`pairSum` is. `Σ_G` is `Paper2.pairSum`. -/
def pairSumS (x : ℂ) : ℂ :=
  ∑' p : pinchPairs x, Rcoef p.1.1 * Rcoef p.1.2 * KS ((p.1.1 - p.1.2 + 3) / 4)

/-! ## The objects of the final statements -/

/-- The catalogue of `G` under `(H_∞)`: `(Σ + Σ) ∩ {σ > 1}`. Under RH it is the RH development's `catalogue`.
Without RH it can be larger: the RH development's `catalogue` is `1 + Σ` only. -/
abbrev catG : Set ℂ := catalogueL Aff.idL

/-- The catalogue of `S`: `{s : σ > 0, 2s + 1 ∈ Σ + Σ}`. -/
abbrev catS : Set ℂ := catalogueL Aff.twoOneL

/-- The admissible germ for `G`: the terminal germ of `G` along a path in `{σ > 1} ∖ X` starting in `σ > 2`. The same
shape as the RH development's `IsAdmissibleGerm`, which is this with `catalogue` for `catG`; they agree under RH,
where the two catalogues coincide. -/
def AdmG (g : ℂ → ℂ) (s₁ : ℂ) : Prop := IsAdmissibleGermOn G (HH \ catG) (halfPlane 2) g s₁

/-- The admissible germ for `S`: the terminal germ of `S` along a path in `{σ > 0} ∖ catalogue` starting in
`σ > 1`. -/
def AdmS (g : ℂ → ℂ) (s₁ : ℂ) : Prop := IsAdmissibleGermOn Sser (halfPlane 0 \ catS) (halfPlane 1) g s₁

/-! ## Auxiliary definitions used by the proofs in `Fill/`

All of these have a real proof or no proof obligation, as with everything in this file. -/

/-- The `A_ε`: a graph `h ↦ ξ h + i h` over `[-r₀, r₀]`, meeting `0` at its ends in real part, staying in
`|t| < 3r₀/2`, with `Re t > 0` at height `0` and `Re t < Re ε` at height `Im ε`. So `t ≤ 0` and `t ∈ ε + [0, ∞)` are both
avoided, on the correct sides. -/
structure IsArc (r₀ : ℝ) (ε : ℂ) (ξ : ℝ → ℝ) : Prop where
  cont : ContinuousOn ξ (Icc (-r₀) r₀)
  brk : ∃ S : Finset ℝ, ∀ h ∈ Ioo (-r₀) r₀, h ∉ S → DifferentiableAt ℝ ξ h
  lip : ∃ L : ℝ, ∀ h ∈ Ioo (-r₀) r₀, |deriv ξ h| ≤ L
  ends : ξ (-r₀) = 0 ∧ ξ r₀ = 0
  small : ∀ h ∈ Icc (-r₀) r₀, ‖(ξ h : ℂ) + (h : ℂ) * I‖ < 3 * r₀ / 2
  west_of : 0 < ξ 0
  east_of : ξ ε.im < ε.re

/-- `(2πi)⁻¹ ∫_{A} F(t) dt` over an arc. -/
def arcInt (r₀ : ℝ) (ξ : ℝ → ℝ) (F : ℂ → ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) *
    ∫ h in (-r₀)..r₀, F ((ξ h : ℂ) + (h : ℂ) * I) * (((deriv ξ h : ℝ) : ℂ) + I)

/-- The left points colliding at `x`: `a ∈ Σ` with `x - a ∈ Σ`. Finite when `Re x > 2B_∞`. -/
def collide (x : ℂ) : Set ℂ := {a | a ∈ PoleSetQ ∧ x - a ∈ PoleSetQ}

/-- The outer region of heights: `|h - h(a)| ≥ r₀` at every colliding `a`. -/
def outerHeights (κ : ℝ) (x : ℂ) (r₀ : ℝ) : Set ℝ := {h | ∀ a ∈ collide x, r₀ ≤ |h - hgt κ a|}

/-- The open ray east from `v₁` in direction `κ`. -/
def rayE (κ : ℝ) (v₁ : ℂ) : Set ℂ := {x | ∃ t : ℝ, 0 < t ∧ x = v₁ + (t : ℂ) * slantDir κ}

/-- `𝔊` is a property of germs. -/
theorem germFam_congr {k : ℂ → ℂ → ℂ} {top : EReal} {C q : ℂ} {f g : ℂ → ℂ} (h : GermFam k top C q f)
    (hfg : f =ᶠ[𝓝 q] g) : GermFam k top C q g := by
  obtain ⟨κ, hκ, m, hm, hf⟩ := h
  exact ⟨κ, hκ, m, hm, hfg.symm.trans hf⟩

end GoldbachBoundaries.HInf
