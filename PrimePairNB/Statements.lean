import PrimePairNB.Defs
import PrimePairNB.ZetaRealNonvanishing
import PrimePairNB.SigmaFinite
import PrimePairNB.SigmaMeromorphic
import PrimePairNB.TIdentity.Assembly
import PrimePairNB.Density
import PrimePairNB.TBoundary
import PrimePairNB.ThmA.Skeleton

/-!
# Statements of the RH development

This file states the main results the paper cites (see the table in the release README). It is the
file to read to see what is claimed. `RiemannHypothesis` (Mathlib's `def`) is an explicit premise wherever
RH is assumed. There are no `axiom`s; each statement is closed by `exact` from a proof file
elsewhere in the library.

Contents:

* Section 1: sanity lemmas. They check that the definitions mean what they should (multiplicities
  are `≥ 1`, RH puts zeros on the line, `𝒞 ⊆ ℍ`, `𝒞 = 1 + Σ`) and that the hypotheses of the main
  statements can be met (an admissible germ exists).
* Section 2: preliminaries on the pole set `Σ` and the density of the points `ρ/n`.
* Section 3: the pole description of `T`, with the identity for `T` and the natural boundary of `T`.
* Section 4: the theorem on `G`: continuation along paths, the local form of every branch, the
  natural boundary (`thm_G_boundary` and its strong form `thm_A_no_extension`), the every-path
  statement, and the path-concatenation lemma. `thm_A` is assembled from the parts by a one-line proof.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-! ## 1. Sanity lemmas -/

/-- `ζ` is analytic away from `1`. -/
lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

lemma ne_one_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 1 := by
  rintro rfl
  simp [NontrivialZeros] at hρ

lemma ne_zero_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 0 := by
  rintro rfl
  simp [NontrivialZeros] at hρ

/-- Sanity: `m(ρ) ≥ 1` at every non-trivial zero (so `zetaMult` is the multiplicity, not a junk
`0`). -/
theorem one_le_zetaMult {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 ≤ zetaMult ρ := by
  have hne1 := ne_one_of_mem_nontrivialZeros hρ
  have han := analyticAt_riemannZeta hne1
  have hzero : riemannZeta ρ = 0 := hρ.1
  -- ζ is not identically zero near ρ (identity theorem on the connected set `{1}ᶜ`)
  have hcd : riemannZeta ⁻¹' {0}ᶜ ∈ codiscreteWithin ({1} : Set ℂ)ᶜ := by
    refine AnalyticOnNhd.preimage_zero_mem_codiscreteWithin (x := 2)
      (fun z hz => analyticAt_riemannZeta hz) ?_ ?_ ?_
    · exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
    · norm_num
    · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hev : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    have hdisj := (mem_codiscreteWithin.mp hcd) ρ hne1
    have h1 : (({1} : Set ℂ)ᶜ \ riemannZeta ⁻¹' {0}ᶜ)ᶜ ∈ 𝓝[≠] ρ :=
      Filter.disjoint_principal_right.mp hdisj
    have h2 : ∀ᶠ z in 𝓝[≠] ρ, z ∈ ({1} : Set ℂ)ᶜ :=
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne1)
    filter_upwards [h1, h2] with z hz1 hz2 hz3
    exact hz1 ⟨hz2, by simpa using hz3⟩
  have hntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2 hev
  have hA0 : analyticOrderAt riemannZeta ρ ≠ 0 := fun h => (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold zetaMult
  rw [han.meromorphicOrderAt_eq] at hntop ⊢
  cases hO : analyticOrderAt riemannZeta ρ with
  | top => simp [hO] at hntop
  | coe n =>
    have hn : n ≠ 0 := fun h => hA0 (by simp [hO, h])
    rw [ENat.map_natCast, WithTop.untopD_coe]
    simp only [Int.toNat_natCast]
    omega

/-! Uniqueness of the representation of a catalogue point. -/

/-! ## 2. Preliminaries: the pole set of `Q`, the density lemma -/

/-! ## 3. The weighted series `T` -/

/-- **The pole description of `T`.** Paper, Theorem 10.1.

Assume RH. Then `T` is single-valued meromorphic on `ℍ`. Its poles there are exactly the points
of `𝒞`, all simple, with residues `1` at `2`, `2μ(k)` at `1 + 1/k` and `-2μ(n)m(ρ)/ρ` at `1 + ρ/n`,
all non-zero.

Lean: some `F` meromorphic on `ℍ`, equal to the series `T` on `σ > 2`, analytic on `ℍ ∖ 𝒞`,
of order exactly `-1` at every point of `𝒞`, whose residues have the catalogue values and are
non-zero. (Any two such `F` agree off a discrete set, since `ℍ` is connected, so orders and
residues do not depend on the choice.) -/
theorem cor_T_poles (hRH : RiemannHypothesis) :
    ∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ catalogue) ∧
      (∀ α ∈ catalogue, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ catalogue, HasResidue F α (res α)) ∧ HasCatalogueValues res ∧
        ∀ α ∈ catalogue, res α ≠ 0 := by
  exact cor_T_poles_proof hRH

/-! ## 4. The unweighted series `G` -/

/-- `κ` is an admissible slope in the sense of the slant lemma (`ThmA`): `κ ∈ (-1,1) ∖ {0}` and, with
`v = 1 + iκ`, no two distinct points of `𝒞` differ by a real multiple of `v`. -/
def IsGoodSlant (κ : ℝ) : Prop :=
  κ ≠ 0 ∧ |κ| < 1 ∧
    ∀ α ∈ catalogue, ∀ α' ∈ catalogue, α ≠ α' → ∀ t : ℝ, α - α' ≠ (t : ℂ) * slantDir κ

/-- **Continuation of `G`.** Assume RH. The series `G` continues analytically along every path in
`ℍ ∖ 𝒞` that starts in `σ > 2`.

Lean: paths are continuous maps `[0,1] → ℂ`; continuation is `ContinuesAlong` (germ chains,
`Defs.lean`). -/
theorem thm_A_continuation (hRH : RiemannHypothesis) :
    ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ HH \ catalogue) → 2 < (γ 0).re →
      ContinuesAlong G γ := by
  exact ThmA.thm_A_continuation_proof hRH

/-- **Concatenation of continuations.** If `g` is a terminal germ of `F`
along `γ₁` and `g'` a terminal germ of `g` along `γ₂`, where `γ₂` starts at the end of `γ₁`, then
`g'` is a terminal germ of `F` along a path `γ` from `γ₁ 0` to `γ₂ 1` whose points all lie on
`γ₁` or `γ₂` (the concatenation). Pure complex analysis, no RH. -/
theorem isTerminalGerm_trans {F g g' : ℂ → ℂ} {γ₁ γ₂ : C(unitInterval, ℂ)}
    (h₁ : IsTerminalGerm F γ₁ g) (h₁₂ : γ₂ 0 = γ₁ 1) (h₂ : IsTerminalGerm g γ₂ g') :
    ∃ γ : C(unitInterval, ℂ), γ 0 = γ₁ 0 ∧ γ 1 = γ₂ 1 ∧
      (∀ t, γ t ∈ range γ₁ ∪ range γ₂) ∧ IsTerminalGerm F γ g' := by
  exact ThmA.isTerminalGerm_trans_proof h₁ h₁₂ h₂

/-- **Local form of every branch of `G`.**

Near each `α ∈ 𝒞` every branch has the form `X_α(s) log(s - α) + (holomorphic)` on a slit disc
about `α`, with `X_α` holomorphic on `ℍ`, `X_α(α) = 0`, `X_2'(2) = 1`, `X'_{1+1/k}(1 + 1/k) = 2μ(k)` and
`X'_{1+ρ/n}(1 + ρ/n) = -2μ(n)m(ρ)/ρ ≠ 0`.

Lean: a family `X α`, chosen before any slope (it does not depend on `κ`), with `X α` holomorphic
on `ℍ`, `X α α = 0`, and `X'_α(α)` having the catalogue values, all non-zero (for the first two
families this is immediate since `μ(k) ≠ 0` for squarefree `k`). Then for every admissible slope `κ`
(there are such slopes, by `IsGoodSlant`) and every `α ∈ 𝒞` there is `r > 0` such that
every branch `g` at every point `s₁` of the slit disc `Δ(α, r) ∖ cut_α` agrees near `s₁` with
`X α · Log((s - α)/v) + h`, `v = 1 + iκ`, for some `h` holomorphic on the whole disc (`h` depends on
the branch; `r` depends on `κ` and `α`, not on the branch). Other branches of `log(s - α)` differ by
constants, absorbed into `h`. -/
theorem thm_A_local (hRH : RiemannHypothesis) :
    ∃ X : ℂ → ℂ → ℂ,
      (∀ α ∈ catalogue, DifferentiableOn ℂ (X α) HH ∧ X α α = 0) ∧
      HasCatalogueValues (fun α => deriv (X α) α) ∧
      (∀ α ∈ catalogue, deriv (X α) α ≠ 0) ∧
      ∀ κ : ℝ, IsGoodSlant κ → ∀ α ∈ catalogue, ∃ r : ℝ, 0 < r ∧
        ∀ s₁ ∈ slitDisc (slantDir κ) α r, ∀ g : ℂ → ℂ, IsAdmissibleGerm g s₁ →
          ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball α r) ∧
            g =ᶠ[𝓝 s₁] fun s => X α s * logAt (slantDir κ) α s + h s := by
  exact ThmA.thm_A_local_proof hRH

/-- **The boundary theorem for `G`.** Assume RH. Let `g` be an admissible germ at `s₁ ∈ ℍ`. For no
`y ∈ ℝ` and `r > 0` with `s₁ ∈ disc(1 + iy, r)` is there a meromorphic function `f` on that disc whose
germ at `s₁` is `g`.

Lean: "germ of `f` at `s₁` is `g`" is `f =ᶠ[𝓝[≠] s₁] g` (`GermExtendsMeromorphically`); this is
equivalent to `=ᶠ[𝓝 s₁]` and does not read `f s₁`. -/
theorem thm_G_boundary (hRH : RiemannHypothesis) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : IsAdmissibleGerm g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  exact ThmA.thm_G_boundary_proof hRH hg y r hr hs₁

/-- **Every path stays in `ℍ ∖ 𝒞`.** Paper, Theorem 10.1. Every germ obtained from `G` by continuation along
any path in `ℂ` is admissible, and `G` cannot be continued analytically along any path in `ℂ` that
leaves `ℍ ∖ 𝒞`.

Lean: a path that starts in `σ > 2` and along which `G` continues stays in `ℍ ∖ 𝒞`. Then every
germ so obtained is admissible by definition (`rem_every_path_admissible`). -/
theorem rem_every_path (hRH : RiemannHypothesis) :
    ∀ γ : C(unitInterval, ℂ), 2 < (γ 0).re → ContinuesAlong G γ → ∀ t, γ t ∈ HH \ catalogue := by
  exact ThmA.rem_every_path_proof hRH

/-- Every terminal germ of `G` along any path in `ℂ`
starting in `σ > 2` is admissible. Derived from `rem_every_path` (real proof). -/
theorem rem_every_path_admissible (hRH : RiemannHypothesis) (γ : C(unitInterval, ℂ))
    (h0 : 2 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm G γ g) : IsAdmissibleGerm g (γ 1) := by
  obtain ⟨f, hf, hf0, hg1⟩ := hg
  exact ⟨γ, rem_every_path hRH γ h0 ⟨f, hf, hf0⟩, h0, rfl, f, hf, hf0, hg1⟩

/-- The continuation of an admissible germ along *any* path in `ℂ` is again admissible.
Proved from `isTerminalGerm_trans` and `rem_every_path`. -/
theorem admissible_continuation_any_path (hRH : RiemannHypothesis) {g g' : ℂ → ℂ} {s₁ : ℂ}
    (hg : IsAdmissibleGerm g s₁) (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s₁)
    (hg' : IsTerminalGerm g γ g') : IsAdmissibleGerm g' (γ 1) := by
  obtain ⟨γ₁, -, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, -, hδ⟩ := isTerminalGerm_trans hterm (hγ0.trans h1.symm) hg'
  have h2' : 2 < (δ 0).re := by rw [hδ0]; exact h2
  have := rem_every_path_admissible hRH δ h2' hδ
  rwa [hδ1] at this

/-- **No branch extends meromorphically to any disc centred on a point of the line**, in the strong
reading: the branch `g` at `s₁` need not lie in the disc;
continue it along any path `γ` in `ℂ` from `s₁` to a point `γ 1` of the disc, and the germ reached
there does not extend meromorphically to the disc. Proved from `admissible_continuation_any_path`
and `thm_G_boundary`; with the constant path it gives back `thm_G_boundary`. -/
theorem thm_A_no_extension (hRH : RiemannHypothesis) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : IsAdmissibleGerm g s₁) (γ : C(unitInterval, ℂ)) (g' : ℂ → ℂ) (hγ0 : γ 0 = s₁)
    (hg' : IsTerminalGerm g γ g') (y r : ℝ) (hr : 0 < r) (hγ1 : γ 1 ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g' (γ 1) (ball (1 + (y : ℂ) * I) r) :=
  thm_G_boundary hRH (admissible_continuation_any_path hRH hg γ hγ0 hg') y r hr hγ1

/-- **The theorem on `G`.** Paper, Theorem 10.1. Assume RH. `G` continues analytically along every path in
`ℍ ∖ 𝒞` that starts in `σ > 2`; every branch has the local form above; no branch extends
meromorphically to any disc centred on a point of the line `σ = 1`; and `G` cannot be continued
analytically along any path in `ℂ` that leaves `ℍ ∖ 𝒞`.

Lean: the conjunction of `thm_A_continuation`, `thm_A_local`, `thm_A_no_extension` (the strong
reading of the third claim: branches continued along any path into the disc) and
`rem_every_path`; proved from them. -/
theorem thm_A (hRH : RiemannHypothesis) :
    (∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ HH \ catalogue) → 2 < (γ 0).re →
      ContinuesAlong G γ) ∧
    (∃ X : ℂ → ℂ → ℂ,
      (∀ α ∈ catalogue, DifferentiableOn ℂ (X α) HH ∧ X α α = 0) ∧
      HasCatalogueValues (fun α => deriv (X α) α) ∧
      (∀ α ∈ catalogue, deriv (X α) α ≠ 0) ∧
      ∀ κ : ℝ, IsGoodSlant κ → ∀ α ∈ catalogue, ∃ r : ℝ, 0 < r ∧
        ∀ s₁ ∈ slitDisc (slantDir κ) α r, ∀ g : ℂ → ℂ, IsAdmissibleGerm g s₁ →
          ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball α r) ∧
            g =ᶠ[𝓝 s₁] fun s => X α s * logAt (slantDir κ) α s + h s) ∧
    (∀ (g : ℂ → ℂ) (s₁ : ℂ), IsAdmissibleGerm g s₁ →
      ∀ (γ : C(unitInterval, ℂ)) (g' : ℂ → ℂ), γ 0 = s₁ → IsTerminalGerm g γ g' →
        ∀ y r : ℝ, 0 < r → γ 1 ∈ ball (1 + (y : ℂ) * I) r →
          ¬ GermExtendsMeromorphically g' (γ 1) (ball (1 + (y : ℂ) * I) r)) ∧
    (∀ γ : C(unitInterval, ℂ), 2 < (γ 0).re → ContinuesAlong G γ → ∀ t, γ t ∈ HH \ catalogue) :=
  ⟨thm_A_continuation hRH, thm_A_local hRH,
    fun _ _ hg γ g' h0 hg' y r hr h1 => thm_A_no_extension hRH hg γ g' h0 hg' y r hr h1,
    rem_every_path hRH⟩

end GoldbachBoundaries
