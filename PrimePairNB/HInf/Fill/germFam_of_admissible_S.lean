import PrimePairNB.HInf.Fill.exists_admS
import PrimePairNB.HInf.Fill.isPinchKernel_S
import PrimePairNB.HInf.Fill.deriv_Jv_kS_extends
import PrimePairNB.HInf.Fill.Dth_eq
import PrimePairNB.HInf.Fill.Dth_analyticOn
import PrimePairNB.HInf.Fill.Xc_analyticOn
import PrimePairNB.HInf.Fill.germFam_slope
import PrimePairNB.HInf.Fill.finite_inter_pinch
import PrimePairNB.HInf.Fill.pinch_countable
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-!
# `germFam_of_admissible_S`

No cutting of the path into pieces: one invariant, and a clopen argument on `[0,1]`. A germ `f` at `p` is
* `famD`: `∃ C, GermFam kS 3 C p f` (so `Re p < 3`), or
* `famR`: `2 < Re p`, and for some `m ∈ 𝓜` and some `M` meromorphic on `ℂ` extending `m'` from `𝒱`, the germ of
  `(f - D)'` is the germ of `M` on a punctured neighbourhood of `p`. The constant is lost here on purpose.

On the strip `2 < Re p < 3` the two agree (`famR_of_famD`, `famD_of_famR`), since `D^θ = D` there. Along the path:
near a point with `Re p < 3` the family `famD` is uniform, as for `G`; near a point with `Re p > 2`, `famR` is
carried by the identity theorem for meromorphic functions, whatever the poles of `M`. The constant `C` changes on each
excursion, and a germ in `Re p ≥ 3` is not claimed to be anything more than `famR`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- `D` is holomorphic on `Re v > 2`. -/
lemma DS_analyticAt {v : ℂ} (h : 2 < v.re) : AnalyticAt ℂ DS v := by
  have hs : AnalyticAt ℂ Sser ((v - 1) / 2) := Sser_analyticAt (by
    have : ((v - 1) / 2).re = (v.re - 1) / 2 := by simp
    rw [this]
    linarith)
  have hm : AnalyticAt ℂ (fun v : ℂ => (v - 1) / 2) v := by fun_prop
  exact AnalyticAt.comp (g := Sser) (f := fun v : ℂ => (v - 1) / 2) hs hm

/-- A finite sum of meromorphic functions. -/
lemma meromorphicAt_finset_sum {ι : Type*} (u : Finset ι) (F : ι → ℂ → ℂ) {z : ℂ}
    (h : ∀ i, MeromorphicAt (F i) z) : MeromorphicAt (fun v => ∑ i ∈ u, F i v) z := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    simp
  | insert i u hi ih =>
    have : (fun v => ∑ j ∈ insert i u, F j v) = fun v => F i v + ∑ j ∈ u, F j v := by
      funext v
      exact Finset.sum_insert hi
    rw [this]
    exact (h i).add ih

/-- `M_x'` extends meromorphically to `ℂ`. -/
lemma exists_mero_deriv_Mc (hZ1 : Z1) {x : ℂ} (hx : x ∈ Xcat) :
    ∃ M : ℂ → ℂ, MeromorphicOn M univ ∧ EqOn M (deriv (Mc kS x)) (Vt 3) := by
  have := finite_pairs hZ1 hx
  have := Fintype.ofFinite (pinchPairs x)
  choose g hgM hgE using fun p : pinchPairs x => deriv_Jv_kS_extends p.2.1 p.2.2.1
  have he : Mc kS x = fun v => 2 * (Real.pi : ℂ) * I *
      ∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 * Jv kS p.1.1 p.1.2 v := by
    funext v
    simp only [Mc, Xc]
    rw [tsum_fintype]
  refine ⟨fun v => 2 * (Real.pi : ℂ) * I * ∑ p : pinchPairs x, cP p.1.1 * cP p.1.2 * g p v, fun v _ => ?_, ?_⟩
  · refine (MeromorphicAt.const _ v).mul (meromorphicAt_finset_sum _ _ fun p => ?_)
    exact (MeromorphicAt.const _ v).mul (hgM p v (mem_univ _))
  · intro v hv
    have hterm : ∀ p : pinchPairs x, HasDerivAt (fun v => cP p.1.1 * cP p.1.2 * Jv kS p.1.1 p.1.2 v)
        (cP p.1.1 * cP p.1.2 * g p v) v := by
      intro p
      rw [hgE p hv]
      exact ((Jv_analyticOn isPinchKernel_S p.2.1 p.2.2.1 v hv).differentiableAt.hasDerivAt).const_mul _
    have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun p _ => hterm p)).const_mul (2 * (Real.pi : ℂ) * I)
    rw [he]
    exact hs.deriv.symm

/-- Every member of `𝓜` has a derivative that extends meromorphically to `ℂ`. -/
lemma exists_mero_deriv_MSpan (hZ1 : Z1) {m : ℂ → ℂ} (hm : m ∈ MSpanK kS) :
    ∃ M : ℂ → ℂ, MeromorphicOn M univ ∧ EqOn M (deriv m) (Vt 3) := by
  induction hm using AddSubgroup.closure_induction with
  | mem f hf =>
    obtain ⟨x, hx, rfl⟩ := hf
    exact exists_mero_deriv_Mc hZ1 hx
  | zero =>
    refine ⟨fun _ => 0, fun v _ => MeromorphicAt.const _ v, fun v _ => ?_⟩
    have : deriv (0 : ℂ → ℂ) v = 0 := by simp
    exact this.symm
  | add f g hf hg ihf ihg =>
    obtain ⟨Mf, hMf, hEf⟩ := ihf
    obtain ⟨Mg, hMg, hEg⟩ := ihg
    refine ⟨fun v => Mf v + Mg v, fun v hv => (hMf v hv).add (hMg v hv), fun v hv => ?_⟩
    have h1 := (MSpanK_analyticOn hZ1 isPinchKernel_S hf v hv).differentiableAt
    have h2 := (MSpanK_analyticOn hZ1 isPinchKernel_S hg v hv).differentiableAt
    have : deriv (f + g) v = deriv f v + deriv g v := deriv_add h1 h2
    rw [this]
    show Mf v + Mg v = _
    rw [hEf hv, hEg hv]
  | neg f hf ihf =>
    obtain ⟨Mf, hMf, hEf⟩ := ihf
    refine ⟨fun v => -Mf v, fun v hv => (hMf v hv).neg, fun v hv => ?_⟩
    have : deriv (-f) v = -deriv f v := deriv.neg
    rw [this]
    show -Mf v = _
    rw [hEf hv]

/-- The germs described by `D^θ + m + C`, the constant free. -/
def famD (p : ℂ) (f : ℂ → ℂ) : Prop := ∃ C : ℂ, GermFam kS 3 C p f

/-- The germs whose difference from `D` has the derivative of a member of `𝓜`, extended meromorphically. -/
def famR (p : ℂ) (f : ℂ → ℂ) : Prop :=
  2 < p.re ∧ ∃ m ∈ MSpanK kS, ∃ M : ℂ → ℂ, MeromorphicOn M univ ∧ EqOn M (deriv m) (Vt 3) ∧
    deriv (fun v => f v - DS v) =ᶠ[𝓝[≠] p] M

lemma famD_congr {p : ℂ} {f g : ℂ → ℂ} (h : famD p f) (hfg : f =ᶠ[𝓝 p] g) : famD p g := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, germFam_congr hC hfg⟩

lemma famD_mem {p : ℂ} {f : ℂ → ℂ} (h : famD p f) : p ∈ Vt 3 := by
  obtain ⟨_, _, hκ, _⟩ := h
  exact hκ.1.1

lemma mem_Vt3 {p : ℂ} (h1 : 1 < p.re) (h3 : p.re < 3) : p ∈ Vt 3 :=
  ⟨h1, (EReal.coe_lt_coe_iff.mpr h3).trans_eq (by norm_cast)⟩

lemma eventually_strip {p : ℂ} (h2 : 2 < p.re) (h3 : p.re < 3) : ∀ᶠ v in 𝓝 p, 2 < v.re ∧ v.re < 3 :=
  ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨h2, h3⟩

/-- On the strip, a germ of `famD` is in `famR`. -/
lemma famR_of_famD (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {p : ℂ} {f : ℂ → ℂ} (h2 : 2 < p.re) (h : famD p f) :
    famR p f := by
  have hpV := famD_mem h
  have h3 := re_lt_three_of_mem hpV
  obtain ⟨C, κ, -, m, hm, hf⟩ := h
  obtain ⟨M, hM, hMe⟩ := exists_mero_deriv_MSpan hZ1 hm
  refine ⟨h2, m, hm, M, hM, hMe, ?_⟩
  have e : (fun v => f v - DS v) =ᶠ[𝓝 p] fun v => m v + C := by
    filter_upwards [hf, eventually_strip h2 h3] with v hv hU
    rw [hv, Dth_eq hZ1 hZ2 hZ3 isPinchKernel_S κ hU.1 hU.2]
    ring
  have d2 : deriv (fun v => m v + C) = deriv m := by
    funext v
    exact deriv_add_const C
  have d := e.deriv
  rw [d2] at d
  have hME : ∀ᶠ v in 𝓝 p, deriv m v = M v := by
    filter_upwards [(isOpen_Vt 3).mem_nhds hpV] with v hv
    exact (hMe hv).symm
  exact (d.trans hME).filter_mono nhdsWithin_le_nhds

/-- On the strip, a germ of `famR` is in `famD`: the derivative determines the germ up to a constant. -/
lemma famD_of_famR (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {p : ℂ} {f : ℂ → ℂ} (h3 : p.re < 3) (hfA : AnalyticAt ℂ f p)
    (h : famR p f) : famD p f := by
  obtain ⟨h2, m, hm, M, -, hMe, hd⟩ := h
  have hpV : p ∈ Vt 3 := mem_Vt3 (by linarith) h3
  have hmA := MSpanK_analyticOn hZ1 isPinchKernel_S hm
  have hDA : AnalyticAt ℂ DS p := DS_analyticAt h2
  set H : ℂ → ℂ := fun v => f v - DS v - m v with hH
  have hHA : AnalyticAt ℂ H p := (hfA.sub hDA).sub (hmA p hpV)
  have hzero : ∀ᶠ v in 𝓝[≠] p, deriv H v = 0 := by
    have h₁ : ∀ᶠ v in 𝓝 p, AnalyticAt ℂ f v := hfA.eventually_analyticAt
    have h₂ : ∀ᶠ v in 𝓝 p, AnalyticAt ℂ DS v := hDA.eventually_analyticAt
    have h₃ : ∀ᶠ v in 𝓝 p, v ∈ Vt 3 := (isOpen_Vt 3).mem_nhds hpV
    filter_upwards [hd, nhdsWithin_le_nhds h₁, nhdsWithin_le_nhds h₂, nhdsWithin_le_nhds h₃] with v hv a1 a2 a3
    have d1 : DifferentiableAt ℂ (fun v => f v - DS v) v := (a1.sub a2).differentiableAt
    have d2 : DifferentiableAt ℂ m v := (hmA v a3).differentiableAt
    have : deriv H v = deriv (fun v => f v - DS v) v - deriv m v := deriv_fun_sub d1 d2
    rw [this, hv, hMe a3, sub_self]
  have hzero' : ∀ᶠ v in 𝓝 p, deriv H v = 0 :=
    hHA.deriv.frequently_zero_iff_eventually_zero.mp hzero.frequently
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hHA.eventually_analyticAt.and hzero')
  refine ⟨H p, 0, mem_Om_of_two_lt hZ1 hpV h2, m, hm, ?_⟩
  have hconst : ∀ y ∈ ball p r, H y = H p := fun y hy =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball p r).isPreconnected
      (fun z hz => (hball z hz).1.differentiableAt.differentiableWithinAt)
      (fun z hz => (hball z hz).2) hy (mem_ball_self hr)
  filter_upwards [ball_mem_nhds p hr, eventually_strip h2 h3] with v hv hU
  rw [Dth_eq hZ1 hZ2 hZ3 isPinchKernel_S 0 hU.1 hU.2, ← hconst v hv]
  simp only [hH]
  ring

/-- The family `famD` is uniform on `𝒱_∞ ∖ X`, with the radius independent of `C`. -/
lemma uniformFamily_famD (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) : ThmA.UniformFamily famD (VInf 3 \ Pinch) := by
  intro p hp
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : ℝ, p ∈ Om κ₀ 3 := by
    obtain ⟨κ₀, hκ₀⟩ := ((countable_not_mem_Om hp.1 hp.2).dense_compl ℝ).nonempty
    exact ⟨κ₀, by simpa using hκ₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_Om hZ1 κ₀ 3) p hκ₀
  refine ⟨r, hr, fun q hq f hf => ?_⟩
  obtain ⟨C, hC⟩ := hf
  obtain ⟨m, hm, hfm⟩ := germFam_slope hZ1 hZ2 hZ3 isPinchKernel_S hC (hball hq)
  have hA : AnalyticOnNhd ℂ (fun v => Dth kS κ₀ v + m v + C) (ball p r) := fun z hz =>
    ((Dth_analyticOn hZ1 hZ2 hZ3 isPinchKernel_S κ₀ z (hball hz)).add
      (MSpanK_analyticOn hZ1 isPinchKernel_S hm z (hball hz).1.1)).add analyticAt_const
  exact ⟨_, hA, hfm.symm, fun q' hq' => ⟨C, κ₀, hball hq', m, hm, EventuallyEq.rfl⟩⟩

/-- A uniform family is locally constant along a continuation: both directions, not only the forward one that
`ThmA.continuationAlong_preserve` gives. -/
lemma uniform_transfer {B : ℂ → (ℂ → ℂ) → Prop} {U : Set ℂ} (hB : ThmA.UniformFamily B U)
    (hcongr : ∀ p f g, B p f → f =ᶠ[𝓝 p] g → B p g) {γ : C(unitInterval, ℂ)} {f : unitInterval → ℂ → ℂ}
    (hf : IsContinuationAlong γ f) {t₀ : unitInterval} (ht₀ : γ t₀ ∈ U) :
    ∀ᶠ s in 𝓝 t₀, (B (γ s) (f s) ↔ B (γ t₀) (f t₀)) := by
  obtain ⟨r, hr, hun⟩ := hB _ ht₀
  obtain ⟨r₁, hr₁, hA₁⟩ := (hf.analyticAt t₀).exists_ball_analyticOnNhd
  set ρ : ℝ := min r r₁ with hρ
  have hρ0 : 0 < ρ := lt_min hr hr₁
  have hsub : ball (γ t₀) ρ ⊆ ball (γ t₀) r := ball_subset_ball (min_le_left _ _)
  have hsub₁ : ball (γ t₀) ρ ⊆ ball (γ t₀) r₁ := ball_subset_ball (min_le_right _ _)
  have hcenter : γ t₀ ∈ ball (γ t₀) ρ := mem_ball_self hρ0
  have hγ : ∀ᶠ s in 𝓝 t₀, γ s ∈ ball (γ t₀) ρ :=
    γ.continuous.continuousAt.eventually_mem (ball_mem_nhds _ hρ0)
  have hconn : IsPreconnected (ball (γ t₀) ρ) := (convex_ball _ _).isPreconnected
  have hft : AnalyticOnNhd ℂ (f t₀) (ball (γ t₀) ρ) := hA₁.mono hsub₁
  filter_upwards [hγ, hf.locallyEq t₀] with s hsb hsf
  constructor
  · intro hs
    obtain ⟨F, hFA, hFf, hFB⟩ := hun _ (hsub hsb) _ hs
    have hEq : EqOn F (f t₀) (ball (γ t₀) ρ) :=
      (hFA.mono hsub).eqOn_of_preconnected_of_eventuallyEq hft hconn hsb (hFf.trans hsf)
    refine hcongr _ _ _ (hFB _ (hsub hcenter)) ?_
    filter_upwards [ball_mem_nhds _ hρ0] with v hv
    exact hEq hv
  · intro ht
    obtain ⟨F, hFA, hFf, hFB⟩ := hun _ (mem_ball_self hr) _ ht
    have hEq : EqOn F (f t₀) (ball (γ t₀) ρ) :=
      (hFA.mono hsub).eqOn_of_preconnected_of_eventuallyEq hft hconn hcenter hFf
    refine hcongr _ _ _ (hFB _ (hsub hsb)) ?_
    filter_upwards [isOpen_ball.mem_nhds hsb, hsf] with v hv hv'
    rw [hEq hv, hv']

/-- The identity theorem between an analytic and a meromorphic function, on a connected open set, in terms of punctured
germs. No radius depends on the poles of `M`. -/
lemma punctured_germ_transfer {G M : ℂ → ℂ} {U : Set ℂ} (hUc : IsConnected U)
    (hG : AnalyticOnNhd ℂ G U) (hM : MeromorphicOn M univ) {q₁ q₂ : ℂ} (h₁ : q₁ ∈ U) (h₂ : q₂ ∈ U)
    (h : G =ᶠ[𝓝[≠] q₁] M) : G =ᶠ[𝓝[≠] q₂] M := by
  have hF : MeromorphicOn (fun v => G v - M v) U := fun v hv =>
    (hG v hv).meromorphicAt.sub (hM v (mem_univ _))
  have htop₁ : meromorphicOrderAt (fun v => G v - M v) q₁ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with v hv
    rw [hv, sub_self]
  have htop₂ : meromorphicOrderAt (fun v => G v - M v) q₂ = ⊤ := by
    by_contra hne
    have hall := (hF.exists_meromorphicOrderAt_ne_top_iff_forall hUc).mp ⟨⟨q₂, h₂⟩, hne⟩
    exact hall ⟨q₁, h₁⟩ htop₁
  rw [meromorphicOrderAt_eq_top_iff] at htop₂
  filter_upwards [htop₂] with v hv
  exact sub_eq_zero.mp hv

/-- `famR` is locally constant along a continuation, on `Re v > 2`. -/
lemma famR_transfer {γ : C(unitInterval, ℂ)} {f : unitInterval → ℂ → ℂ} (hf : IsContinuationAlong γ f)
    {t₀ : unitInterval} (h2 : 2 < (γ t₀).re) :
    ∀ᶠ s in 𝓝 t₀, (famR (γ s) (f s) ↔ famR (γ t₀) (f t₀)) := by
  obtain ⟨r, hr, hA⟩ := (hf.analyticAt t₀).exists_ball_analyticOnNhd
  set ρ : ℝ := min r ((γ t₀).re - 2) with hρ
  have hρ0 : 0 < ρ := lt_min hr (by linarith)
  have hball2 : ∀ v ∈ ball (γ t₀) ρ, 2 < v.re := by
    intro v hv
    have h1 : ‖v - γ t₀‖ < ρ := by simpa [dist_eq_norm] using hv
    have h3 : |(v - γ t₀).re| ≤ ‖v - γ t₀‖ := Complex.abs_re_le_norm _
    have h4 : ρ ≤ (γ t₀).re - 2 := min_le_right _ _
    have h5 := (abs_le.mp h3).1
    simp only [sub_re] at h5
    linarith
  have hft : AnalyticOnNhd ℂ (f t₀) (ball (γ t₀) ρ) := hA.mono (ball_subset_ball (min_le_left _ _))
  have hDA : AnalyticOnNhd ℂ DS (ball (γ t₀) ρ) := fun v hv => DS_analyticAt (hball2 v hv)
  have hsub : AnalyticOnNhd ℂ (fun v => f t₀ v - DS v) (ball (γ t₀) ρ) := fun v hv => (hft v hv).sub (hDA v hv)
  set G : ℂ → ℂ := deriv (fun v => f t₀ v - DS v) with hGdef
  have hG : AnalyticOnNhd ℂ G (ball (γ t₀) ρ) := fun v hv => (hsub v hv).deriv
  have hconn : IsConnected (ball (γ t₀) ρ) := ⟨⟨_, mem_ball_self hρ0⟩, (convex_ball _ _).isPreconnected⟩
  have hγ : ∀ᶠ s in 𝓝 t₀, γ s ∈ ball (γ t₀) ρ :=
    γ.continuous.continuousAt.eventually_mem (ball_mem_nhds _ hρ0)
  filter_upwards [hγ, hf.locallyEq t₀] with s hsb hsf
  have key : deriv (fun v => f s v - DS v) =ᶠ[𝓝 (γ s)] G :=
    (hsf.sub (EventuallyEq.refl _ DS)).deriv
  constructor
  · rintro ⟨-, m, hm, M, hM, hMe, hd⟩
    refine ⟨h2, m, hm, M, hM, hMe, ?_⟩
    exact punctured_germ_transfer hconn hG hM hsb (mem_ball_self hρ0)
      ((key.symm.filter_mono nhdsWithin_le_nhds).trans hd)
  · rintro ⟨-, m, hm, M, hM, hMe, hd⟩
    refine ⟨hball2 _ hsb, m, hm, M, hM, hMe, ?_⟩
    exact (key.filter_mono nhdsWithin_le_nhds).trans
      (punctured_germ_transfer hconn hG hM (mem_ball_self hρ0) hsb hd)

/-- **`S` with excursions.** A germ reached from `Re v > 3` along a path in
`{Re v > 2B_∞} ∖ X` along which `S` continues, ending at `Re v < 3`, is `D^θ + m + C`. -/
theorem germFam_of_admissible_S (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {g : ℂ → ℂ} {q : ℂ}
    (hg : IsAdmissibleGermOn DS (halfPlane (2 * Binf) \ Pinch) (halfPlane 3) g q) (hq : q.re < 3) :
    ∃ C : ℂ, GermFam kS 3 C q g := by
  obtain ⟨γ, hγ, h0, rfl, f, hf, hf0, hg1⟩ := hg
  have hB := M1.half_le_Binf hZ1
  have h03 : (3 : ℝ) < (γ 0).re := h0
  let Inv : unitInterval → Prop := fun t => famD (γ t) (f t) ∨ famR (γ t) (f t)
  have hR : ∀ t, 2 < (γ t).re → (Inv t ↔ famR (γ t) (f t)) := fun t h2 =>
    ⟨fun h => h.elim (famR_of_famD hZ1 hZ2 hZ3 h2) id, Or.inr⟩
  have hD : ∀ t, (γ t).re < 3 → (Inv t ↔ famD (γ t) (f t)) := fun t h3 =>
    ⟨fun h => h.elim id (famD_of_famR hZ1 hZ2 hZ3 h3 (hf.analyticAt t)), Or.inl⟩
  have hloc : IsLocallyConstant Inv := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    by_cases h2 : 2 < (γ t₀).re
    · have hnear : ∀ᶠ s in 𝓝 t₀, 2 < (γ s).re :=
        (Complex.continuous_re.comp γ.continuous).continuousAt.eventually_const_lt h2
      filter_upwards [famR_transfer hf h2, hnear] with s hs hs2
      exact propext ((hR s hs2).trans (hs.trans (hR t₀ h2).symm))
    · have h3 : (γ t₀).re < 3 := by linarith
      have hmem : γ t₀ ∈ VInf 3 \ Pinch := by
        refine ⟨⟨mem_Vt3 ?_ h3, (hγ t₀).1⟩, (hγ t₀).2⟩
        have : 2 * Binf < (γ t₀).re := (hγ t₀).1
        linarith
      have hnear : ∀ᶠ s in 𝓝 t₀, (γ s).re < 3 :=
        (Complex.continuous_re.comp γ.continuous).continuousAt.eventually_lt_const h3
      filter_upwards [uniform_transfer (uniformFamily_famD hZ1 hZ2 hZ3)
        (fun _ _ _ h e => famD_congr h e) hf hmem, hnear] with s hs hs3
      exact propext ((hD s hs3).trans (hs.trans (hD t₀ h3).symm))
  have hstart : Inv 0 := by
    refine Or.inr ⟨by linarith, 0, zero_mem _, fun _ => 0, fun v _ => MeromorphicAt.const _ v, fun v _ => ?_, ?_⟩
    · have : deriv (0 : ℂ → ℂ) v = 0 := by simp
      exact this.symm
    · have e : (fun v => f 0 v - DS v) =ᶠ[𝓝 (γ 0)] fun _ => 0 := by
        filter_upwards [hf0] with v hv
        rw [hv, sub_self]
      have d := e.deriv
      have d2 : deriv (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
        funext v
        simp
      rw [d2] at d
      exact d.filter_mono nhdsWithin_le_nhds
  have hend : Inv 1 := by
    have : Inv 1 = Inv 0 := hloc.apply_eq_of_preconnectedSpace 1 0
    rw [this]
    exact hstart
  obtain ⟨C, hC⟩ := (hD 1 hq).mp hend
  exact ⟨C, germFam_congr hC hg1.symm⟩

end GoldbachBoundaries.HInf.Fill

