import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.half_le_Binf
import PrimePairNB.Paper2.M1.Fill.poleSetQ_re_bounds

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- A point on the admissible contour, and its reflected point, avoid the potential poles. -/
lemma E2_line_regular (hZ1 : Z1) {δ c : ℝ} (h : AdmC δ c) {s w : ℂ}
    (hs : s ∈ RegC δ c) (hw : w.re = c) :
    (0 < w.re ∧ w ∉ PoleSetQ) ∧ (0 < (s - w).re ∧ s - w ∉ PoleSetQ) := by
  have hB := half_le_Binf hZ1
  have hc := h.2.2.1
  have hδ := h.1
  have hs' := hs.1
  have hw0 : 0 < w.re := by rw [hw]; linarith
  have hsw0 : 0 < (s - w).re := by simp only [sub_re, hw]; linarith
  refine ⟨⟨hw0, ?_⟩, ⟨hsw0, ?_⟩⟩
  · intro hp
    have hf : w ∈ Fdelta δ := ⟨hp, by rw [hw]; linarith⟩
    exact h.2.2.2.2 w hf hw.symm
  · intro hp
    have hf : s - w ∈ Fdelta δ := ⟨hp, by simp only [sub_re, hw]; linarith⟩
    have he := hs.2 (s - w) hf
    simp only [sub_re, hw] at he
    exact he (by ring)

/-- Off the pinch set, subtraction by a potential pole avoids every potential pole. -/
lemma E2_sub_regular (hZ1 : Z1) {s a : ℂ} (hs : 2 * Binf < s.re)
    (ha : a ∈ PoleSetQ) (hP : s ∉ Pinch) : 0 < (s - a).re ∧ s - a ∉ PoleSetQ := by
  have hB := half_le_Binf hZ1
  have ha1 := (poleSetQ_re_bounds ha).2.1
  refine ⟨by simp only [sub_re]; linarith, ?_⟩
  intro hb
  exact hP ⟨a, ha, s - a, hb, by ring⟩

lemma E2_reg_re {δ c : ℝ} (h : AdmC δ c) {s : ℂ} (hs : s ∈ RegC δ c) :
    2 * Binf < s.re := by
  have hc := h.2.2.1
  have hδ := h.1
  have hs' := hs.1
  linarith

lemma E2_analytic_Qcont {z : ℂ} (hz : 0 < z.re) (hp : z ∉ PoleSetQ) :
    AnalyticAt ℂ Qcont z := by
  simpa using analyticAt_Qcont_sub_sum hz ∅
    (fun n _ hn => regular_of_not_mem_poleSetQ hz hp hn)

/-- Holomorphy of the Gamma kernel in its parameter on the right of its fixed argument. -/
lemma E2_analytic_KerS {s a : ℂ} (hsa : a.re < s.re) :
    AnalyticAt ℂ (fun z => KerS z a) s := by
  have hgd : DifferentiableOn ℂ Gamma (halfPlane 0) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_Gamma
    intro m hm
    have he := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at he
    change 0 < z.re at hz
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hg : AnalyticAt ℂ Gamma (s - a) :=
    hgd.analyticAt ((isOpen_halfPlane 0).mem_nhds (by
      show 0 < (s - a).re
      simp only [sub_re]
      linarith))
  have hi : AnalyticAt ℂ (fun z => (Gamma z)⁻¹) s :=
    differentiable_one_div_Gamma.analyticAt s
  have hcomp : AnalyticAt ℂ (fun z : ℂ => Gamma (z - a)) s :=
    AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z - a) (x := s) hg
      (analyticAt_id.sub analyticAt_const)
  simpa only [KerS, div_eq_mul_inv] using
    ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => Gamma a) s).fun_mul hcomp).fun_mul hi

/-- The indicator is constant near points of the contour region. -/
lemma E2_nu_eventuallyEq {δ c : ℝ} {s₀ a : ℂ} (hs₀ : s₀ ∈ RegC δ c)
    (ha : a ∈ Fdelta δ) : (fun s => nu c a s) =ᶠ[𝓝 s₀] (fun _ => nu c a s₀) := by
  classical
  have hn : s₀.re - a.re ≠ c := by
    intro he
    exact hs₀.2 a ha (by linarith)
  rcases lt_or_gt_of_ne hn with hl | hr
  · have he : ∀ᶠ s : ℂ in 𝓝 s₀, s.re - a.re < c :=
      (isOpen_lt (Complex.continuous_re.sub continuous_const) continuous_const).mem_nhds hl
    filter_upwards [he] with s hs
    simp [nu, iverson, hs, hl]
  · have he : ∀ᶠ s : ℂ in 𝓝 s₀, c < s.re - a.re :=
      (isOpen_lt continuous_const (Complex.continuous_re.sub continuous_const)).mem_nhds hr
    filter_upwards [he] with s hs
    simp [nu, iverson, not_lt.mpr hs.le, not_lt.mpr hr.le]

/-- Freeze the finitely many locally constant indicators. -/
lemma E2_Tc_eventuallyEq {δ c : ℝ} {s₀ : ℂ} (hF : (Fdelta δ).Finite)
    (hs₀ : s₀ ∈ RegC δ c) :
    Tc δ c =ᶠ[𝓝 s₀] (fun s => IcQ Qcont c s +
      ∑ a ∈ hF.toFinset, nu c a s₀ * Rcoef a * KerS s a * Qcont (s - a)) := by
  classical
  have hall : ∀ᶠ s in 𝓝 s₀, ∀ a ∈ Fdelta δ, nu c a s = nu c a s₀ := by
    exact (hF.eventually_all).mpr fun a ha => E2_nu_eventuallyEq hs₀ ha
  filter_upwards [hall] with s hs
  simp only [Tc, TcQ, finsum_mem_eq_finite_toFinset_sum _ hF]
  congr 1
  exact Finset.sum_congr rfl fun a ha => by rw [hs a (hF.mem_toFinset.mp ha)]

/-- Multiplication by an analytic coefficient preserves the lower bound for a simple pole. -/
lemma E2_order_mul {A B : ℂ → ℂ} {s : ℂ} (hA : AnalyticAt ℂ A s)
    (hB : MeromorphicAt B s) (ho : -1 ≤ meromorphicOrderAt B s) :
    -1 ≤ meromorphicOrderAt (fun z => A z * B z) s := by
  change -1 ≤ meromorphicOrderAt (A * B) s
  rw [meromorphicOrderAt_mul hA.meromorphicAt hB]
  simpa using add_le_add hA.meromorphicOrderAt_nonneg ho

lemma E2_sum_simple {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ℂ)
    (hf : ∀ i ∈ S, MeromorphicAt (f i) s)
    (ho : ∀ i ∈ S, -1 ≤ meromorphicOrderAt (f i) s) :
    MeromorphicAt (fun z => ∑ i ∈ S, f i z) s ∧
      -1 ≤ meromorphicOrderAt (fun z => ∑ i ∈ S, f i z) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨analyticAt_const.meromorphicAt,
      le_trans (show (-1 : WithTop ℤ) ≤ 0 from by decide) (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) s).meromorphicOrderAt_nonneg⟩
  | @insert a S ha ih =>
    have hS := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => ho i (Finset.mem_insert_of_mem hi))
    simp only [Finset.sum_insert ha]
    refine ⟨(hf a (Finset.mem_insert_self _ _)).fun_add hS.1, ?_⟩
    exact (le_min (ho a (Finset.mem_insert_self _ _)) hS.2).trans
      (meromorphicOrderAt_add (hf a (Finset.mem_insert_self _ _)) hS.1)

end GoldbachBoundaries.Paper2.M1
