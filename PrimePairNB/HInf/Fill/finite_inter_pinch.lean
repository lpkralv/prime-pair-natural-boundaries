import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.re_le_two_of_mem_pinch

/-! Proofs of `finite_inter_pinch` and `isOpen_Om`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- A compact subset of `Re v > 2B_∞` meets `Σ + Σ` in a finite set.  -/
theorem finite_inter_pinch (hZ1 : Z1) {K : Set ℂ} (hK : IsCompact K) (hK2 : K ⊆ halfPlane (2 * Binf)) :
    (K ∩ Pinch).Finite := by
  refine hK.induction_on (p := fun S => (S ∩ Pinch).Finite) (by simp) ?_ ?_ ?_
  · intro S T hST hT
    exact hT.subset (inter_subset_inter_left _ hST)
  · intro S T hS hT
    rw [union_inter_distrib_right]
    exact hS.union hT
  · intro x hx
    obtain ⟨U, hU, hUf⟩ := GoldbachBoundaries.Paper2.M1.pinch_locallyFinite hZ1 (hK2 hx)
    exact ⟨K ∩ U, inter_mem_nhdsWithin K hU, hUf.subset (by
      intro z hz
      exact ⟨hz.1.2, hz.2⟩)⟩

theorem isClosed_rayW (κ : ℝ) (x : ℂ) : IsClosed (rayW κ x) := by
  have hsd : slantDir κ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [slantDir] at this
  have : rayW κ x = {z | hgt κ z = hgt κ x} ∩ {z | absc κ z ≤ absc κ x} := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have : (x - (t : ℂ) * slantDir κ) / slantDir κ = x / slantDir κ - t := by
        field_simp
      simp only [mem_inter_iff, mem_setOf_eq, hgt, absc, this, Complex.sub_im, Complex.ofReal_im,
        Complex.sub_re, Complex.ofReal_re]
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      simp only [mem_setOf_eq, hgt, absc] at h1 h2
      refine ⟨(x / slantDir κ).re - (z / slantDir κ).re, by linarith, ?_⟩
      have key : z / slantDir κ = x / slantDir κ - (((x / slantDir κ).re - (z / slantDir κ).re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using h1
      have e : z = (x / slantDir κ - (((x / slantDir κ).re - (z / slantDir κ).re : ℝ) : ℂ)) * slantDir κ := by
        rw [← key, div_mul_cancel₀ _ hsd]
      exact e.trans (by rw [sub_mul, div_mul_cancel₀ _ hsd])
  rw [this]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_le ?_ continuous_const)
  · unfold hgt; fun_prop
  · unfold absc; fun_prop

private theorem isOpen_Vt (top : EReal) : IsOpen (Vt top) := by
  have h1 : IsOpen {v : ℂ | 1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {v : ℂ | (v.re : EReal) < top} :=
    isOpen_lt (continuous_coe_real_ereal.comp Complex.continuous_re) continuous_const
  exact h1.inter h2

theorem isOpen_VInf (top : EReal) : IsOpen (VInf top) := by
  have h1 : IsOpen {v : ℂ | 2 * Binf < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have : VInf top = Vt top ∩ {v : ℂ | 2 * Binf < v.re} := rfl
  rw [this]
  exact (isOpen_Vt top).inter h1

/-- `Ω_θ` is open: on a compact set only finitely many cuts occur.  -/
theorem isOpen_Om (hZ1 : Z1) (κ : ℝ) (top : EReal) : IsOpen (Om κ top) := by
  rw [isOpen_iff_mem_nhds]
  intro v hv
  have hvV : v ∈ VInf top := hv.1
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp (isOpen_VInf top) v hvV
  -- the compact set `K` and the compact set `K'` where relevant cuts live
  set K : Set ℂ := closedBall v (r / 2) with hKdef
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKV : K ⊆ VInf top := fun z hz =>
    hrV (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  set K' : Set ℂ := (fun p : ℂ × ℝ => p.1 + (p.2 : ℂ) * slantDir κ) '' (K ×ˢ Icc (0 : ℝ) 1) with hK'def
  have hK'c : IsCompact K' := by
    refine (hKc.prod isCompact_Icc).image ?_
    fun_prop
  have hK'2 : K' ⊆ halfPlane (2 * Binf) := by
    rintro _ ⟨⟨z, t⟩, ⟨hz, ht0, ht1⟩, rfl⟩
    have := (hKV hz).2
    simp only [halfPlane, mem_setOf_eq, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, slantDir, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re,
      Complex.I_im, Complex.mul_im]
    simp
    linarith
  have hF := finite_inter_pinch hZ1 hK'c hK'2
  have hopen : IsOpen (ball v (r / 2) \ ⋃ x ∈ K' ∩ Pinch, rayW κ x) := by
    refine isOpen_ball.sdiff ?_
    exact hF.isClosed_biUnion (fun x _ => isClosed_rayW κ x)
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨mem_ball_self (by linarith), ?_⟩) ?_
  · intro hmem
    simp only [mem_iUnion] at hmem
    obtain ⟨x, hx, hvx⟩ := hmem
    exact hv.2 (mem_iUnion₂.mpr ⟨x, hx.2, hvx⟩)
  · rintro z ⟨hzb, hzr⟩
    have hzK : z ∈ K := ball_subset_closedBall hzb
    refine ⟨hKV hzK, ?_⟩
    simp only [mem_iUnion]
    rintro ⟨x, hx, t, ht, hzx⟩
    apply hzr
    simp only [mem_iUnion]
    refine ⟨x, ⟨?_, hx⟩, t, ht, hzx⟩
    have h2 := re_le_two_of_mem_pinch hx
    have hz1 := (hKV hzK).1.1
    have hre : z.re = x.re - t := by rw [hzx]; simp [slantDir]
    refine ⟨(z, t), ⟨hzK, ht, by linarith⟩, ?_⟩
    simp only
    rw [hzx]; ring

end GoldbachBoundaries.HInf.Fill

