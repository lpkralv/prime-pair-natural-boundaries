import PrimePairNB.HInf.Defs

/-! Proof of `isOpen_Uth`. The helpers `rayW_eq`, `isClosed_rayW_Uth`, `exists_finite_cuts` are also used by
`Fill/Pth_local.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- The ray west from `a` is the closed half-line `{Im z - Im a = κ (Re z - Re a), Re z ≤ Re a}`. -/
lemma rayW_eq (κ : ℝ) (a : ℂ) :
    rayW κ a = {z : ℂ | z.im - a.im = κ * (z.re - a.re) ∧ z.re ≤ a.re} := by
  ext z
  simp only [rayW, mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [slantDir, sub_re, sub_im, mul_re, mul_im, add_re, add_im, one_re, one_im, ofReal_re, ofReal_im,
      I_re, I_im]
    constructor
    · ring
    · nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨a.re - z.re, by linarith, ?_⟩
    apply Complex.ext
    · simp [slantDir]
    · simp [slantDir]
      linarith

lemma isClosed_rayW_Uth (κ : ℝ) (a : ℂ) : IsClosed (rayW κ a) := by
  rw [rayW_eq]
  exact (isClosed_eq (continuous_im.sub continuous_const)
    (continuous_const.mul (continuous_re.sub continuous_const))).inter
    (isClosed_le continuous_re continuous_const)

/-- Near `z₀`, only finitely many rays matter: any ray from `Σ` meeting `ball z₀ (Re z₀ / 2)` starts in a finite set. -/
lemma exists_finite_cuts (κ : ℝ) {z₀ : ℂ} (hx₀ : 0 < z₀.re) :
    ∃ S : Set ℂ, S.Finite ∧ S ⊆ PoleSetQ ∧
      ∀ w ∈ ball z₀ (z₀.re / 2), ∀ a ∈ PoleSetQ, w ∈ rayW κ a → a ∈ S := by
  set r : ℝ := z₀.re / 2 with hr
  set R : ℝ := 1 + |z₀.im| + z₀.re + |κ| with hR
  set K : Set ℂ := closedBall 0 R ∩ {w | r ≤ w.re} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_re)
  have hK0 : K ⊆ halfPlane 0 := fun w hw => by
    show 0 < w.re
    have := hw.2
    simp only [mem_ofPred_eq] at this
    linarith
  refine ⟨K ∩ PoleSetQ, M6.finite_inter_poleSetQ_A hKc hK0, inter_subset_right, ?_⟩
  intro w hw a ha hwa
  rw [rayW_eq] at hwa
  obtain ⟨him, hre⟩ := hwa
  have hwz : ‖w - z₀‖ < r := by rwa [mem_ball, dist_eq_norm] at hw
  have h1 : |w.re - z₀.re| < r := lt_of_le_of_lt (by
    simpa using Complex.abs_re_le_norm (w - z₀)) hwz
  have h2 : |w.im - z₀.im| < r := lt_of_le_of_lt (by
    simpa using Complex.abs_im_le_norm (w - z₀)) hwz
  have hb := M1.poleSetQ_re_bounds ha
  rw [abs_lt] at h1 h2
  refine ⟨⟨?_, ?_⟩, ha⟩
  · rw [mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im a).trans ?_
    rw [abs_of_pos hb.1]
    have hd : |w.re - a.re| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hb.2.1]
    have hk : |κ * (w.re - a.re)| ≤ |κ| := by
      rw [abs_mul]
      nlinarith [abs_nonneg κ]
    have hw' : |w.im| ≤ |z₀.im| + r := by
      rw [abs_le]
      constructor
      · have := neg_abs_le z₀.im; linarith
      · have := le_abs_self z₀.im; linarith
    have ha' : |a.im| ≤ |w.im| + |κ| := by
      have e : a.im = w.im - κ * (w.re - a.re) := by linarith
      rw [e, abs_le]
      constructor
      · linarith [neg_abs_le w.im, le_abs_self (κ * (w.re - a.re))]
      · linarith [le_abs_self w.im, neg_abs_le (κ * (w.re - a.re))]
    linarith [hb.2.1]
  · simp only [mem_ofPred_eq]
    linarith

/-- `U_θ` is open (`Paper2.M1.poleSetQ_locallyFinite`; unconditional). -/
theorem isOpen_Uth (κ : ℝ) : IsOpen (Uth κ) := by
  rw [isOpen_iff_mem_nhds]
  intro z₀ hz₀
  have hx₀ : 0 < z₀.re := hz₀.1
  obtain ⟨S, hSf, hSP, key⟩ := exists_finite_cuts κ hx₀
  set C : Set ℂ := ⋃ a ∈ S, rayW κ a with hC
  have hCc : IsClosed C := hSf.isClosed_biUnion fun a _ => isClosed_rayW_Uth κ a
  have hz₀C : z₀ ∉ C := by
    intro h
    obtain ⟨a, haS, hz⟩ := mem_iUnion₂.mp h
    exact hz₀.2 (mem_iUnion₂.mpr ⟨a, hSP haS, hz⟩)
  have hsub : ball z₀ (z₀.re / 2) ∩ halfPlane 0 ∩ Cᶜ ⊆ Uth κ := by
    rintro w ⟨⟨hwb, hw0⟩, hwC⟩
    refine ⟨hw0, fun h => hwC ?_⟩
    obtain ⟨a, ha, hwa⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨a, key w hwb a ha hwa, hwa⟩
  refine mem_of_superset ?_ hsub
  refine IsOpen.mem_nhds ?_ ⟨⟨mem_ball_self (by positivity), hx₀⟩, hz₀C⟩
  exact (isOpen_ball.inter (isOpen_lt continuous_const continuous_re)).inter hCc.isOpen_compl

end GoldbachBoundaries.HInf.Fill
