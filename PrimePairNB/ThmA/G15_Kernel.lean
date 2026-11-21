import PrimePairNB.ThmA.G14_Geometry

/-!
# Parametric integrals, the kernel, `X_α`, the branch `P_v`, and `P` along `s - 𝒮`

Contents: the kernel lemma, the branch `P_v` (`E`, `P_v`), the continuation of `P` along a
segment (defined by an explicit integral of `Q`, `Defs.lean`), and the values of `X'_α(α)`.

The lemmas `differentiableOn_intervalIntegral_of_continuousOn`, `J_spec`, `X_deriv_spec`,
`exists_Eaux`, `Pv_spec`, `Qcont_pole_split`, `PsegA_split`, `analyticAt_N1A` are proved in
`Fill/<name>.lean`; `X_differentiableOn`, `Mon_analyticOn` and `MSpan_analyticOn` are in
`Fill/J_spec.lean` and `Eaux_spec` is in `Fill/exists_Eaux.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-! ### Real proofs -/

theorem X_self (α : ℂ) : X α α = 0 := by
  unfold X
  split_ifs with h
  · subst h; simp only [J, segInt]; norm_num
  · simp [J, segInt]

theorem Mon_mem_MSpan {α : ℂ} (hα : α ∈ catalogue) : Mon α ∈ MSpan :=
  AddSubgroup.subset_closure ⟨α, hα, rfl⟩

/-- `N₁` depends on the anchor function only through its value at `s - w_b`. -/
theorem N1A_congr {κ b : ℝ} {A A' : ℂ → ℂ} {s : ℂ} (h : A (s - wb κ b) = A' (s - wb κ b)) :
    N1A κ b A s = N1A κ b A' s := by
  simp only [N1A, PsegA, h]

end GoldbachBoundaries.ThmA
