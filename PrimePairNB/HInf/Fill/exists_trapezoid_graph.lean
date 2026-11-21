import PrimePairNB.HInf.Defs
import PrimePairNB.HInf.Fill.graphInt_line
import PrimePairNB.HInf.Fill.differentiableOn_graphInt
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace GoldbachBoundaries.HInf.Fill

/-- **Trapezoids.** Finitely many disjoint bands of height, each with a plateau value: a graph that is the line `c + κh`
off the bands, the prescribed constant on each plateau, and on each ramp a convex combination of the two. This is the
"tents" (`r i = 0`) and "flat tops" (`r i > 0`) in one lemma. -/
theorem exists_trapezoid_graph (κ c : ℝ) {ι : Type*} (S : Finset ι) (h₀ r τ : ι → ℝ) {w : ℝ} (hw : 0 < w)
    (hr : ∀ i ∈ S, 0 ≤ r i)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r i + r j + 2 * w < |h₀ i - h₀ j|) :
    ∃ Γ : SlantGraph κ, Γ.c = c ∧
      (∀ h : ℝ, (∀ i ∈ S, r i + w ≤ |h - h₀ i|) → Γ.ξ h = c + κ * h) ∧
      (∀ i ∈ S, ∀ h : ℝ, |h - h₀ i| ≤ r i → Γ.ξ h = τ i) ∧
      (∀ i ∈ S, ∀ h : ℝ, |h - h₀ i| < r i + w → ∃ l ∈ Icc (0 : ℝ) 1,
        Γ.ξ h = (1 - l) * (c + κ * h) + l * τ i) := by
  classical
  let b (i : ι) : ContDiffBump (h₀ i) :=
    { rIn := max (r i) 0 + w / 2
      rOut := max (r i) 0 + w
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let d (i : ι) (h : ℝ) : ℝ := b i h * (τ i - (c + κ * h))
  have hd (i : ι) : ContDiff ℝ 1 (d i) := by
    exact (b i).contDiff.mul (contDiff_const.sub (contDiff_const.add
      (contDiff_const.mul contDiff_id)))
  have hdc (i : ι) : HasCompactSupport (d i) :=
    (b i).hasCompactSupport.mul_right
  obtain ⟨B, hB⟩ : ∃ B : ι → ℝ, ∀ i h, |deriv (d i) h| ≤ B i := by
    have hi (i : ι) : ∃ C : ℝ, ∀ h, |deriv (d i) h| ≤ C := by
      simpa only [Real.norm_eq_abs] using
        (hd i).continuous_deriv_one.bounded_above_of_compact_support (hdc i).deriv
    exact Classical.skolem.mp hi
  let D (h : ℝ) := ∑ i ∈ S, d i h
  have hD : Differentiable ℝ D :=
    Differentiable.fun_sum (fun i _ => (hd i).differentiable (by norm_num))
  have hder (h : ℝ) : deriv D h = ∑ i ∈ S, deriv (d i) h := by
    dsimp only [D]
    exact deriv_fun_sum (u := S) (fun i _ => ((hd i).differentiable (by norm_num)) h)
  let T : ℝ := 1 + ∑ i ∈ S, (|h₀ i| + r i + w)
  have hzero (i : ι) (hi : i ∈ S) (h : ℝ) (hh : r i + w ≤ |h - h₀ i|) :
      b i h = 0 := by
    apply (b i).zero_of_le_dist
    simpa [b, max_eq_left (hr i hi), Real.dist_eq] using hh
  have htail (h : ℝ) (hh : T ≤ |h|) : D h = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hm : |h₀ i| + r i + w ≤ ∑ j ∈ S, (|h₀ j| + r j + w) :=
      Finset.single_le_sum (f := fun j => |h₀ j| + r j + w)
        (fun j hj => by have := hr j hj; positivity) hi
    have ht := abs_sub_abs_le_abs_sub h (h₀ i)
    have hz : r i + w ≤ |h - h₀ i| := by dsimp [T] at hh; linarith
    simp [d, hzero i hi h hz]
  let Γ : SlantGraph κ :=
    { ξ := fun h => c + κ * h + D h
      cont := by exact (by fun_prop : Continuous (fun h : ℝ => c + κ * h)).add hD.continuous
      c := c
      T := T
      tail := fun h hh => by simp [htail h hh]
      brk := ∅
      diff := fun h _ => by fun_prop
      lip := by
        refine ⟨|κ| + ∑ i ∈ S, B i, fun h _ => ?_⟩
        have he : deriv (fun h => c + κ * h + D h) h = κ + deriv D h := by
          rw [deriv_fun_add (by fun_prop) (hD h)]
          simp
        rw [he, hder]
        apply (abs_add_le _ _).trans
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => hB i h) }
  have hsingle (i : ι) (hi : i ∈ S) (h : ℝ) (hh : |h - h₀ i| < r i + w) :
      D h = d i h := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hsep := hdisj i hi j hj (Ne.symm hji)
      have ht : |h₀ i - h₀ j| ≤ |h - h₀ i| + |h - h₀ j| := by
        simpa [abs_sub_comm, add_comm] using abs_sub_le (h₀ i) h (h₀ j)
      have hz : r j + w ≤ |h - h₀ j| := by linarith
      simp [d, hzero j hj h hz]
    · exact fun hn => (hn hi).elim
  refine ⟨Γ, rfl, ?_, ?_, ?_⟩
  · intro h hh
    have : D h = 0 := Finset.sum_eq_zero fun i hi => by simp [d, hzero i hi h (hh i hi)]
    change c + κ * h + D h = c + κ * h
    rw [this, add_zero]
  · intro i hi h hh
    have hb : b i h = 1 := by
      apply (b i).one_of_mem_closedBall
      rw [mem_closedBall, Real.dist_eq]
      dsimp [b]
      have := hr i hi
      rw [max_eq_left this]
      linarith
    change c + κ * h + D h = τ i
    rw [hsingle i hi h (by linarith)]
    dsimp [d]
    rw [hb]
    ring
  · intro i hi h hh
    refine ⟨b i h, ⟨(b i).nonneg, (b i).le_one⟩, ?_⟩
    change c + κ * h + D h = _
    rw [hsingle i hi h hh]
    dsimp [d]
    ring

end GoldbachBoundaries.HInf.Fill

