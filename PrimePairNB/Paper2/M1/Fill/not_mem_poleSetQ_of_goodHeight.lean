import PrimePairNB.Paper2.M1.Kernel
import PrimePairNB.Paper2.M1.Fill.half_le_Binf

/-! `not_mem_poleSetQ_of_goodHeight`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- No point of `Σ_Q` lies in the region of Paper, Lemma 2.2 (Z1): such a point would be a zero with `|γ| ≥ H - 1`
and `β ≥ B_∞ + 2δ` (excluded by the good height), or `1`, `1/k` (real), or `ρ/n` with `n ≥ 2` (real part `< 1/2 ≤ B_∞`).
Uses: `half_le_Binf`. -/
theorem not_mem_poleSetQ_of_goodHeight (hZ1 : Z1) {δ H : ℝ} (hδ : 0 < δ) (hH : GoodHeight δ H) {w : ℂ}
    (hw : Binf + 2 * δ ≤ w.re) (hwH : H ≤ |w.im|) : w ∉ PoleSetQ := by
  have hB := half_le_Binf hZ1
  have h2 : 2 ≤ |w.im| := hH.1.trans hwH
  rintro ((h1 | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩)
  · rw [mem_singleton_iff.mp h1] at h2
    norm_num at h2
  · have him : (1 / (k : ℂ)).im = 0 := by
      rw [one_div, Complex.inv_im]
      simp
    rw [him] at h2
    norm_num at h2
  · rcases eq_or_lt_of_le hn with h | h
    · subst h
      simp only [Nat.cast_one, div_one] at hw hwH
      have := hH.2 ρ hρ (by linarith)
      linarith
    · rw [Complex.div_natCast_re] at hw
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have : ρ.re / n ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hρ.2.2]
      linarith

end GoldbachBoundaries.Paper2.M1
