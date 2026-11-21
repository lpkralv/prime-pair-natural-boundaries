import PrimePairNB.Paper2.M1.Kernel

/-!
# Fill: `verticalIntegral'_eq_add_sum_of_simplePoles`

Two steps.

1. **Rectangles** (`rectangleIntegral'_eq_sum_of_simplePoles_D`). For `T` above every `|Im p|`, `p ∈ S`, the rectangle
   `[σ, σ'] × [-T, T]` has integral `∑_{p ∈ S} A p`. Write `f = g + P` with `P(s) = ∑_{p ∈ S} A p/(s - p)`. The
   principal part integrates to `∑ A p` (PNT+'s `ResidueTheoremInRectangle`, term by term). The rest `g` is
   holomorphic on the rectangle off `S` and bounded near each `p ∈ S` (`f - A p/(s - p)` is bounded by hypothesis, the
   other principal parts are continuous at `p`); filling in its limits at the points of `S` (Riemann's removable
   singularity theorem, `differentiableOn_update_limUnder_of_bddAbove`) gives a function holomorphic on the whole
   rectangle that agrees with `g` on the border, so Cauchy's theorem gives `0`.
2. **Lines** (as the RH development's one-pole `verticalIntegral'_eq_add_of_simplePole`, `TIdentity/Basic.lean`, a port of
   PNT+'s `tendsto_truncated_vertical_shift_with_simple_pole`): the truncated left line integral equals the two
   horizontal sides plus the truncated right line integral minus `∑ A p`; let `T → ∞`.

Poles sharing a real part need no care: no line is ever placed between them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The rectangle integral of a finite sum of functions continuous on the border is the sum of the rectangle
integrals. -/
theorem rectangleIntegral'_finset_sum_D {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (h : ∀ i ∈ S, ContinuousOn (F i) (RectangleBorder z w)) :
    RectangleIntegral' (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, RectangleIntegral' (F i) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral]
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, ContinuousOn (F i) (RectangleBorder z w) :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hfun : (fun s => ∑ i ∈ insert a S, F i s) = F a + fun s => ∑ i ∈ S, F i s := by
      funext s; simp [Finset.sum_insert ha]
    have h1 : RectangleBorderIntegrable (F a) z w :=
      (h a (Finset.mem_insert_self a S)).rectangleBorder_integrable
    have h2 : RectangleBorderIntegrable (fun s => ∑ i ∈ S, F i s) z w :=
      (continuousOn_finsetSum S fun i hi => hS i hi).rectangleBorder_integrable
    rw [hfun, Finset.sum_insert ha, ← ih hS]
    unfold RectangleIntegral'
    rw [RectangleBorderIntegrable.add h1 h2, smul_add]

/-- **Rectangle residue theorem for finitely many simple poles**, in the form used for vertical strips. -/
theorem rectangleIntegral'_eq_sum_of_simplePoles_D {σ σ' T : ℝ} {f : ℂ → ℂ} (S : Finset ℂ) (A : ℂ → ℂ)
    (hσ : σ ≤ σ') (hS : ∀ p ∈ S, σ < p.re ∧ p.re < σ' ∧ |p.im| < T) (hT : 0 ≤ T)
    (hf : DifferentiableOn ℂ f (Icc σ σ' ×ℂ univ \ (S : Set ℂ)))
    (hpole : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f ((σ : ℂ) - I * T) ((σ' : ℂ) + I * T) = ∑ p ∈ S, A p := by
  classical
  set z : ℂ := (σ : ℂ) - I * T with hz
  set w : ℂ := (σ' : ℂ) + I * T with hw
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hwre : w.re = σ' := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hTT : -T ≤ T := by linarith
  have hzw_re : z.re ≤ w.re := by rw [hzre, hwre]; exact hσ
  have hzw_im : z.im ≤ w.im := by rw [hzim, hwim]; exact hTT
  have hRstrip : Rectangle z w ⊆ Icc σ σ' ×ℂ univ := by
    intro x hx
    rw [Rectangle, hzre, hzim, hwre, hwim, uIcc_of_le hσ, uIcc_of_le hTT] at hx
    exact mem_reProdIm.mpr ⟨(mem_reProdIm.mp hx).1, trivial⟩
  have hnotB : ∀ p ∈ S, p ∉ RectangleBorder z w := by
    intro p hp hpB
    obtain ⟨h1, h2, h3⟩ := hS p hp
    rw [abs_lt] at h3
    simp only [RectangleBorder, hzre, hzim, hwre, hwim, mem_union, mem_reProdIm,
      mem_singleton_iff] at hpB
    rcases hpB with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩ <;> linarith
  have hBsub : ∀ x ∈ RectangleBorder z w, x ∈ Icc σ σ' ×ℂ univ \ (S : Set ℂ) := fun x hx =>
    ⟨hRstrip (rectangleBorder_subset_rectangle z w hx), fun hxS => hnotB x hxS hx⟩
  have hpnhds : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    rw [abs_lt] at h3
    rw [rectangle_mem_nhds_iff, hzre, hzim, hwre, hwim, uIoo_of_lt (h1.trans h2),
      uIoo_of_lt (by linarith)]
    exact mem_reProdIm.mpr ⟨⟨h1, h2⟩, h3⟩
  -- the principal part
  set P : ℂ → ℂ := fun s => ∑ p ∈ S, A p / (s - p) with hPdef
  have hPcont : ∀ p ∈ S, ContinuousOn (fun s => A p / (s - p)) (RectangleBorder z w) := by
    intro p hp s hs
    have hsp : s - p ≠ 0 := sub_ne_zero.mpr fun h => hnotB p hp (h ▸ hs)
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hsp).continuousWithinAt
  have hPint : RectangleIntegral' P z w = ∑ p ∈ S, A p := by
    rw [hPdef, rectangleIntegral'_finset_sum_D S _ hPcont]
    exact Finset.sum_congr rfl fun p hp => ResidueTheoremInRectangle hzw_re hzw_im (hpnhds p hp)
  have hPdiff : DifferentiableOn ℂ P (S : Set ℂ)ᶜ := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    have : ∀ p ∈ S, DifferentiableAt ℂ (fun s => A p / (s - p)) s := fun p hp =>
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (sub_ne_zero.mpr fun h => hs (h ▸ hp))
    exact DifferentiableAt.fun_sum this
  -- the rest
  set g : ℂ → ℂ := fun s => f s - P s with hgdef
  have hgdiff : DifferentiableOn ℂ g (Icc σ σ' ×ℂ univ \ (S : Set ℂ)) :=
    hf.sub (hPdiff.mono fun s hs => hs.2)
  have hadd : RectangleIntegral' f z w = RectangleIntegral' g z w + RectangleIntegral' P z w := by
    have hgB : RectangleBorderIntegrable g z w := (hgdiff.continuousOn.mono hBsub).rectangleBorder_integrable
    have hPB : RectangleBorderIntegrable P z w :=
      (continuousOn_finsetSum S hPcont).rectangleBorder_integrable
    have hfe : g + P = f := by funext s; simp [hgdef]
    calc RectangleIntegral' f z w = RectangleIntegral' (g + P) z w := by rw [hfe]
      _ = _ := by unfold RectangleIntegral'; rw [RectangleBorderIntegrable.add hgB hPB, smul_add]
  -- fill in the removable singularities of `g`
  set gt : ℂ → ℂ := fun s => if s ∈ S then limUnder (𝓝[≠] s) g else g s with hgtdef
  have hgt : DifferentiableOn ℂ gt (Rectangle z w) := by
    intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨h1, h2, -⟩ := hS x hxS
      have hsplit : g = (f - fun s => A x / (s - x)) - fun s => ∑ q ∈ S.erase x, A q / (s - q) := by
        funext s
        simp only [hgdef, hPdef, Pi.sub_apply]
        rw [← Finset.add_sum_erase S _ hxS]
        ring
      have hcont : ContinuousAt (fun s => ∑ q ∈ S.erase x, A q / (s - q)) x :=
        tendsto_finsetSum (S.erase x) fun q hq =>
          (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
            (sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm) :
            ContinuousAt (fun s => A q / (s - q)) x)
      have hbig : g =O[𝓝[≠] x] (1 : ℂ → ℂ) := by
        rw [hsplit]
        exact (hpole x hxS).sub ((hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ)
      obtain ⟨U, hU, hUb⟩ := IsBigO_to_BddAbove hbig
      have hopen : IsOpen {s : ℂ | σ < s.re ∧ s.re < σ'} :=
        (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
      have hV : U ∩ {s : ℂ | σ < s.re ∧ s.re < σ'} ∩ ((S.erase x : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 x :=
        inter_mem (inter_mem hU (hopen.mem_nhds ⟨h1, h2⟩))
          ((S.erase x).finite_toSet.isClosed.compl_mem_nhds (by simp))
      obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
      have hball_notS : ∀ y ∈ ball x r, y ≠ x → y ∉ S := by
        intro y hy hyx hyS
        exact (hrV hy).2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyx, hyS⟩))
      have hd : DifferentiableOn ℂ g (ball x r \ {x}) := by
        refine hgdiff.mono fun y hy => ⟨?_, hball_notS y hy.1 hy.2⟩
        have := (hrV hy.1).1.2
        exact mem_reProdIm.mpr ⟨⟨this.1.le, this.2.le⟩, trivial⟩
      have hb : BddAbove (norm ∘ g '' (ball x r \ {x})) :=
        hUb.mono (image_mono (sdiff_subset_sdiff_left fun y hy => (hrV hy).1.1))
      have hupd := differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds x hr) hd hb
      have heq : gt =ᶠ[𝓝 x] Function.update g x (limUnder (𝓝[≠] x) g) := by
        filter_upwards [ball_mem_nhds x hr] with y hy
        by_cases hyx : y = x
        · rw [hyx]; simp [hgtdef, hxS]
        · simp [hgtdef, hyx, hball_notS y hy hyx]
      exact ((hupd.differentiableAt (ball_mem_nhds x hr)).congr_of_eventuallyEq
        heq).differentiableWithinAt
    · have hSc : (S : Set ℂ)ᶜ ∈ 𝓝 x := S.finite_toSet.isClosed.compl_mem_nhds hxS
      have h1 : DifferentiableWithinAt ℂ g (Rectangle z w) x := by
        refine (hgdiff x ⟨hRstrip hx, hxS⟩).mono_of_mem_nhdsWithin ?_
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨_, hSc, fun y hy => ⟨hRstrip hy.2, hy.1⟩⟩
      refine h1.congr_of_eventuallyEq ?_ (by simp [hgtdef, hxS])
      filter_upwards [nhdsWithin_le_nhds hSc] with y hy
      have hy' : y ∉ S := hy
      simp [hgtdef, hy']
  have hg0 : RectangleIntegral' g z w = 0 := by
    have hcongr : RectangleIntegral g z w = RectangleIntegral gt z w := by
      apply RectangleIntegral_congr
      intro y hy
      have hyS : y ∉ S := fun h => hnotB y h hy
      simp [hgtdef, hyS]
    unfold RectangleIntegral'
    rw [hcongr, HolomorphicOn.vanishesOnRectangle hgt subset_rfl, smul_zero]
  rw [hadd, hg0, hPint, zero_add]

/-- **Moving a vertical line past finitely many simple poles.** If `σ ≤ σ'` (needed when `S = ∅`), `f` is
holomorphic on the closed strip `σ ≤ Re ≤ σ'` except at the finitely many points of `S` (all strictly inside),
`f - A p/(s - p)` is bounded near each `p ∈ S` (`A p = 0` allowed: a removable point), the horizontal integrals tend
to `0` as `Im → ±∞`, and `f` is integrable on both lines, then
`(2πi)⁻¹ ∫_{(σ')} f = ∑_{p ∈ S} A p + (2πi)⁻¹ ∫_{(σ)} f`. (Rectangle version: subtract the principal parts, which have
rectangle integral `A p` each, and apply Cauchy's theorem; or induct on `S` with the RH development's one-pole lemma after
splitting the strip at lines that avoid `S`, which needs care when two poles share a real part.) -/
theorem verticalIntegral'_eq_add_sum_of_simplePoles {σ σ' : ℝ} {f : ℂ → ℂ} (S : Finset ℂ)
    (A : ℂ → ℂ)
    (hσ : σ ≤ σ') (hS : ∀ p ∈ S, σ < p.re ∧ p.re < σ')
    (hf : DifferentiableOn ℂ f (Icc σ σ' ×ℂ univ \ (S : Set ℂ)))
    (hpole : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hbot : Tendsto (fun y : ℝ => ∫ x in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun y : ℝ => ∫ x in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable fun y : ℝ => f (σ + y * I))
    (hright : Integrable fun y : ℝ => f (σ' + y * I)) :
    VerticalIntegral' f σ' = ∑ p ∈ S, A p + VerticalIntegral' f σ := by
  set B : ℂ := ∑ p ∈ S, A p with hBdef
  set T₀ : ℝ := ∑ p ∈ S, |p.im| with hT₀
  have hT₀nn : 0 ≤ T₀ := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) = B := by
    filter_upwards [eventually_gt_atTop T₀] with T hT
    refine rectangleIntegral'_eq_sum_of_simplePoles_D S A hσ
      (fun p hp => ⟨(hS p hp).1, (hS p hp).2, ?_⟩) (by linarith) hf hpole
    exact lt_of_le_of_lt (Finset.single_le_sum (f := fun p : ℂ => |p.im|)
      (fun p _ => abs_nonneg _) hp) hT
  -- From here on, the RH development's `verticalIntegral'_eq_add_of_simplePole` (`TIdentity/Basic.lean`) with `A := B`.
  have hleft_eq : ∀ᶠ T : ℝ in atTop,
      (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ (-T) T =
        (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' (-T) -
          (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' T +
          (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ' (-T) T - B := by
    filter_upwards [hrect] with T hT
    have hT' : (1 / (2 * Real.pi * I) : ℂ) •
        RectangleIntegral f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) = B := by
      simpa [RectangleIntegral'] using hT
    calc
      (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ (-T) T
          = (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' (-T) -
              (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' T +
              (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ' (-T) T -
              (1 / (2 * Real.pi * I) : ℂ) •
                RectangleIntegral f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) := by
            simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
              ofReal_im, mul_zero, sub_self, sub_zero, sub_im, mul_im, one_mul, zero_add,
              zero_sub, add_re, add_zero, add_im]
            module
      _ = _ := by rw [hT']
  have hbotT : Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' (-T))
      atTop (𝓝 0) := by
    simpa [HIntegral] using
      (hbot.comp tendsto_neg_atTop_atBot).const_smul (1 / (2 * Real.pi * I) : ℂ)
  have htopT : Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' T)
      atTop (𝓝 0) := by
    simpa [HIntegral] using htop.const_smul (1 / (2 * Real.pi * I) : ℂ)
  have hvert : ∀ τ : ℝ, Integrable (fun y : ℝ => f (τ + y * I)) →
      Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • VIntegral f τ (-T) T)
        atTop (𝓝 (VerticalIntegral' f τ)) := fun τ hτ => by
    simpa [VIntegral, VerticalIntegral', VerticalIntegral] using
      ((intervalIntegral_tendsto_integral hτ tendsto_neg_atTop_atBot tendsto_id).const_smul
        I).const_smul (1 / (2 * Real.pi * I) : ℂ)
  have hsum := ((hbotT.sub htopT).add (hvert σ' hright)).sub
    (tendsto_const_nhds (x := B) (f := atTop))
  have hlim : Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ (-T) T)
      atTop (𝓝 (VerticalIntegral' f σ' - B)) := by
    refine (hsum.congr' (hleft_eq.mono fun _ hT => hT.symm)).trans ?_
    simp
  have := tendsto_nhds_unique (hvert σ hleft) hlim
  rw [this]
  ring

end GoldbachBoundaries.Paper2.M1
