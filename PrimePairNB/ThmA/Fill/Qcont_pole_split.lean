import PrimePairNB.ThmA.G15_Kernel

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.ThmA

/-- **Removing one pole of `Q`** (the pole-set lemma for `Q`(i),(ii); used in the local model and
the access lemma): `Q = Res_a(Q)/(z-a) + q` with `q` holomorphic on `{Re > 0} ∖ (Σ ∖ {a})`.

Sketch. `q := Qcont - sigmaRes a/(z-a)` off `a`, with the limit value at `a`. Holomorphic off `Σ`
(`lem_Sigma_i_ii_proof`); at `a`, `Qcont` has a simple pole with residue `sigmaRes a`
(`exists_hasResidue_Qcont_ne_zero`, `HasResidue.meromorphicOrderAt_eq_neg_one`), so the difference
has a removable singularity (`MeromorphicAt` order `≥ 0`, `AnalyticAt` after `update`). The domain
is open because `Σ` is locally finite in `Re > 0` (`lem_Sigma_iv_proof`). -/
theorem Qcont_pole_split (hRH : RiemannHypothesis) {a : ℂ} (ha : a ∈ PoleSetQ) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q (halfPlane 0 \ (PoleSetQ \ {a})) ∧
      ∀ z ∈ halfPlane 0, z ∉ PoleSetQ → Qcont z = sigmaRes a / (z - a) + q z := by
  classical
  obtain ⟨c, hc, hr⟩ := exists_hasResidue_Qcont_ne_zero hRH ha
  have hma := meromorphicAt_Qcont (re_pos_of_mem_poleSetQ ha)
  obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hma).mp
    (hr.meromorphicOrderAt_eq_neg_one hma hc)
  have hga : g a = sigmaRes a := by
    have hr' : HasResidue Qcont a (g a) := by
      refine (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hfg, self_mem_nhdsWithin] with z hz hza
      simp only [hz, zpow_neg_one, smul_eq_mul]
      field_simp [sub_ne_zero.mpr hza]
    exact (sigmaRes_eq hr').symm
  have hds : AnalyticAt ℂ (dslope g a) a := by
    obtain ⟨p, hp⟩ := hg
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  let q : ℂ → ℂ := Function.update (fun z => Qcont z - sigmaRes a / (z - a)) a (dslope g a a)
  have hqa : AnalyticAt ℂ q a := by
    apply hds.congr
    have hfg' := eventually_nhdsWithin_iff.mp hfg
    filter_upwards [hfg'] with z hz
    by_cases hza : z = a
    · subst z
      simp [q]
    · dsimp only [q]
      rw [Function.update_of_ne hza, dslope_of_ne g hza, slope_def_field, hga]
      rw [hz hza]
      simp only [zpow_neg_one, smul_eq_mul]
      ring
  refine ⟨q, ?_, ?_⟩
  · intro z hz
    by_cases hza : z = a
    · subst z; exact hqa
    · have hzS : z ∉ PoleSetQ := by
        intro h
        exact hz.2 ⟨h, hza⟩
      have hQ : AnalyticAt ℂ Qcont z := by
        simpa using analyticAt_Qcont_sub_sum hz.1 ∅
          (fun n _ hmu => regular_of_not_mem_poleSetQ hz.1 hzS hmu)
      have hdiff : AnalyticAt ℂ (fun z => Qcont z - sigmaRes a / (z - a)) z :=
        hQ.sub (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza))
      apply hdiff.congr
      filter_upwards [eventually_ne_nhds hza] with w hw
      simp [q, Function.update_of_ne hw]
  · intro z hz hzS
    have hza : z ≠ a := fun he => hzS (he ▸ ha)
    dsimp only [q]
    rw [Function.update_of_ne hza]
    ring

end GoldbachBoundaries.ThmA
