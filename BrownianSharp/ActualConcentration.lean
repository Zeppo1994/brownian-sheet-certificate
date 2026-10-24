import BrownianSharp.Ehrhard
import BrownianSharp.GaussianGridStatistics
import BrownianSharp.GaussianMomentRoot
import BrownianSharp.NativeMatrix
import BrownianSharp.GridConfinement
import BrownianSharp.Confinement

/-!
# Actual-statistic Gaussian lower tails

The first theorem packages the complete elementary/measure-theoretic PV
argument for an actual observable. Its only analytic input is concavity of the
Gaussian-quantile transform of its strict CDF. The later specialization
derives that input for the normalized finite-grid moment from the same
set-level Ehrhard theorem used for its p-th root.
-/

open MeasureTheory ProbabilityTheory
open BrownianSharp.Concentration

namespace BrownianSharp

/-- A positive-measure level set is excluded by the atomlessness premise. -/
theorem measureReal_strictLevel_eq_weakLevel_of_null
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X) (hAtom : ∀ r, μ {ω | X ω = r} = 0)
    (a : ℝ) : μ.real {ω | X ω < a} = μ.real {ω | X ω ≤ a} := by
  let L : Set Ω := {ω | X ω < a}
  let Z : Set Ω := {ω | X ω = a}
  let C : Set Ω := {ω | X ω ≤ a}
  have hdisj : Disjoint L Z := by
    rw [Set.disjoint_left]
    intro ω hωL hωZ
    simp only [L, Z, Set.mem_setOf_eq] at hωL hωZ
    linarith
  have hunion : L ∪ Z = C := by
    ext ω
    simp only [L, Z, C, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hlt : X ω < a
      · exact Or.inl hlt
      · right
        linarith
  have hZmeas : MeasurableSet Z := by
    change MeasurableSet (X ⁻¹' ({a} : Set ℝ))
    exact hXmeas (measurableSet_singleton a)
  have hsum := measureReal_union hdisj hZmeas
    (measure_ne_top μ _) (measure_ne_top μ _)
  have hzero : μ.real Z = 0 := by
    change (μ Z).toReal = 0
    rw [show Z = {ω | X ω = a} by rfl, hAtom a]
    simp
  calc
    μ.real L = μ.real L + μ.real Z := by rw [hzero, add_zero]
    _ = μ.real (L ∪ Z) := hsum.symm
    _ = μ.real C := by rw [hunion]

/-- The generic mean-centred PV kernel, with all CDF quantile and median data
derived from the displayed actual law. The remaining hypotheses are exactly
the transformed-CDF concavity and endpoint/range facts. -/
theorem mean_lower_tail_of_transformed_cdf_concave_actual
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (hXmeas : Measurable X)
    (hXnonneg : ∀ ω, 0 ≤ X ω) (hmean : 0 < μ[X])
    (hAtom : ∀ r, μ {ω | X ω = r} = 0)
    (F G : ℝ → ℝ)
    (hF : ∀ s, F s = μ.real {ω | X ω < s})
    (hGconcave : ConcaveOn ℝ (Set.Ioi 0) G)
    (hGrep : ∀ s, 0 < s → F s = standardGaussianCDF (G s))
    (t : ℝ) (ht : 1 < t) :
    μ.real {ω | X ω - μ[X] < -t *
      Real.sqrt (ProbabilityTheory.variance X μ)} ≤
        Real.exp (-Real.pi * (t - 1) ^ 2 / 1024) := by
  have hvar : 0 < ProbabilityTheory.variance X μ :=
    variance_pos_of_positive_mean_and_null_mean_level μ X hX hXmeas hmean
      (fun r _ => hAtom r)
  have hσ : 0 < Real.sqrt (ProbabilityTheory.variance X μ) := Real.sqrt_pos.mpr hvar
  obtain ⟨median, hmedianLt, hmedianGt⟩ :=
    exists_two_sided_median_of_null_levels μ X hXmeas hAtom
  have hXnonnegAE : 0 ≤ᵐ[μ] X := ae_of_all _ hXnonneg
  have hmedianPos : 0 < median := by
    by_contra hnot
    have hmedle : median ≤ 0 := le_of_not_gt hnot
    have hEmpty : {ω | X ω < median} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      linarith [hXnonneg ω]
    rw [hEmpty] at hmedianLt
    norm_num at hmedianLt
  have hFmedian : F median = 1 / 2 := by
    rw [hF]
    exact hmedianLt
  have hGmedian : G median = 0 := by
    apply standardGaussianCDF_strictMono.injective
    rw [← hGrep median hmedianPos, hFmedian, standardGaussianCDF_zero]
  have hmedianLower : (1 / 2 : ℝ) ≤ μ.real {ω | X ω ≤ median} := by
    calc
      (1 / 2 : ℝ) = μ.real {ω | X ω < median} := hmedianLt.symm
      _ ≤ μ.real {ω | X ω ≤ median} :=
        MeasureTheory.measureReal_mono (by
          intro ω hω
          change X ω < median at hω
          exact hω.le)
  have hmedianUpper : (1 / 2 : ℝ) ≤ μ.real {ω | median ≤ X ω} := by
    calc
      (1 / 2 : ℝ) = μ.real {ω | median < X ω} := hmedianGt.symm
      _ ≤ μ.real {ω | median ≤ X ω} :=
        MeasureTheory.measureReal_mono (by
          intro ω hω
          change median < X ω at hω
          exact hω.le)
  have hEpos : 0 < ∫ ω, max (X ω - median) 0 ∂μ :=
    pospart_integral_pos_of_positive_upper_median μ X hX median
      (by
        have hnotzero : μ {ω | median < X ω} ≠ 0 := by
          intro hz
          have hreal : μ.real {ω | median < X ω} = 0 := by
            simp [Measure.real_def, hz]
          rw [hreal] at hmedianGt
          norm_num at hmedianGt
        exact ENNReal.toReal_pos hnotzero (measure_ne_top μ _))
  let δ : ℝ := 4 * (∫ ω, max (X ω - median) 0 ∂μ)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact mul_pos (by norm_num) hEpos
  have hδeq : δ = 4 * (∫ ω, max (X ω - median) 0 ∂μ) := rfl
  have hmy : median < median + δ := by linarith
  have hweakInterval := measure_median_interval_mass_ge_quarter_of_pospart
    μ X hX hXmeas median hmedianGt hEpos
  have hposY : 0 < median + δ := by linarith
  have hatomY : μ.real {ω | X ω = median + δ} = 0 := by
    have hzero := hAtom (median + δ)
    simp [Measure.real_def, hzero]
  have hopenInterval := measure_median_open_interval_mass_ge_quarter
    μ X hXmeas median (median + δ) hmy hweakInterval hatomY
  have hrep : ∀ s, 0 < s → 0 < F s →
      F s = (ProbabilityTheory.gaussianReal 0 1).real {z | z < G s} := by
    intro s hs hFs
    rw [hGrep s hs]
    rfl
  have hrepY : F (median + δ) = standardGaussianCDF (G (median + δ)) :=
    hGrep (median + δ) hposY
  have hquantile : Real.sqrt Real.pi / 4 ≤ G (median + δ) :=
    transformed_cdf_right_quantile_of_interval_mass μ X hXmeas F G
      median (median + δ) (Real.sqrt Real.pi / 4) hmy hF hrepY hmedianLt
      hopenInterval standardGaussianCDF_strictMono
      standardGaussianCDF_sqrt_pi_div_four_lt_three_quarters
  exact measure_mean_lower_tail_le_of_transformed_cdf_concave_of_pv_scale
    μ X hX hXmeas hXnonneg F G median δ t hF hrep hGconcave hGmedian
    hmedianLower hmedianUpper hquantile hδ hδeq hσ ht

/-- The set-level Ehrhard theorem supplies transformed-CDF concavity for any
measurable convex observable whose strict levels are atomless. This generic
bridge is used for both the finite-grid root and its normalized p-th moment. -/
theorem transformed_cdf_concave_of_set_ehrhard
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (X : E → ℝ) (hXconvex : ConvexOn ℝ Set.univ X)
    (hXmeas : Measurable X) (hAtom : ∀ r, μ {x | X x = r} = 0)
    (F G : ℝ → ℝ)
    (hF : ∀ s, F s = μ.real {x | X x < s})
    (hFRange : ∀ s, 0 < s → 0 < F s ∧ F s < 1)
    (hEhrhard : GaussianEhrhard E μ)
    (hG : ∀ s, G s = cdfGaussianQuantile F s) :
    ConcaveOn ℝ (Set.Ioi 0) G := by
  classical
  have hrep : ∀ s, 0 < s → F s = standardGaussianCDF (G s) := by
    intro s hs
    rw [hG]
    exact cdfGaussianQuantile_representation F (hFRange s hs).1 (hFRange s hs).2
  have hMass : ∀ s ∈ Set.Ioi (0 : ℝ), ∀ u ∈ Set.Ioi (0 : ℝ),
      ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
        standardGaussianCDF (a • G s + b • G u) ≤ F (a • s + b • u) := by
    intro s hs u hu a b ha hb hab
    let Ks : Set E := {x | X x ≤ s}
    let Ku : Set E := {x | X x ≤ u}
    have hKsconv : Convex ℝ Ks := by
      simpa [Ks] using hXconvex.convex_le s
    have hKuconv : Convex ℝ Ku := by
      simpa [Ku] using hXconvex.convex_le u
    have hmassS : μ.real Ks = F s := by
      calc
        μ.real Ks = μ.real {x | X x < s} :=
          (measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom s).symm
        _ = F s := (hF s).symm
    have hmassU : μ.real Ku = F u := by
      calc
        μ.real Ku = μ.real {x | X x < u} :=
          (measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom u).symm
        _ = F u := (hF u).symm
    have hFs := hFRange s hs
    have hFu := hFRange u hu
    have hset := hEhrhard Ks Ku hKsconv hKuconv a b ha hb hab
      (by rw [hmassS]; exact hFs.1) (by rw [hmassS]; exact hFs.2)
      (by rw [hmassU]; exact hFu.1) (by rw [hmassU]; exact hFu.2)
    have hquantS : standardGaussianQuantile (μ.real Ks) = G s := by
      simpa [cdfGaussianQuantile, hmassS] using (hG s).symm
    have hquantU : standardGaussianQuantile (μ.real Ku) = G u := by
      simpa [cdfGaussianQuantile, hmassU] using (hG u).symm
    have hsubset : weightedMinkowski a Ks b Ku ⊆
        {z | X z ≤ a * s + b * u} := by
      intro z hz
      rcases hz with ⟨x, hx, y, hy, rfl⟩
      change X x ≤ s at hx
      change X y ≤ u at hy
      have hconv := hXconvex.2 (Set.mem_univ x) (Set.mem_univ y)
        ha.le hb.le hab
      have hle : X (a • x + b • y) ≤ a * X x + b * X y := by
        simpa [smul_eq_mul] using hconv
      calc
        X (a • x + b • y) ≤ a * X x + b * X y := hle
        _ ≤ a * s + b * u := add_le_add
          (mul_le_mul_of_nonneg_left hx ha.le)
          (mul_le_mul_of_nonneg_left hy hb.le)
    have hmono : μ.real (weightedMinkowski a Ks b Ku) ≤ F (a * s + b * u) := by
      calc
        μ.real (weightedMinkowski a Ks b Ku) ≤
            μ.real {z | X z ≤ a * s + b * u} := MeasureTheory.measureReal_mono hsubset
        _ = μ.real {z | X z < a * s + b * u} :=
            (measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom _).symm
        _ = F (a * s + b * u) := (hF _).symm
    rw [hquantS, hquantU] at hset
    have hfinal := hset.trans hmono
    simpa [smul_eq_mul] using hfinal
  apply transformed_cdf_concave_of_ehrhard_mass F G hrep hMass

/-- Full support and positive-degree scaling put the strict CDF of a continuous
homogeneous observable strictly inside `(0,1)` at every positive threshold. -/
theorem productGaussian_cdf_range_of_positive_degree
    {κ : Type*} [Fintype κ]
    (X : (κ → ℝ) → ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hX : Continuous X) (hXzero : X 0 = 0)
    (hscale : ∀ c x, 0 ≤ c → X (c • x) = c ^ p * X x)
    (hnonzero : ∃ x, 0 < X x) {s : ℝ} (hs : 0 < s) :
    0 < (productStandardGaussian κ).real {x | X x < s} ∧
      (productStandardGaussian κ).real {x | X x < s} < 1 := by
  let μ := productStandardGaussian κ
  let A : Set (κ → ℝ) := {x | X x < s}
  obtain ⟨v, hv⟩ := hnonzero
  let c : ℝ := (s + 1) / X v + 1
  have hc1 : 1 ≤ c := by
    dsimp [c]
    have hratio : 0 < (s + 1) / X v := div_pos (by linarith) hv
    linarith
  have hcpow : c ≤ c ^ p := by
    calc
      c = c ^ 1 := by simp
      _ ≤ c ^ p := pow_le_pow_right₀ hc1 hp
  have hXcv : s < X (c • v) := by
    rw [hscale c v (by linarith : 0 ≤ c)]
    calc
      s < c * X v := by
        dsimp [c]
        have hv' : 0 < X v := hv
        field_simp
        nlinarith
      _ ≤ c ^ p * X v := mul_le_mul_of_nonneg_right hcpow hv.le
  let B : Set (κ → ℝ) := {x | s < X x}
  have hAopen : IsOpen A := by
    dsimp [A]
    exact isOpen_lt hX continuous_const
  have hAne : A.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [A, hXzero] using hs
  have hBopen : IsOpen B := by
    dsimp [B]
    exact isOpen_lt continuous_const hX
  have hBne : B.Nonempty := ⟨c • v, hXcv⟩
  have hApos : 0 < μ A := by
    dsimp [μ]
    exact BrownianSharp.GaussianDensity.standardGaussian_open_pos hAopen hAne
  have hBpos : 0 < μ B := by
    dsimp [μ]
    exact BrownianSharp.GaussianDensity.standardGaussian_open_pos hBopen hBne
  have hAposReal : 0 < μ.real A := ENNReal.toReal_pos hApos.ne' (measure_ne_top μ A)
  have hBposReal : 0 < μ.real B := ENNReal.toReal_pos hBpos.ne' (measure_ne_top μ B)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    change X x < s at hxA
    change s < X x at hxB
    exact (not_lt_of_ge hxB.le) hxA
  have hsum := MeasureTheory.measureReal_union hdisj hBopen.measurableSet
    (measure_ne_top μ A) (measure_ne_top μ B)
  have hunionle : μ.real (A ∪ B) ≤ 1 := by
    calc
      μ.real (A ∪ B) ≤ μ.real Set.univ :=
        MeasureTheory.measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
      _ = 1 := by simp [μ]
  have hsum' : μ.real A + μ.real B ≤ 1 := by rw [← hsum]; exact hunionle
  constructor
  · exact hAposReal
  · linarith

/-- The normalized finite-grid moment has the full weak lower-tail property
under the actual product-Gaussian law, conditional only on set-level Ehrhard.
The row normalization makes its expectation exactly one; moment integrability,
continuity, scaling, and atomlessness are all discharged from the existing
Gaussian row and root infrastructure. -/
theorem normalized_finiteGridMoment_variance_sensitive_tail
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (heven : Even p)
    (A : ι → κ → ℝ)
    (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1)
    (hM : 0 < standardGaussianMoment p)
    (hEhrhard : GaussianEhrhard (κ → ℝ) (productStandardGaussian κ)) :
    VarianceSensitiveLowerTail (productStandardGaussian κ)
      (fun x => finiteGridMoment p A x / standardGaussianMoment p)
      (Real.pi / 4096) := by
  classical
  let μ : Measure (κ → ℝ) := productStandardGaussian κ
  let X : (κ → ℝ) → ℝ :=
    fun x => finiteGridMoment p A x / standardGaussianMoment p
  let R : (κ → ℝ) → ℝ := finiteGridRoot p A
  have hnonzero : ∃ i k, A i k ≠ 0 := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have hsum : (∑ k, A i k ^ 2) = 1 := hnorm i
    by_contra hnz
    have hz : ∀ k, A i k = 0 := by
      intro k
      by_contra hk
      exact hnz ⟨i, k, hk⟩
    have hzero : (∑ k, A i k ^ 2) = 0 := by simp [hz]
    rw [hzero] at hsum
    norm_num at hsum
  have hrootnonneg : ∀ x, 0 ≤ R x :=
    fun x => finiteGridRoot_nonneg p hp A x
  have hXeq : X = fun x => R x ^ p / standardGaussianMoment p := by
    funext x
    dsimp [X, R]
    rw [← finiteGridRoot_pow_eq_moment p hp A x]
  have hXcont : Continuous X := by
    rw [hXeq]
    exact (finiteGridRoot_continuous p hp A).pow p |>.div_const _
  have hXmeas : Measurable X := hXcont.measurable
  have hXnonneg : ∀ x, 0 ≤ X x := by
    intro x
    rw [hXeq]
    exact div_nonneg (pow_nonneg (hrootnonneg x) _) hM.le
  have hXzero : X 0 = 0 := by
    rw [hXeq]
    have hR0 : R 0 = 0 := by
      have hs := finiteGridRoot_smul p hp A (0 : κ → ℝ) (0 : ℝ) (by norm_num)
      simpa using hs
    norm_num [hR0, show p ≠ 0 by omega, hM.ne']
  have hXscale : ∀ c x, 0 ≤ c → X (c • x) = c ^ p * X x := by
    intro c x hc
    rw [hXeq]
    change finiteGridRoot p A (c • x) ^ p / standardGaussianMoment p =
      c ^ p * (finiteGridRoot p A x ^ p / standardGaussianMoment p)
    rw [finiteGridRoot_smul p hp A x c hc, mul_pow]
    ring
  obtain ⟨x₀, hx₀⟩ := finiteGridRoot_exists_pos_of_nonzero_entry p hp A hnonzero
  have hXpos : 0 < X x₀ := by
    rw [hXeq]
    exact div_pos (pow_pos hx₀ (by omega)) hM
  have hFRange : ∀ s, 0 < s → 0 < (fun r => μ.real {x | X x < r}) s ∧
        (fun r => μ.real {x | X x < r}) s < 1 := by
    intro s hs
    change 0 < μ.real {x | X x < s} ∧ μ.real {x | X x < s} < 1
    exact productGaussian_cdf_range_of_positive_degree X p (by omega)
      hXcont hXzero hXscale ⟨x₀, hXpos⟩ hs
  have hAtom : ∀ r, μ {x | X x = r} = 0 := by
    intro r
    by_cases hr : 0 ≤ r
    · let z : ℝ := (standardGaussianMoment p * r) ^ (1 / (p : ℝ))
      have hz : 0 ≤ z := by
        dsimp [z]
        exact Real.rpow_nonneg (by positivity) _
      have hzp : z ^ p = standardGaussianMoment p * r := by
        dsimp [z]
        simpa [one_div, Real.rpow_natCast] using
          (Real.rpow_inv_natCast_pow
            (show 0 ≤ standardGaussianMoment p * r by positivity)
            (show p ≠ 0 by omega))
      have hsubset : {x | X x = r} ⊆ {x | R x = z} := by
        intro x hx
        have hx' : R x ^ p / standardGaussianMoment p = r := by
          simpa [X, hXeq] using hx
        have hpow : R x ^ p = standardGaussianMoment p * r :=
          by simpa [mul_comm] using (div_eq_iff hM.ne').mp hx'
        have hRp : (R x) ^ (p : ℝ) = z ^ (p : ℝ) := by
          simpa [Real.rpow_natCast] using hpow.trans hzp.symm
        have hmono := Real.strictMonoOn_rpow_Ici_of_exponent_pos
          (show 0 < (p : ℝ) by exact_mod_cast (by omega : 0 < p))
        rcases lt_trichotomy (R x) z with hlt | heq | hgt
        · exact False.elim (by
            have h := hmono (Set.mem_Ici.mpr (hrootnonneg x)) (Set.mem_Ici.mpr hz) hlt
            linarith [hRp])
        · exact heq
        · exact False.elim (by
            have h := hmono (Set.mem_Ici.mpr hz) (Set.mem_Ici.mpr (hrootnonneg x)) hgt
            linarith [hRp])
      exact MeasureTheory.measure_mono_null hsubset
        (finiteGridRoot_all_levels_standardGaussian_measure_zero_of_nonzero_entry
          p hp A hnonzero z)
    · have hrneg : r < 0 := lt_of_not_ge hr
      have hempty : {x | X x = r} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        linarith [hXnonneg x]
      rw [hempty]
      simp
  have hconvex : ConvexOn ℝ Set.univ X := by
    have h := (finiteGridMoment_convexOn p hp A).smul
      (inv_nonneg.mpr hM.le)
    simpa [X, div_eq_mul_inv, mul_comm] using h
  let F : ℝ → ℝ := fun s => μ.real {x | X x < s}
  let G : ℝ → ℝ := cdfGaussianQuantile F
  have hF : ∀ s, F s = μ.real {x | X x < s} := fun _ => rfl
  have hG : ∀ s, G s = cdfGaussianQuantile F s := fun _ => rfl
  have hGconcave : ConcaveOn ℝ (Set.Ioi 0) G :=
    transformed_cdf_concave_of_set_ehrhard μ X hconvex hXmeas hAtom
      F G hF hFRange hEhrhard hG
  have hcoeff : MemLp (id : (κ → ℝ) → κ → ℝ) 2 μ := by
    apply MeasureTheory.memLp_pi_iff.mpr
    intro k
    exact (GaussianRows.coordinate_gaussian
      (fun (j : κ) (x : κ → ℝ) => x j)
      (fun j => measurable_pi_apply j)
      (fun j => productStandardGaussian_coordinate_law j) k).memLp_two
  have hsumLp : MemLp (fun x => ∑ i, rowEvaluation A x i ^ p) 2 μ := by
    have hterm : ∀ i, MemLp (fun x => rowEvaluation A x i ^ p) 2 μ := by
      intro i
      convert normalized_matrix_row_power_memLp_two A hnorm i p using 1 <;> rfl
    simpa using (memLp_finsetSum (Finset.univ : Finset ι)
      (fun i _ => hterm i))
  have hmomentLp : MemLp (fun x => finiteGridMoment p A x) 2 μ := by
    have h := hsumLp.const_mul ((Fintype.card ι : ℝ)⁻¹)
    have heq : (fun x => finiteGridMoment p A x) =
        (fun x => (∑ i, rowEvaluation A x i ^ p) / Fintype.card ι) := by
      funext x
      exact finiteGridMoment_eq_raw_average_of_even p heven A x
    rw [heq]
    simpa [div_eq_mul_inv, mul_comm] using h
  have hXLp : MemLp X 2 μ := by
    have h := hmomentLp.const_mul (standardGaussianMoment p)⁻¹
    simpa [X, div_eq_mul_inv, mul_comm] using h
  have hmeanPA : (∫ x : κ → ℝ,
      normalizedPowerAverage (fun i x => ∑ k, A i k * x k)
        p (standardGaussianMoment p) x ∂μ) = 1 := by
    dsimp [μ, productStandardGaussian]
    exact normalized_matrix_power_average_mean A hnorm p hM.ne'
  have hPAeq : (fun x : κ → ℝ => X x) =
      (fun x => normalizedPowerAverage (fun i x => ∑ k, A i k * x k)
        p (standardGaussianMoment p) x) := by
    funext x
    dsimp [X]
    exact (normalized_matrix_power_average_eq_moment A p heven x).symm
  have hmean : μ[X] = 1 := by
    rw [show μ[X] = ∫ x : κ → ℝ, X x ∂μ by rfl, hPAeq]
    exact hmeanPA
  have hmeanPos : 0 < μ[X] := by rw [hmean]; norm_num
  intro t ht
  have hstrict := mean_lower_tail_of_transformed_cdf_concave_actual
    μ X hXLp hXmeas hXnonneg hmeanPos hAtom F G hF hGconcave
      (by
        intro s hs
        exact cdfGaussianQuantile_representation F
          (hFRange s hs).1 (hFRange s hs).2) t (by linarith)
  let a := μ[X] - t * Real.sqrt (ProbabilityTheory.variance X μ)
  have hweakLevel : μ.real {x | X x ≤ a} = μ.real {x | X x < a} :=
    (measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom a).symm
  have hevent : {x | X x - μ[X] < -t * Real.sqrt (ProbabilityTheory.variance X μ)} =
      {x | X x < a} := by
    ext x
    simp only [Set.mem_setOf_eq]
    dsimp [a]
    constructor <;> intro hx <;> linarith
  have hbound : μ.real {x | X x ≤ a} ≤
      Real.exp (-Real.pi * (t - 1) ^ 2 / 1024) := by
    rw [hweakLevel]
    rw [hevent.symm]
    exact hstrict
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  have hsq : t ^ 2 / 4 ≤ (t - 1) ^ 2 := by nlinarith
  nlinarith [Real.pi_pos]

/-- The relaxed variance-sensitive lower tail with a weak threshold follows
from the strict PV estimate when all levels are atomless. -/
theorem varianceSensitiveLowerTail_of_mean_lower_tail_strict
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X)
    (hAtom : ∀ r, μ {ω | X ω = r} = 0)
    (hstrict : ∀ t : ℝ, 1 < t →
      μ.real {ω | X ω - μ[X] < -t *
        Real.sqrt (ProbabilityTheory.variance X μ)} ≤
          Real.exp (-Real.pi * (t - 1) ^ 2 / 1024)) :
    VarianceSensitiveLowerTail μ X (Real.pi / 4096) := by
  intro t ht
  let a := μ[X] - t * Real.sqrt (ProbabilityTheory.variance X μ)
  rw [← measureReal_strictLevel_eq_weakLevel_of_null μ X hXmeas hAtom a]
  have hstrictAt : μ.real {ω | X ω - μ[X] < -t *
      Real.sqrt (ProbabilityTheory.variance X μ)} ≤
        Real.exp (-Real.pi * (t - 1) ^ 2 / 1024) := hstrict t (by linarith)
  have hrewrite : {ω | X ω < a} =
      {ω | X ω - μ[X] < -t * Real.sqrt (ProbabilityTheory.variance X μ)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    dsimp [a]
    constructor <;> intro h <;> linarith
  rw [← hrewrite] at hstrictAt
  refine hstrictAt.trans (Real.exp_le_exp.mpr ?_)
  have hsq : t ^ 2 / 4 ≤ (t - 1) ^ 2 := by nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

/-- Scaling a statistic by a positive constant preserves its normalized
variance-sensitive tail, including the actual mean and variance of the scaled
statistic. -/
theorem varianceSensitiveLowerTail_const_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c C : ℝ) (hc : 0 < c)
    (htail : VarianceSensitiveLowerTail μ X C) :
    VarianceSensitiveLowerTail μ (fun ω => c * X ω) C := by
  have hmean : μ[fun ω => c * X ω] = c * μ[X] := by
    rw [show μ[fun ω => c * X ω] = ∫ ω, c * X ω ∂μ by rfl,
      integral_const_mul]
  have hvariance : ProbabilityTheory.variance (fun ω => c * X ω) μ =
      c ^ 2 * ProbabilityTheory.variance X μ := by
    exact ProbabilityTheory.variance_const_mul c X μ
  have hsqrt : Real.sqrt (c ^ 2 * ProbabilityTheory.variance X μ) =
      c * Real.sqrt (ProbabilityTheory.variance X μ) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]
  intro t ht
  have h := htail t ht
  have hevent : {ω | c * X ω ≤ μ[fun ω => c * X ω] -
      t * Real.sqrt (ProbabilityTheory.variance (fun ω => c * X ω) μ)} =
      {ω | X ω ≤ μ[X] - t * Real.sqrt (ProbabilityTheory.variance X μ)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hmean, hvariance, hsqrt]
    constructor <;> intro hx <;> nlinarith
  rw [hevent]
  exact h

/-- Both the normalized moment and its normalized p-th root inherit the
variance-sensitive lower tail from the same finite-grid root. The only
geometric premise is set-level Gaussian Ehrhard for the ambient product law.
The moment case is independently proved above; this theorem adds the root
statistic needed for the second confinement application. -/
theorem normalized_finiteGridMoment_root_variance_sensitive_tail
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (heven : Even p) (A : ι → κ → ℝ)
    (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1)
    (hM : 0 < standardGaussianMoment p)
    (hEhrhard : GaussianEhrhard (κ → ℝ)
      (Measure.pi (fun _ : κ => ProbabilityTheory.gaussianReal 0 1))) :
    VarianceSensitiveLowerTail
      (Measure.pi (fun _ : κ => ProbabilityTheory.gaussianReal 0 1))
      (fun x => (finiteGridMoment p A x / standardGaussianMoment p) ^
        (1 / (p : ℝ))) (Real.pi / 4096) := by
  classical
  let μ : Measure (κ → ℝ) :=
    Measure.pi (fun _ : κ => ProbabilityTheory.gaussianReal 0 1)
  have hnonzero : ∃ i k, A i k ≠ 0 := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have hsumpos : 0 < ∑ k, A i k ^ 2 := by rw [hnorm i]; norm_num
    by_contra h
    push_neg at h
    have hz : ∀ k, A i k = 0 := fun k => h i k
    have : ∑ k, A i k ^ 2 = 0 := by simp [hz]
    linarith
  have hcoeff : MemLp (id : (κ → ℝ) → κ → ℝ) 2 μ := by
    apply MeasureTheory.memLp_pi_iff.mpr
    intro k
    exact (GaussianRows.coordinate_gaussian
      (fun (j : κ) (x : κ → ℝ) => x j)
      (fun j => measurable_pi_apply j)
      (fun j => productStandardGaussian_coordinate_law j) k).memLp_two
  have hrootLp : MemLp (fun x => finiteGridRoot p A x) 2 μ :=
    finiteGridRoot_memLp_two_of_coeff_memLp hcoeff p hp A
  have hrootAtom : ∀ r, μ {x | finiteGridRoot p A x = r} = 0 := by
    intro r
    exact finiteGridRoot_all_levels_standardGaussian_measure_zero_of_nonzero_entry
      p hp A hnonzero r
  have hrootStrict : ∀ t : ℝ, 1 < t →
      μ.real {x | finiteGridRoot p A x - μ[finiteGridRoot p A] <
        -t * Real.sqrt (ProbabilityTheory.variance (finiteGridRoot p A) μ)} ≤
          Real.exp (-Real.pi * (t - 1) ^ 2 / 1024) := by
    intro t ht
    exact finiteGridRoot_mean_lower_tail_of_ehrhard_mass p hp A hnonzero t ht
      (finiteGridRoot_ehrhard_mass_of_set_ehrhard p hp A hnonzero hEhrhard)
  have hrootTail : VarianceSensitiveLowerTail μ (finiteGridRoot p A)
      (Real.pi / 4096) :=
    varianceSensitiveLowerTail_of_mean_lower_tail_strict μ
      (finiteGridRoot p A) (finiteGridRoot_continuous p hp A).measurable
      hrootAtom hrootStrict
  let c : ℝ := ((standardGaussianMoment p) ^ (1 / (p : ℝ)))⁻¹
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hscaled := varianceSensitiveLowerTail_const_mul μ
    (finiteGridRoot p A) hrootLp c (Real.pi / 4096) hc hrootTail
  have hpoint : ∀ x : κ → ℝ,
      (finiteGridMoment p A x / standardGaussianMoment p) ^ (1 / (p : ℝ)) =
        c * finiteGridRoot p A x := by
    intro x
    rw [← normalized_matrix_power_average_eq_moment A p heven x]
    rw [normalized_matrix_power_root_eq p hp heven A hM x]
    dsimp [c]
    rw [div_eq_mul_inv]
    change finiteGridRoot p A x *
        ((standardGaussianMoment p) ^ (1 * (p : ℝ)⁻¹))⁻¹ =
      ((standardGaussianMoment p) ^ (1 * (p : ℝ)⁻¹))⁻¹ *
        finiteGridRoot p A x
    exact mul_comm _ _
  intro t ht
  have h := hscaled t ht
  have hfun : (fun x : κ → ℝ =>
      (finiteGridMoment p A x / standardGaussianMoment p) ^ (1 / (p : ℝ))) =
      (fun x => c * finiteGridRoot p A x) := funext hpoint
  have hmean : μ[fun x => (finiteGridMoment p A x /
      standardGaussianMoment p) ^ (1 / (p : ℝ))] =
      μ[fun x => c * finiteGridRoot p A x] := by rw [hfun]
  have hvariance : ProbabilityTheory.variance
      (fun x => (finiteGridMoment p A x / standardGaussianMoment p) ^
        (1 / (p : ℝ))) μ = ProbabilityTheory.variance
          (fun x => c * finiteGridRoot p A x) μ := by rw [hfun]
  have hevent :
      {x | (finiteGridMoment p A x / standardGaussianMoment p) ^
        (1 / (p : ℝ)) ≤ μ[fun x => (finiteGridMoment p A x /
          standardGaussianMoment p) ^ (1 / (p : ℝ))] - t *
          Real.sqrt (ProbabilityTheory.variance
            (fun x => (finiteGridMoment p A x / standardGaussianMoment p) ^
              (1 / (p : ℝ))) μ)} =
      {x | c * finiteGridRoot p A x ≤ μ[fun x => c * finiteGridRoot p A x] -
          t * Real.sqrt (ProbabilityTheory.variance
            (fun x => c * finiteGridRoot p A x) μ)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [hpoint x, hmean, hvariance]
  change μ.real {x | (finiteGridMoment p A x / standardGaussianMoment p) ^
      (1 / (p : ℝ)) ≤ μ[fun x => (finiteGridMoment p A x /
        standardGaussianMoment p) ^ (1 / (p : ℝ))] - t *
          Real.sqrt (ProbabilityTheory.variance
            (fun x => (finiteGridMoment p A x / standardGaussianMoment p) ^
              (1 / (p : ℝ))) μ)} ≤ _
  rw [hevent]
  exact h

/-- The normalized moment and its p-th root both satisfy the variance-sensitive
tail under set-level Ehrhard alone; positivity of the normalizing Gaussian
moment is discharged from the exact even-moment formula. -/
theorem normalized_finiteGridMoment_and_root_variance_sensitive_tail
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (heven : Even p) (A : ι → κ → ℝ)
    (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1)
    (hEhrhard : GaussianEhrhard (κ → ℝ)
      (productStandardGaussian κ)) :
    VarianceSensitiveLowerTail (productStandardGaussian κ)
      (fun x => finiteGridMoment p A x / standardGaussianMoment p)
      (Real.pi / 4096) ∧
    VarianceSensitiveLowerTail (productStandardGaussian κ)
      (fun x => (finiteGridMoment p A x / standardGaussianMoment p) ^
        (1 / (p : ℝ))) (Real.pi / 4096) := by
  obtain ⟨k, hpEq⟩ := heven
  subst p
  have heven' : Even (k + k) := ⟨k, rfl⟩
  have hM : 0 < standardGaussianMoment (k + k) := by
    simpa [two_mul] using standardGaussianMoment_even_pos k
  constructor
  · exact normalized_finiteGridMoment_variance_sensitive_tail
      (k + k) hp heven' A hnorm hM hEhrhard
  · exact normalized_finiteGridMoment_root_variance_sensitive_tail
      (k + k) hp heven' A hnorm hM hEhrhard

end BrownianSharp
