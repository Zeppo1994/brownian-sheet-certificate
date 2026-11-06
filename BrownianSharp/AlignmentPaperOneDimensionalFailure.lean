import BrownianSharp.AlignmentPaperGenericBumpCertified

/-! Remark 2.9 (the case `d = 1`): the Gaussian synthesis `V_n` is a family of
`2^n` independent bumps with disjoint supports, hence the confinement
probability is at least `(1 - e^{-a² n/2})^(2^n) = e^{-o(2^n)}` and the
displayed statement of Theorem 2.1 fails for `d = 1`. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace BrownianSharp.AlignmentPaperOneDimensionalFailure
open AlignmentPaperContinuumGenericBump AlignmentPaperContinuumGoodRegion
  AlignmentPaperGenericBumpCertified

theorem gaussian_Ioi_tail {t : ℝ} (ht : 0 ≤ t) :
    gaussianReal 0 1 (Set.Ioi t) ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / 2)) * gaussianReal 0 1 (Set.Ioi 0) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    withDensity_apply _ measurableSet_Ioi, withDensity_apply _ measurableSet_Ioi,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_right_eq_self _ t]
  refine lintegral_mono fun u => ?_
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem (show u + t ∈ Set.Ioi t by simp [hu]),
      Set.indicator_of_mem (show u ∈ Set.Ioi 0 from hu)]
    simp only [gaussianPDF, gaussianPDFReal, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have h : Real.exp (-(u + t) ^ 2 / 2) ≤ Real.exp (-t ^ 2 / 2) * Real.exp (-u ^ 2 / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hc : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h hc]
  · rw [Set.indicator_of_notMem (show u + t ∉ Set.Ioi t by simp; linarith)]
    simp

theorem gaussian_Iio_neg (t : ℝ) :
    gaussianReal 0 1 (Set.Iio (-t)) = gaussianReal 0 1 (Set.Ioi t) := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have h := congrArg (fun ν : Measure ℝ => ν (Set.Iio (-t))) hm
  rw [Measure.map_apply measurable_neg measurableSet_Iio,
    show (fun x : ℝ => -x) ⁻¹' Set.Iio (-t) = Set.Ioi t by ext x; simp] at h
  exact h.symm

/-- The sharp two-sided Gaussian tail `P(|g| > r) ≤ e^{-r²/2}`. -/
theorem gaussian_abs_tail {r : ℝ} (hr : 0 ≤ r) :
    (gaussianReal 0 1).real {x | r < |x|} ≤ Real.exp (-(r ^ 2) / 2) := by
  set ν := gaussianReal 0 1
  have hsplit : {x : ℝ | r < |x|} ⊆ Set.Iio (-r) ∪ Set.Ioi r := fun x hx => by
    rcases lt_abs.mp (show r < |x| from hx) with h | h
    · exact Or.inr h
    · exact Or.inl (show x < -r by linarith)
  have h0 : ν (Set.Iio 0) = ν (Set.Ioi 0) := by simpa using gaussian_Iio_neg 0
  have h1 : ν (Set.Ioi 0) + ν (Set.Iio 0) ≤ 1 := by
    calc _ = ν (Set.Ioi 0 ∪ Set.Iio 0) := (measure_union (Set.disjoint_left.mpr
          fun x (h : 0 < x) (h' : x < 0) => absurd h (not_lt.mpr h'.le)) measurableSet_Iio).symm
      _ ≤ 1 := prob_le_one
  have h2 : ν {x | r < |x|} ≤ ENNReal.ofReal (Real.exp (-(r ^ 2) / 2)) := by
    calc _ ≤ ν (Set.Iio (-r)) + ν (Set.Ioi r) := (measure_mono hsplit).trans (measure_union_le _ _)
      _ = ν (Set.Ioi r) + ν (Set.Ioi r) := by rw [gaussian_Iio_neg]
      _ ≤ _ := by
        have := gaussian_Ioi_tail hr
        calc _ ≤ ENNReal.ofReal (Real.exp (-(r ^ 2) / 2)) * ν (Set.Ioi 0) +
              ENNReal.ofReal (Real.exp (-(r ^ 2) / 2)) * ν (Set.Ioi 0) := add_le_add this this
          _ = ENNReal.ofReal (Real.exp (-(r ^ 2) / 2)) * (ν (Set.Ioi 0) + ν (Set.Iio 0)) := by
              rw [h0, mul_add]
          _ ≤ _ := by simpa using mul_le_mul_right h1 (ENNReal.ofReal (Real.exp (-(r ^ 2) / 2)))
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

/-- At each point of the cube at most one atom of `V_n` is nonzero (`d = 1`),
so `V_n` is bounded by the largest coefficient. -/
theorem abs_bumpSynthesis_le {n : ℕ} (ψ : AdmissibleBump) (z : LayerIndex 1 n → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (hz : ∀ i, |z i| ≤ r) (x : Fin 1 → ℝ) :
    |bumpSynthesis ψ z x| ≤ r := by
  by_cases h : ∃ a : LayerIndex 1 n, cubeBumpAtom ψ x a ≠ 0
  · obtain ⟨a, ha⟩ := h
    have hdepth : ∀ b c : LayerIndex 1 n, layerIndexDepth b = layerIndexDepth c := by
      intro b c
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have hb := layerIndexDepth_grade b
      have hc := layerIndexDepth_grade c
      simpa [Finsupp.sum_fintype, layerIndexDepth] using hb.trans hc.symm
    unfold bumpSynthesis
    rw [Finset.sum_eq_single a]
    · rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (cubeBumpAtom_abs_le_one ψ x a)).trans (hz a)
    · intro b _ hne
      by_contra h0
      exact hne (cubeBumpAtom_unique_address ψ x b a (hdepth b a)
        (fun h => h0 (by simp [h])) ha)
    · simp
  · simp only [not_exists, not_not] at h
    simpa [bumpSynthesis, h] using hr

/-- Remark 2.9 (i): for `d = 1` and every admissible bump, the confinement
event of Theorem 2.1 has probability at least `(1 - e^{-a² n/2})^(2^n)`
for every iid standard Gaussian family. -/
theorem oneDimensional_confinement_lower_bound.{u} (ψ : AdmissibleBump) {a : ℝ}
    (ha : 0 < a) (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (G : LayerIndex 1 n → Ω → ℝ)
    (hG : ∀ i, HasLaw (G i) (gaussianReal 0 1) P) (hInd : iIndepFun G P) :
    (1 - Real.exp (-(a ^ 2 * n / 2))) ^ (2 ^ n) ≤
      P.real {ω | ∀ x ∈ cubeSet 1,
        |bumpSynthesis ψ (fun i => G i ω) x| ≤
          a * Real.sqrt ((n : ℝ) * hyperbolicCount 1 n)} := by
  have : Nonempty (LayerIndex 1 n) := Fintype.card_pos_iff.mp (by
    simp [layerIndex_card 1 n one_pos])
  have : IsProbabilityMeasure P := (hG (Classical.arbitrary _)).isProbabilityMeasure
  have hS : hyperbolicCount 1 n = 1 := by simp [hyperbolicCount]
  set r : ℝ := a * Real.sqrt n with hr
  have hr0 : 0 ≤ r := by positivity
  have hsub : (⋂ i ∈ (Finset.univ : Finset (LayerIndex 1 n)), G i ⁻¹' {x : ℝ | |x| ≤ r}) ⊆
      {ω | ∀ x ∈ cubeSet 1, |bumpSynthesis ψ (fun i => G i ω) x| ≤
        a * Real.sqrt ((n : ℝ) * hyperbolicCount 1 n)} := by
    intro ω hω x _
    rw [hS, mul_one]
    exact abs_bumpSynthesis_le ψ _ hr0
      (fun i => by simpa using Set.mem_iInter₂.mp hω i (by simp)) x
  have hfac : ∀ i, 1 - Real.exp (-(a ^ 2 * n / 2)) ≤
      (P (G i ⁻¹' {x : ℝ | |x| ≤ r})).toReal := by
    intro i
    have hm : MeasurableSet {x : ℝ | r < |x|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hν : (P (G i ⁻¹' {x : ℝ | |x| ≤ r})).toReal =
        (gaussianReal 0 1).real {x : ℝ | |x| ≤ r} := by
      rw [← (hG i).map_eq]
      simp [Measure.real, Measure.map_apply_of_aemeasurable (hG i).aemeasurable
        (measurableSet_le continuous_abs.measurable measurable_const)]
    have hc := measureReal_compl (μ := gaussianReal 0 1) hm
    have hcs : {x : ℝ | r < |x|}ᶜ = {x : ℝ | |x| ≤ r} := by ext x; simp
    rw [hcs, probReal_univ] at hc
    have h2 : (gaussianReal 0 1).real {x : ℝ | r < |x|} ≤ Real.exp (-(a ^ 2 * n / 2)) :=
      (gaussian_abs_tail hr0).trans (le_of_eq (by
        rw [hr, mul_pow, Real.sq_sqrt n.cast_nonneg]; ring_nf))
    rw [hν, hc]
    linarith
  calc _ = ∏ _i : LayerIndex 1 n, (1 - Real.exp (-(a ^ 2 * n / 2))) := by
        rw [Finset.prod_const, Finset.card_univ, layerIndex_card 1 n one_pos]
        simp
    _ ≤ ∏ i : LayerIndex 1 n, (P (G i ⁻¹' {x : ℝ | |x| ≤ r})).toReal :=
        Finset.prod_le_prod₀ (fun _ _ => sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))) (fun i _ => hfac i)
    _ = _ := by
        rw [← ENNReal.toReal_prod, ← hInd.measure_inter_preimage_eq_mul _
          (fun i _ => measurableSet_le continuous_abs.measurable measurable_const)]
        rfl
    _ ≤ _ := measureReal_mono hsub

/-- Remark 2.9 (ii), quantitative form: for all `a, b > 0` the confinement
probability exceeds `exp (-b * nativeDimension 1 n)` for every large `n`
(with `N` independent of the iid realization). -/
theorem oneDimensional_confinement_probability_gt.{u} (ψ : AdmissibleBump)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (G : LayerIndex 1 n → Ω → ℝ),
      (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
      Real.exp (-b * nativeDimension 1 n) <
        P.real {ω | ∀ x ∈ cubeSet 1,
          |bumpSynthesis ψ (fun i => G i ω) x| ≤
            a * Real.sqrt ((n : ℝ) * hyperbolicCount 1 n)} := by
  have hb' : 0 < 1 - Real.exp (-b) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hlim : Filter.Tendsto (fun n : ℕ => Real.exp (-(a ^ 2 / 2 * n))) Filter.atTop
      (nhds 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < a ^ 2 / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hb')
  refine ⟨N, fun n hn Ω _ P G hG hInd => ?_⟩
  have hq := hN n hn
  have hq' : a ^ 2 / 2 * n = a ^ 2 * n / 2 := by ring
  rw [hq'] at hq
  have hpos := Real.exp_pos (-b)
  have hS : nativeDimension 1 n = ((2 ^ n : ℕ) : ℝ) := by simp [nativeDimension, hyperbolicCount]
  refine lt_of_lt_of_le ?_ (oneDimensional_confinement_lower_bound ψ ha n Ω P G hG hInd)
  rw [hS, mul_comm, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ (by linarith) hpos.le (by positivity)

/-- A standard iid Gaussian realization exists in every universe. -/
theorem exists_iid_gaussian_family.{u} (ι : Type) [Fintype ι] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (G : ι → Ω → ℝ),
      (∀ i, HasLaw (G i) (gaussianReal 0 1) P) ∧ iIndepFun G P := by
  let μ : Measure (ULift.{u} ℝ) := (gaussianReal 0 1).map ULift.up
  have : IsProbabilityMeasure μ :=
    ⟨by rw [Measure.map_apply measurable_up MeasurableSet.univ]; simp⟩
  refine ⟨ι → ULift.{u} ℝ, inferInstance, Measure.pi fun _ => μ,
    fun i ω => (ω i).down, fun i => ⟨?_, ?_⟩,
    iIndepFun_pi (X := fun _ => ULift.down) (fun _ => measurable_down.aemeasurable)⟩
  · exact (measurable_down.comp (measurable_pi_apply i)).aemeasurable
  · classical
    have h := Measure.pi_map_eval (fun _ : ι => μ) i
    show Measure.map (ULift.down ∘ Function.eval (β := fun _ : ι => ULift.{u} ℝ) i) _ = _
    rw [← Measure.map_map measurable_down (measurable_pi_apply i), h]
    simp [μ, Measure.map_map measurable_down measurable_up]
    exact Measure.map_id

/-- Remark 2.9 (ii): the `d = 1` instance of the conclusion of Theorem 2.1
(in the form `AdmissibleBumpIidConfinementStatement`) is false for every
admissible bump. -/
theorem not_oneDimensional_iid_confinement.{u} (ψ : AdmissibleBump) :
    ¬ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (G : LayerIndex 1 n → Ω → ℝ),
        (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
        P.real {ω | ∀ x ∈ cubeSet 1,
          |bumpSynthesis ψ (fun i => G i ω) x| ≤
            a * Real.sqrt ((n : ℝ) * hyperbolicCount 1 n)} ≤
          Real.exp (-b * nativeDimension 1 n) := by
  rintro ⟨a, b, ha, hb, N, hN⟩
  obtain ⟨N', hN'⟩ := oneDimensional_confinement_probability_gt.{u} ψ ha hb
  obtain ⟨Ω, _, P, G, hG, hInd⟩ := exists_iid_gaussian_family.{u} (LayerIndex 1 (max N N'))
  exact absurd (hN _ (le_max_left _ _) Ω P G hG hInd)
    (not_le.mpr (hN' _ (le_max_right _ _) Ω P G hG hInd))

/-- Remark 2.9, (2.40): `(1 - e^{-a²n/2})^{2^n} = e^{-o(|D_n|)}`, i.e. its logarithm is
`o(|D_n|)` with `|D_n| = 2^n` for `d = 1`. -/
theorem log_confinement_lower_bound_isLittleO {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun n : ℕ => Real.log ((1 - Real.exp (-(a ^ 2 * n / 2))) ^ (2 ^ n)) /
      nativeDimension 1 n) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => Real.exp (-(a ^ 2 * n / 2))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp <|
      (Filter.Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop).atTop_div_const
        (by norm_num)
  have h2 := (Real.continuousAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).tendsto.comp
    (tendsto_const_nhds.sub h1)
  rw [sub_zero, Real.log_one] at h2
  refine h2.congr' (Filter.Eventually.of_forall fun n => ?_)
  simp only [Function.comp_apply, Real.log_pow, nativeDimension, hyperbolicCount]
  field_simp
  simp

end BrownianSharp.AlignmentPaperOneDimensionalFailure
