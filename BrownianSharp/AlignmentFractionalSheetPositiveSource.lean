import BrownianSharp.AlignmentFractionalSheetTensorFeature
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.CameronMartin
import BrownianSharp.AlignmentCompactFeatureBall

/-! Positive-cube source embedding into the actual full-line product source. -/

noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalSheetPositiveSource

open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentFractionalSheetMvNGram
open BrownianSharp.AlignmentFractionalSheetPositive
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensor
open BrownianSharp.AlignmentSigmaFiniteL2Tensor
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.CameronMartin
open BrownianSharp.AlignmentCompactFeatureBall

abbrev FullProductL2 (d : ℕ) :=
  Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))

/-- Restriction of the whole-space product source to the unit cube. -/
noncomputable def restrictToUnitCube (d : ℕ) :
    FullProductL2 d →L[ℝ] UnitCubeL2 d :=
  Lp.LpToLpOfMeasureLeSMul (p := 2) (μ :=
    (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (unitCubeSet d)) (ν := Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))
    (c := 1) (by simp)
    (by simpa using (Measure.restrict_le_self :
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (unitCubeSet d) ≤ Measure.pi (fun _ : Fin d => (volume : Measure ℝ))))

/-- Pairing with a zero-extended cube source is exactly pairing after
restriction to the cube. -/
theorem unitCubeZeroExtend_inner {d : ℕ} (F : FullProductL2 d)
    (g : UnitCubeL2 d) :
    ⟪F, unitCubeZeroExtend g⟫ = ⟪restrictToUnitCube d F, g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  simp only [Real.inner_apply]
  let μ := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  have hJ : (unitCubeZeroExtend g : (Fin d → ℝ) → ℝ) =ᵐ[μ]
      (unitCubeSet d).indicator (g : (Fin d → ℝ) → ℝ) := by
    change (MemLp.toLp ((unitCubeSet d).indicator (g : (Fin d → ℝ) → ℝ))
      ((memLp_indicator_iff_restrict (measurableSet_unitCubeSet d)).2 (Lp.memLp g)) :
        (Fin d → ℝ) → ℝ) =ᵐ[μ]
      (unitCubeSet d).indicator (g : (Fin d → ℝ) → ℝ)
    exact MemLp.coeFn_toLp _
  calc
    (∫ u, (F : (Fin d → ℝ) → ℝ) u * (unitCubeZeroExtend g : (Fin d → ℝ) → ℝ) u ∂μ) =
        ∫ u, (unitCubeSet d).indicator
          (fun u => (F : (Fin d → ℝ) → ℝ) u * (g : (Fin d → ℝ) → ℝ) u) u ∂μ := by
      apply integral_congr_ae
      filter_upwards [hJ] with u hu
      by_cases hs : u ∈ unitCubeSet d
      · rw [hu]
        simp [Set.indicator_of_mem hs]
      · have hz : (unitCubeZeroExtend g : (Fin d → ℝ) → ℝ) u = 0 := by
          rw [hu]
          simp [Set.indicator, hs]
        simp [Set.indicator, hs, hz]
    _ = ∫ u, (F : (Fin d → ℝ) → ℝ) u * (g : (Fin d → ℝ) → ℝ) u ∂
        (μ.restrict (unitCubeSet d)) := by
      rw [integral_indicator (measurableSet_unitCubeSet d)]
    _ = ∫ u, (restrictToUnitCube d F : (Fin d → ℝ) → ℝ) u *
        (g : (Fin d → ℝ) → ℝ) u ∂(μ.restrict (unitCubeSet d)) := by
      apply integral_congr_ae
      have hR := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := 1)
        (by simp) (by simpa using (Measure.restrict_le_self :
          μ.restrict (unitCubeSet d) ≤ μ)) F
      filter_upwards [hR] with u hu
      have hu' : (restrictToUnitCube d F : (Fin d → ℝ) → ℝ) u =
          (F : (Fin d → ℝ) → ℝ) u := by
        simpa only [restrictToUnitCube, μ] using hu
      rw [hu']

/-- Restricting a normalized whole-line MvN axis feature to positive time
recovers the gamma-scaled causal RL kernel vector. -/
theorem normalizedAxis_restrict {H : ℝ} (hH0 : 0 < H) (hH1 : H < 1)
    (t : UnitInterval) :
    restrictUnitCLM (normalizedAxis H hH0 hH1 t) =
      (Real.Gamma (H+1/2) *
        ‖mvNFullFeature (H-1/2) 1
          (mvNFullKernel_memLp hH0 hH1
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) •
        kernelVector (H+1/2) t.1 (by linarith)
          (Set.mem_Icc.mp t.property).1 (Set.mem_Icc.mp t.property).2 := by
  have ht0 : 0 ≤ (t:ℝ) := (Set.mem_Icc.mp t.property).1
  have ht1 : (t:ℝ) ≤ 1 := (Set.mem_Icc.mp t.property).2
  have hR := restrict_mvNFullKernel_eq_RL (p := H-1/2) (t := t.1)
    (by linarith) ht0 ht1
    (mvNFullKernel_memLp hH0 hH1 t.property)
  have hR' : restrictUnitCLM (mvNFullFeature (H-1/2) t.1
      (mvNFullKernel_memLp hH0 hH1 t.property)) =
      Real.Gamma (H+1/2) • kernelVector (H+1/2) t.1 (by linarith) ht0 ht1 := by
    simpa only [mvNFullFeature, show H-1/2+1 = H+1/2 by ring] using hR
  change restrictUnitCLM (mvNNormalizedFeature H hH0 hH1 t.1
    ht0 ht1) = _
  unfold mvNNormalizedFeature
  rw [map_smul, hR']
  rw [smul_smul]
  congr 1
  ring

/-- Pointwise positive-time form of the restricted normalized axis feature. -/
theorem normalizedAxis_ae_causal {H : ℝ} (hH0 : 0 < H) (hH1 : H < 1)
    (t : UnitInterval) :
    (normalizedAxis H hH0 hH1 t : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun u => (Real.Gamma (H+1/2) *
        ‖mvNFullFeature (H-1/2) 1
          (mvNFullKernel_memLp hH0 hH1
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        causalKernel (H+1/2) t.1 u) := by
  let c := Real.Gamma (H+1/2) *
    ‖mvNFullFeature (H-1/2) 1
      (mvNFullKernel_memLp hH0 hH1
        (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹
  have ht0 : 0 ≤ (t:ℝ) := (Set.mem_Icc.mp t.property).1
  have ht1 : (t:ℝ) ≤ 1 := (Set.mem_Icc.mp t.property).2
  have hR := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := 1) (by simp)
    (by simpa using (Measure.restrict_le_self :
      volume.restrict (Set.Icc (0:ℝ) 1) ≤ volume)) (normalizedAxis H hH0 hH1 t)
  have hEq := normalizedAxis_restrict hH0 hH1 t
  have hSmul := Lp.coeFn_smul c
    (kernelVector (H+1/2) t.1 (by linarith) ht0 ht1)
  have hα : (1/2:ℝ) < H+1/2 := by linarith
  have hK := MemLp.coeFn_toLp
    (causalKernel_memLp_unit (α := H+1/2) (t := t.1) hα ht0 ht1)
  filter_upwards [hR, hSmul, hK] with u hR hSmul hK
  have hR' : (restrictUnitCLM (normalizedAxis H hH0 hH1 t) : ℝ → ℝ) u =
      (normalizedAxis H hH0 hH1 t : ℝ → ℝ) u := hR
  have hEq' : (restrictUnitCLM (normalizedAxis H hH0 hH1 t) : ℝ → ℝ) u =
      c * (kernelVector (H+1/2) t.1 (by linarith) ht0 ht1 : ℝ → ℝ) u := by
    calc
      _ = (c • kernelVector (H+1/2) t.1 (by linarith) ht0 ht1 : UnitL2) u := by
        simpa [c] using congrArg (fun z : UnitL2 => (z : ℝ → ℝ) u) hEq
      _ = c * (kernelVector (H+1/2) t.1 (by linarith) ht0 ht1 : ℝ → ℝ) u := by
        simpa [smul_eq_mul] using hSmul
  calc
    (normalizedAxis H hH0 hH1 t : ℝ → ℝ) u =
        (restrictUnitCLM (normalizedAxis H hH0 hH1 t) : ℝ → ℝ) u := hR'.symm
    _ = c * (kernelVector (H+1/2) t.1 (by linarith) ht0 ht1 : ℝ → ℝ) u := hEq'
    _ = c * causalKernel (H+1/2) t.1 u := by
      rw [show (kernelVector (H+1/2) t.1 (by linarith) ht0 ht1 : ℝ → ℝ) u =
        causalKernel (H+1/2) t.1 u by simpa [kernelVector] using hK]
    _ = (Real.Gamma (H+1/2) *
        ‖mvNFullFeature (H-1/2) 1
          (mvNFullKernel_memLp hH0 hH1
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        causalKernel (H+1/2) t.1 u := rfl

/-- The full sheet feature, restricted to the positive cube, is a constant
multiple of the literal tensor RL kernel. -/
theorem fractionalSheetFeature_ae_positiveKernel {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (t : BrownianCubeAnchor d) :
    fractionalSheetFeature H hH t =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (unitCubeSet d)]
      (fun u => (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        Latest.fractionalTensorKernel (fun i => H i+1/2) t u) := by
  let v : Fin d → FullLineL2 := fun i => normalizedAxis (H i) (hH i).1 (hH i).2
    (cubeCoordinate i t)
  have hfeature : fractionalSheetFeature H hH t =
      productVector v := by
    change tensorContinuous v = productVector v
    exact tensorContinuous_apply v
  have hprod := productVector_ae v
  have haxis : ∀ i, v i =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun x => (Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        causalKernel (H i+1/2) (t.val i) x) := by
    intro i
    exact normalizedAxis_ae_causal (hH i).1 (hH i).2 (cubeCoordinate i t)
  have hpi := Measure.ae_eq_pi haxis
  have hpi' : (fun u : Fin d → ℝ => ∏ i, v i (u i)) =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (unitCubeSet d)]
      (fun u => ∏ i, (Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        causalKernel (H i+1/2) (t.val i) (u i)) := by
    have hpiProd : (fun u : Fin d → ℝ => ∏ i, v i (u i)) =ᵐ[
        Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))]
        (fun u => ∏ i, (Real.Gamma (H i+1/2) *
          ‖mvNFullFeature (H i-1/2) 1
            (mvNFullKernel_memLp (hH i).1 (hH i).2
              (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
          causalKernel (H i+1/2) (t.val i) (u i)) := by
      filter_upwards [hpi] with u hu
      apply Finset.prod_congr rfl
      intro i hi
      exact congrFun hu i
    rw [AlignmentFractionalTensor.unitCube_measure_eq_pi d]
    exact hpiProd
  have hprod' : fractionalSheetFeature H hH t =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (unitCubeSet d)] (fun u => ∏ i, v i (u i)) := by
    rw [hfeature]
    exact ae_mono (Measure.restrict_le_self :
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (unitCubeSet d) ≤ Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) hprod
  have halg (u : Fin d → ℝ) :
      (∏ i, (Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        causalKernel (H i+1/2) (t.val i) (u i)) =
      (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        Latest.fractionalTensorKernel (fun i => H i+1/2) t u := by
    change (∏ i, (Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        causalKernel (H i+1/2) (t.val i) (u i)) =
      (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        (∏ i, if u i < t.val i then
          (Real.Gamma (H i+1/2))⁻¹ * (t.val i-u i)^(H i+1/2-1) else 0)
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simp [BrownianSharp.AlignmentFractionalL2.causalKernel,
      BrownianSharp.AlignmentFractionalKernel.kernel]
  filter_upwards [hprod', hpi'] with u h1 h2
  rw [h1, h2]
  exact halg u

/-- Exact feature-operator factorization on the embedded positive cube. The
full MvN sheet feature restricted to positive source coordinates is the
Gamma/variance-normalized tensor RL kernel. -/
theorem fractionalSheetFeature_positiveSource_factor {d : ℕ}
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (g : UnitCubeL2 d) (t : BrownianCubeAnchor d) :
    ⟪fractionalSheetFeature H hH t, unitCubeZeroExtend g⟫ =
      (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        fractionalTensorRL (fun i => H i+1/2) (by intro i; linarith [(hH i).1])
          g t := by
  let c : ℝ := ∏ i, Real.Gamma (H i+1/2) *
    ‖mvNFullFeature (H i-1/2) 1
      (mvNFullKernel_memLp (hH i).1 (hH i).2
        (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹
  rw [unitCubeZeroExtend_inner]
  rw [L2.inner_def]
  simp only [Real.inner_apply]
  have hμ : (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (unitCubeSet d) ≤ Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) :=
    Measure.restrict_le_self
  have hR := Lp.coeFn_LpToLpOfMeasureLeSMul (p := 2) (c := 1) (by simp)
    (by simpa using hμ)
    (fractionalSheetFeature H hH t)
  have hK := fractionalSheetFeature_ae_positiveKernel H hH t
  calc
    (∫ u, (restrictToUnitCube d (fractionalSheetFeature H hH t) :
        (Fin d → ℝ) → ℝ) u * (g : (Fin d → ℝ) → ℝ) u ∂
          ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
            (unitCubeSet d))) =
        ∫ u, (c * Latest.fractionalTensorKernel (fun i => H i+1/2) t u) *
          (g : (Fin d → ℝ) → ℝ) u ∂
          ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
            (unitCubeSet d)) := by
      apply integral_congr_ae
      filter_upwards [hR, hK] with u hr hk
      have hr' : (restrictToUnitCube d (fractionalSheetFeature H hH t) :
          (Fin d → ℝ) → ℝ) u = (fractionalSheetFeature H hH t :
          (Fin d → ℝ) → ℝ) u := by
        simpa only [restrictToUnitCube] using hr
      have hk' : (fractionalSheetFeature H hH t :
          (Fin d → ℝ) → ℝ) u = c * Latest.fractionalTensorKernel
            (fun i => H i+1/2) t u := by
        simpa only [c] using hk
      rw [hr', hk']
    _ = c * ∫ u, Latest.fractionalTensorKernel (fun i => H i+1/2) t u *
        (g : (Fin d → ℝ) → ℝ) u ∂
          ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
            (unitCubeSet d)) := by
      change (∫ u, (c * Latest.fractionalTensorKernel (fun i => H i+1/2) t u) *
          (g : (Fin d → ℝ) → ℝ) u ∂
            ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
              (unitCubeSet d))) = _
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    _ = c * fractionalTensorRL (fun i => H i+1/2)
        (by intro i; linarith [(hH i).1]) g t := by
      rw [fractionalTensorRL_apply]
      rfl

/-- Continuous-path form of the positive-source factorization. -/
theorem fractionalSheetFeature_positiveSource_path_factor {d : ℕ}
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1)
    (g : UnitCubeL2 d) :
    featurePath (fractionalSheetFeature H hH) (unitCubeZeroExtend g) =
      (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) •
        fractionalTensorRL (fun i => H i+1/2)
          (by intro i; linarith [(hH i).1]) g := by
  ext t
  change ⟪unitCubeZeroExtend g, fractionalSheetFeature H hH t⟫ = _
  rw [real_inner_comm]
  rw [fractionalSheetFeature_positiveSource_factor]
  rfl

/-- The scaled true tensor RL unit-ball image embeds in the actual MvN
fractional-sheet feature ball via the isometric zero extension. -/
theorem scaled_fractionalIntegrationBall_subset_sheetFeatureBall {d : ℕ}
    (H : Fin d → ℝ) (hH : ∀ i, 0 < H i ∧ H i < 1) :
    Set.image (fun f : C(BrownianCubeAnchor d, ℝ) =>
      (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) • f)
      (Latest.fractionalIntegrationBall (fun i => H i+1/2)) ⊆
      featureBall (fractionalSheetFeature H hH) := by
  intro f hf
  rcases hf with ⟨f₀, hf₀, rfl⟩
  rw [Latest.fractionalIntegrationBall] at hf₀
  rcases hf₀ with ⟨g, hg, hpath⟩
  refine ⟨unitCubeZeroExtend g, ?_, ?_⟩
  · rw [unitCubeZeroExtend_norm]
    exact hg
  · rw [fractionalSheetFeature_positiveSource_path_factor]
    ext t
    change (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) *
        fractionalTensorRL (fun i => H i+1/2)
          (by intro i; linarith [(hH i).1]) g t =
      (∏ i, Real.Gamma (H i+1/2) *
        ‖mvNFullFeature (H i-1/2) 1
          (mvNFullKernel_memLp (hH i).1 (hH i).2
            (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1))‖⁻¹) * f₀ t
    rw [fractionalTensorRL_apply, hpath t]

end BrownianSharp.AlignmentFractionalSheetPositiveSource
