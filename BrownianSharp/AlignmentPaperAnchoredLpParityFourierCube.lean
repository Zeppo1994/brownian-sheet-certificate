import BrownianSharp.AlignmentPaperAnchoredLpParityFourier

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentPaperAnchoredLpParityFourierCube

open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLpParityFourier
open BrownianSharp.AlignmentPaperAnchoredLpSourceFourier
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
open BrownianSharp.AlignmentPaperAnchoredLpFaceCoefficients
open BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
open BrownianSharp.AlignmentFractionalTensor
open HaarQuarter

/-- The actual parity-source coefficient is the cube integral with the
active sine multipliers and every lower-face mean weight retained. -/
theorem anchoredFaceSource_fourierCoeff_eq_cube {d : ℕ} {p : ℝ}
    (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (k : Fin d → ℤ) (J : Finset (Fin d))
    (hJ : ∀ i, i ∈ J ↔ k i ≠ 0) :
    UnitAddTorus.mFourierCoeff
        (fun x : UnitAddTorus (Fin d) =>
          ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℝ) : ℂ)) k =
      ∫ v, (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ) else
        -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) *
        (g v : ℂ) ∂cubeMeasure d := by
  classical
  let fold : UnitAddTorus (Fin d) → (Fin d → ℝ) :=
    fun x i => triangleWave (x i)
  let F : UnitAddTorus (Fin d) → ℂ := fun x =>
    ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℝ) : ℂ)
  let ψ : (Fin d → ℝ) → ℂ := fun v =>
    (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ) else
      -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) * (g v : ℂ)
  have hfactorMeas : Measurable (fun v : Fin d → ℝ =>
      ∏ i, if k i = 0 then ((1-v i:ℝ):ℂ) else
        -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) := by
    apply Finset.measurable_prod
    intro i hi
    by_cases hk : k i = 0 <;> simp [hk] <;> fun_prop
  have hgs : AEStronglyMeasurable (fun v : Fin d → ℝ => (g v : ℂ))
      (cubeMeasure d) := by
    exact Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      (Lp.stronglyMeasurable g).aestronglyMeasurable
  have hψsm : AEStronglyMeasurable ψ (cubeMeasure d) := by
    change AEStronglyMeasurable
      (fun v => (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ) else
        -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) *
        (g v : ℂ)) (cubeMeasure d)
    exact hfactorMeas.aestronglyMeasurable.mul hgs
  have hfold : MeasurePreserving fold (volume : Measure (UnitAddTorus (Fin d)))
      (cubeMeasure d) := by
    simpa [fold, cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi,
      unitIntervalMeasure] using measurePreserving_foldCoordinates d
  have hψmap : AEStronglyMeasurable ψ
      ((volume : Measure (UnitAddTorus (Fin d))).map fold) := by
    rw [hfold.map_eq]
    exact hψsm
  have hmap := MeasureTheory.integral_map hfold.measurable.aemeasurable hψmap
  rw [hfold.map_eq] at hmap
  have hprodSplit (v : Fin d → ℝ) :
      (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ) else
        -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) =
        (∏ i ∈ J, (-2 * Complex.I *
          (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ))) *
        ∏ i ∈ Finset.univ \ J, ((1-v i:ℝ):ℂ) := by
    classical
    calc
      _ = (∏ i ∈ Finset.univ \ J,
            if k i = 0 then ((1-v i:ℝ):ℂ) else
              -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) *
          ∏ i ∈ J, (if k i = 0 then ((1-v i:ℝ):ℂ) else
              -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) := by
            rw [← Finset.prod_sdiff (Finset.subset_univ J)]
      _ = (∏ i ∈ Finset.univ \ J, ((1-v i:ℝ):ℂ)) *
          ∏ i ∈ J, (-2 * Complex.I *
            (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) := by
            congr 1
            · apply Finset.prod_congr rfl
              intro i hi
              have hk : k i = 0 := by
                by_contra hk
                exact (Finset.mem_sdiff.mp hi).2 ((hJ i).2 hk)
              simp [hk]
            · apply Finset.prod_congr rfl
              intro i hi
              simp [(hJ i).1 hi]
      _ = _ := by ring
  have hpoint (x : UnitAddTorus (Fin d)) :
      F x * (∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i))) =
        ((2 : ℝ)^J.card : ℂ) * ψ (fold x) := by
    rw [anchoredFaceSource_characterProduct]
    change ((2 : ℝ)^J.card : ℂ) *
        ((g (fun i => triangleWave (x i)) : ℂ) *
          ∏ i ∈ Finset.univ \ J, (1 - (triangleWave (x i) : ℂ))) *
        (∏ i ∈ J, (-2 * Complex.I *
          (Real.sin (Real.pi * (k i : ℝ) * triangleWave (x i)) : ℂ))) =
      ((2 : ℝ)^J.card : ℂ) *
        ((∏ i, if k i = 0 then ((1-triangleWave (x i):ℝ):ℂ) else
          -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * triangleWave (x i)) : ℂ)) *
          (g (fun i => triangleWave (x i)) : ℂ))
    rw [hprodSplit (fun i => triangleWave (x i))]
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ac_rfl
  have hIntEq :
      (∫ x : UnitAddTorus (Fin d), F x *
        (∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i)))
        ∂(volume : Measure (UnitAddTorus (Fin d)))) =
      ((2 : ℝ)^J.card : ℂ) *
        ∫ v, ψ v ∂cubeMeasure d := by
    calc
      _ = ∫ x : UnitAddTorus (Fin d), ((2 : ℝ)^J.card : ℂ) * ψ (fold x)
          ∂(volume : Measure (UnitAddTorus (Fin d))) := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact hpoint x
      _ = ((2 : ℝ)^J.card : ℂ) *
          ∫ x : UnitAddTorus (Fin d), ψ (fold x)
            ∂(volume : Measure (UnitAddTorus (Fin d))) := by
            rw [integral_const_mul]
      _ = ((2 : ℝ)^J.card : ℂ) * ∫ v, ψ v ∂cubeMeasure d := by
            rw [hmap]
  have havg := anchoredFaceSource_fourierCoeff_average hp g k J hJ
  have hμ : (volume : Measure (UnitAddTorus (Fin d))) =
      Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) :=
    unitAddTorus_volume_eq_productHaar d
  have hcard : (J.powerset.card : ℂ) = (2 : ℂ)^J.card := by simp
  have hpow : ((2 : ℝ) : ℂ)^J.card = (2 : ℂ)^J.card := by norm_num
  have hpowne : (2 : ℂ)^J.card ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    UnitAddTorus.mFourierCoeff F k =
        ∫ x : UnitAddTorus (Fin d), F x * UnitAddTorus.mFourier (-k) x
          ∂(volume : Measure (UnitAddTorus (Fin d))) := by
            rw [UnitAddTorus.mFourierCoeff, hμ]
            simp only [smul_eq_mul]
            apply integral_congr_ae
            filter_upwards [] with x
            ring <;> rfl
    _ = (J.powerset.card : ℂ)⁻¹ *
          ∫ x : UnitAddTorus (Fin d), F x *
            (∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i)))
              ∂(volume : Measure (UnitAddTorus (Fin d))) := by
          simpa [F] using havg
    _ = (J.powerset.card : ℂ)⁻¹ *
          (((2 : ℝ)^J.card : ℂ) * ∫ v, ψ v ∂cubeMeasure d) := by
          rw [hIntEq]
    _ = ∫ v, ψ v ∂cubeMeasure d := by
          rw [hcard, hpow, ← mul_assoc, inv_mul_cancel₀ hpowne, one_mul]
    _ = ∫ v, (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ) else
          -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) *
          (g v : ℂ) ∂cubeMeasure d := by rfl

/-- The actual parity-source coefficient is the derivative multiplier of the
periodic anchored path coefficient on the exact frequency face. -/
theorem anchoredFaceSource_fourierCoeff_eq_derivativePath {d : ℕ} {p : ℝ}
    (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (k : Fin d → ℤ) (J : Finset (Fin d))
    (hJ : ∀ i, i ∈ J ↔ k i ≠ 0) :
    UnitAddTorus.mFourierCoeff
        (fun x : UnitAddTorus (Fin d) =>
          ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℝ) : ℂ)) k =
      (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) *
        UnitAddTorus.mFourierCoeff
          (fun x : UnitAddTorus (Fin d) =>
            ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) k := by
  calc
    _ = ∫ v, (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ) else
          -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) *
          (g v : ℂ) ∂cubeMeasure d :=
      anchoredFaceSource_fourierCoeff_eq_cube hp g k J hJ
    _ = _ := (periodicIntegrationPath_derivativeFourierCoeff_sine hp g k J hJ).symm

end BrownianSharp.AlignmentPaperAnchoredLpParityFourierCube
