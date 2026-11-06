import BrownianSharp.AlignmentPaperAnchoredLpGradeBudget
import BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity
import BrownianSharp.AlignmentPaperFaceGradeYoung
import BrownianSharp.AlignmentPaperProductGradeSquareFunctionLp
import BrownianSharp.AlignmentPaperFiniteKernelLpDensity
import BrownianSharp.AlignmentPaperAnchoredLpParityFourierCube
import BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension

/-! Actual-source adapters for the finite-grade anchored Lp budget. -/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpActualGradeBudget

open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLpParityFourier
open BrownianSharp.AlignmentPaperAnchoredLpParityFourierCube
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
open BrownianSharp.AlignmentPaperAnchoredLpFacePartition
open BrownianSharp.AlignmentPaperAnchoredLpGradeBudget
open BrownianSharp.AlignmentPaperAnchoredLpGradeBudget
open BrownianSharp.AlignmentPaperMultivariateFaceInverse
open BrownianSharp.AlignmentPaperProductSquareFunctionLp
open BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity
open BrownianSharp.AlignmentPaperFaceGradeYoung
open BrownianSharp.AlignmentPaperProductGradeSquareFunctionLp
open BrownianSharp.AlignmentPaperFiniteKernelLpDensity
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.SmoothResolution

local instance actualGradeTorusProbability (d : ℕ) :
    IsProbabilityMeasure
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  infer_instance

/-- The actual complex-valued parity source for a face. -/
def faceParitySource {d : ℕ} {p : ℝ} (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    UnitAddTorus (Fin d) → ℂ := fun x =>
  (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)

theorem faceParitySource_memLp {d : ℕ} {p : ℝ} (hp : 1 < p)
    (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    MemLp (faceParitySource J g) (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  rw [← BrownianSharp.unitAddTorus_volume_eq_productHaar d]
  exact memLp_complex_anchoredFaceSource hp J g

/-- Select the canonical Lp representative of the actual parity source. -/
noncomputable def faceParitySourceLp {d : ℕ} {p : ℝ} (hp : 1 < p)
    (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    Lp ℂ (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
  (faceParitySource_memLp hp J g).toLp
    (faceParitySource (p := p) J g)

theorem faceParitySourceLp_ae {d : ℕ} {p : ℝ} (hp : 1 < p)
    (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    (faceParitySourceLp hp J g : UnitAddTorus (Fin d) → ℂ) =ᵐ[
      Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)]
      faceParitySource (p := p) J g := by
  exact (faceParitySource_memLp hp J g).coeFn_toLp

/-- The canonical Lp representative retains the actual quantitative face-source
moment used in `sourceLpNorm`. -/
theorem faceParitySourceLp_moment {d : ℕ} {p : ℝ} (hp : 1 < p)
    (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    ∫ x : UnitAddTorus (Fin d), ‖faceParitySourceLp hp J g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      sourceLpNorm p J g ^ p := by
  have hae := faceParitySourceLp_ae hp J g
  have hraw : ∫ x : UnitAddTorus (Fin d),
      ‖faceParitySourceLp hp J g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      ∫ x : UnitAddTorus (Fin d),
        ‖(anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)‖ ^ p
        ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
    simp [faceParitySource, Complex.norm_real, Real.norm_eq_abs]
  have hμ : (volume : Measure (UnitAddTorus (Fin d))) =
      Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) :=
    BrownianSharp.unitAddTorus_volume_eq_productHaar d
  have hmeasureInt :
      ∫ x : UnitAddTorus (Fin d),
        ‖(anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)‖ ^ p
        ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
      ∫ x : UnitAddTorus (Fin d),
        ‖(anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)‖ ^ p
        ∂(volume : Measure (UnitAddTorus (Fin d))) := by
    exact congrArg (fun ν : Measure (UnitAddTorus (Fin d)) =>
      ∫ x : UnitAddTorus (Fin d),
        ‖(anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)‖ ^ p ∂ν) hμ.symm
  have hI : 0 ≤ ∫ x : UnitAddTorus (Fin d),
      ‖(anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)‖ ^ p
      ∂(volume : Measure (UnitAddTorus (Fin d))) :=
    integral_nonneg fun x => by positivity
  have hpow :
      ∫ x : UnitAddTorus (Fin d),
        ‖(anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ)‖ ^ p
        ∂(volume : Measure (UnitAddTorus (Fin d))) =
      sourceLpNorm p J g ^ p := by
    unfold sourceLpNorm
    symm
    simpa [one_div] using
      (Real.rpow_inv_rpow hI (ne_of_gt (lt_trans zero_lt_one hp)))
  exact hraw.trans (hmeasureInt.trans hpow)

/-- The actual parity source is integrable on product Haar. -/
theorem integrable_faceParitySource {d : ℕ} {p : ℝ} (hp : 1 < p)
    (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    Integrable (faceParitySource J g)
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  exact (faceParitySource_memLp hp J g).integrable (by
    simpa using ENNReal.ofReal_le_ofReal hp.le)

/-- The Fourier derivative relation required by the actual face inverse
reconstruction follows from the proved coefficient identity for every exact
support face. -/
theorem faceParitySource_fourier_derivativePath {d : ℕ} {p : ℝ}
    (hp : 1 < p) (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (J : Finset (Fin d)) (k : Fin d → ℤ)
    (hJ : frequencySupport k = J) :
    UnitAddTorus.mFourierCoeff (faceParitySource J g) k =
      (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) *
        UnitAddTorus.mFourierCoeff
          (fun x : UnitAddTorus (Fin d) =>
            ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) k := by
  have hsupport : ∀ i, i ∈ J ↔ k i ≠ 0 := by
    intro i
    have hmem := congrArg (fun A : Finset (Fin d) => i ∈ A) hJ
    simpa [frequencySupport] using hmem.symm
  exact anchoredFaceSource_fourierCoeff_eq_derivativePath hp g k J hsupport

/-- The frequency-side product kernel in the inverse leaf is exactly the
actual product smooth-resolution kernel used by the square-function theorem. -/
theorem faceSmoothBlockKernel_eq_actualProductKernel {d : ℕ} (s : Fin d → ℕ) :
    faceSmoothBlockKernel s = admissibleBlockKernel smoothResolutionCutoff s := by
  rw [faceSmoothBlockKernel, productSmoothBlockKernel_eq_coordinateProduct]
  rfl

theorem faceBlockSource_eq_actualProductBlock {d : ℕ} (s : Fin d → ℕ)
    (h : UnitAddTorus (Fin d) → ℂ) :
    faceBlockSource s h = productSmoothBlockConvolution s h := by
  funext x
  rw [faceBlockSource, productSmoothBlockConvolution,
    faceSmoothBlockKernel_eq_actualProductKernel]

/-- Replacing the actual parity-source function by its canonical Lp element
does not change any finite product smooth block. -/
theorem faceBlockSource_eq_lpelementProductBlock {d : ℕ} {p : ℝ}
    (hp : 1 < p) (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) (s : Fin d → ℕ) :
    faceBlockSource s (faceParitySource (p := p) J g) =
      productSmoothBlockConvolution s (faceParitySourceLp hp J g) := by
  funext x
  rw [faceBlockSource_eq_actualProductBlock,
    ← applyKernel_productBlockIntegralKernel]
  exact (applyKernel_congr_ae (productBlockIntegralKernel s)
    (faceParitySourceLp_ae hp J g) x).symm

theorem faceBlockSource_moment_eq_lpelementProductBlock {d : ℕ} {p : ℝ}
    (hp : 1 < p) (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) (s : Fin d → ℕ) :
    ∫ x : UnitAddTorus (Fin d),
      ‖faceBlockSource s (faceParitySource (p := p) J g) x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) =
    ∫ x : UnitAddTorus (Fin d),
      ‖productSmoothBlockConvolution s (faceParitySourceLp hp J g) x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  rw [faceBlockSource_eq_lpelementProductBlock hp J g s]

/-- Pointwise Lp bounds on every member of a finite family pass to its
`ell2(Lp)` grade energy with the same scalar constant. -/
theorem gradeLpEnergy_le_of_lpMomentRoot_le {X S : Type*} [MeasurableSpace X]
    [Fintype S] {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q)
    (μ : Measure X) (f h : S → X → ℂ)
    (hbound : ∀ s, (∫ x, ‖f s x‖ ^ p ∂μ) ^ (1 / p) ≤
      q * (∫ x, ‖h s x‖ ^ p ∂μ) ^ (1 / p)) :
    gradeLpEnergy p μ f ≤ q * gradeLpEnergy p μ h := by
  classical
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hMoment (u : S → X → ℂ) (s : S) :
      (∫ x, ‖u s x‖ ^ p ∂μ) ^ (2 / p) =
        ((∫ x, ‖u s x‖ ^ p ∂μ) ^ (1 / p)) ^ 2 := by
    have hI : 0 ≤ ∫ x, ‖u s x‖ ^ p ∂μ := integral_nonneg fun x => by positivity
    rw [show (2 / p : ℝ) = (1 / p) * 2 by field_simp, Real.rpow_mul hI]
    rw [← Real.rpow_natCast]
    rfl
  have hsum :
      (∑ s : S, (∫ x, ‖f s x‖ ^ p ∂μ) ^ (2 / p)) ≤
        q ^ 2 * (∑ s : S, (∫ x, ‖h s x‖ ^ p ∂μ) ^ (2 / p)) := by
    calc
      _ = ∑ s : S, ((∫ x, ‖f s x‖ ^ p ∂μ) ^ (1 / p)) ^ 2 := by
        simp_rw [hMoment]
      _ ≤ ∑ s : S, (q * (∫ x, ‖h s x‖ ^ p ∂μ) ^ (1 / p)) ^ 2 := by
        apply Finset.sum_le_sum
        intro s hs
        have hnonneg : 0 ≤ (∫ x, ‖f s x‖ ^ p ∂μ) ^ (1 / p) := by positivity
        have hbound' := hbound s
        have hright : 0 ≤ q * (∫ x, ‖h s x‖ ^ p ∂μ) ^ (1 / p) := by positivity
        nlinarith
      _ = q ^ 2 * (∑ s : S, (∫ x, ‖h s x‖ ^ p ∂μ) ^ (2 / p)) := by
        rw [Finset.mul_sum]
        congr 1
        ext s
        rw [mul_pow, hMoment]
  have hsumF : 0 ≤ ∑ s : S, (∫ x, ‖f s x‖ ^ p ∂μ) ^ (2 / p) := by
    apply Finset.sum_nonneg
    intro s hs
    positivity
  have hsumH : 0 ≤ ∑ s : S, (∫ x, ‖h s x‖ ^ p ∂μ) ^ (2 / p) := by
    apply Finset.sum_nonneg
    intro s hs
    positivity
  have hroot := Real.sqrt_le_sqrt hsum
  have hfactor : Real.sqrt (q ^ 2 *
      (∑ s : S, (∫ x, ‖h s x‖ ^ p ∂μ) ^ (2 / p))) =
      q * Real.sqrt (∑ s : S, (∫ x, ‖h s x‖ ^ p ∂μ) ^ (2 / p)) := by
    rw [Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq_eq_abs, abs_of_nonneg hq]
  unfold gradeLpEnergy
  calc
    _ = Real.sqrt (∑ s : S, (∫ x, ‖f s x‖ ^ p ∂μ) ^ (2 / p)) :=
      (Real.sqrt_eq_rpow _).symm
    _ ≤ Real.sqrt (q ^ 2 *
        (∑ s : S, (∫ x, ‖h s x‖ ^ p ∂μ) ^ (2 / p))) := hroot
    _ = q * Real.sqrt (∑ s : S, (∫ x, ‖h s x‖ ^ p ∂μ) ^ (2 / p)) := hfactor
    _ = _ := by rw [Real.sqrt_eq_rpow]

/-- The actual periodic fold has a face budget: the per-face inverse estimate
is fed the canonical Lp parity source, whose mixed grade cost is bounded by
the proved product signed-kernel square function. -/
theorem actual_face_contract_of_sourceSF {d n : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : p < 2)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (Cy : ℝ) (hCy : 1 ≤ Cy)
    (hfaceYoung : ∀ {d' n' : ℕ} (J : Finset (Fin d'))
      (s : Shape d' n') (F h : UnitAddTorus (Fin d') → ℂ)
      (hh : Integrable h (Measure.pi fun _ : Fin d' => AddCircle.haarAddCircle))
      (hderiv : ∀ k : Fin d' → ℤ, frequencySupport k = J →
        UnitAddTorus.mFourierCoeff h k =
          (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) *
            UnitAddTorus.mFourierCoeff F k),
      (∫ x : UnitAddTorus (Fin d'), ‖faceBlockTarget J s.1 F x‖ ^ p
        ∂(Measure.pi fun _ : Fin d' => AddCircle.haarAddCircle)) ^ (1 / p) ≤
        Cy ^ d' * (2:ℝ)^(-(n':ℝ)) *
          (∫ x : UnitAddTorus (Fin d'), ‖faceBlockSource s.1 h x‖ ^ p
            ∂(Measure.pi fun _ : Fin d' => AddCircle.haarAddCircle)) ^ (1 / p)) :
    ∀ J : Finset (Fin d),
      gradeLpEnergy p (volume : Measure (UnitAddTorus (Fin d)))
        (fun s : Shape d n => faceBlockTarget J s.1
          (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ))) ≤
        (Cy^d * (productGradeSquareConstant p)^(d/p)) *
          (2:ℝ)^(-(n:ℝ)) * sourceLpNorm p J g := by
  intro J
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  let F : UnitAddTorus (Fin d) → ℂ := fun x =>
    ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)
  let h : UnitAddTorus (Fin d) → ℂ := faceParitySource J g
  let hLp := faceParitySourceLp hp J g
  let q : ℝ := Cy^d * (2:ℝ)^(-(n:ℝ))
  have hh : Integrable h μ := by
    exact integrable_faceParitySource hp J g
  have hderiv : ∀ k : Fin d → ℤ, frequencySupport k = J →
      UnitAddTorus.mFourierCoeff h k =
        (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) *
          UnitAddTorus.mFourierCoeff F k := by
    intro k hk
    exact faceParitySource_fourier_derivativePath hp g J k hk
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 ≤ q := by positivity
  have hpoint : ∀ s : Shape d n,
      (∫ x : UnitAddTorus (Fin d), ‖faceBlockTarget J s.1 F x‖ ^ p ∂μ) ^ (1 / p) ≤
        q * (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p ∂μ) ^ (1 / p) := by
    intro s
    have hy := hfaceYoung J s F h hh hderiv
    simpa [μ, q, mul_assoc] using hy
  have henergy := gradeLpEnergy_le_of_lpMomentRoot_le hp0 hq μ
    (fun s : Shape d n => faceBlockTarget J s.1 F)
    (fun s : Shape d n => faceBlockSource s.1 h) hpoint
  have hsf := productSmoothGrade_mixedLp_le_of_memLp n d hp hp2 hLp
  have hsourceMom :
      ∫ x : UnitAddTorus (Fin d), ‖(hLp : UnitAddTorus (Fin d) → ℂ) x‖ ^ p ∂μ =
        sourceLpNorm p J g ^ p := by
    simpa [μ, hLp] using faceParitySourceLp_moment hp J g
  have hsourceTerms :
      (∑ s : Shape d n,
        (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p ∂μ) ^ (2/p)) =
      ∑ s : Shape d n,
        (∫ x : UnitAddTorus (Fin d),
          ‖productSmoothBlockConvolution (fun i => s.1 i)
            (hLp : UnitAddTorus (Fin d) → ℂ) x‖ ^ p ∂μ) ^ (2/p) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [faceBlockSource_moment_eq_lpelementProductBlock hp J g s.1]
  have hsf' :
      (∑ s : Shape d n,
        (∫ x : UnitAddTorus (Fin d),
          ‖productSmoothBlockConvolution (fun i => s.1 i)
            (hLp : UnitAddTorus (Fin d) → ℂ) x‖ ^ p ∂μ) ^ (2/p)) ^ (p/2) ≤
        (productGradeSquareConstant p)^d * sourceLpNorm p J g ^ p := by
    rw [hsourceMom] at hsf
    simpa [μ, hLp] using hsf
  have hsumSourceNonneg : 0 ≤ ∑ s : Shape d n,
      (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p ∂μ) ^ (2/p) := by
    apply Finset.sum_nonneg
    intro s hs
    positivity
  have hsumSourcePow :
      (∑ s : Shape d n,
        (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p ∂μ) ^ (2/p)) ^ (p/2) ≤
        (productGradeSquareConstant p)^d * sourceLpNorm p J g ^ p := by
    rw [hsourceTerms]
    exact hsf'
  have hsourceNormNonneg : 0 ≤ sourceLpNorm p J g := by
    unfold sourceLpNorm
    positivity
  have hKnonneg : 0 ≤ productGradeSquareConstant p := by
    have hweak := BrownianSharp.AlignmentPaperSignedKernelLp.uniformSignedKernelWeakConstant_nonneg
    have hpminus : 0 < p - 1 := by linarith
    have htwo : 0 < 2 - p := by linarith
    dsimp [productGradeSquareConstant]
    positivity
  have henergySource :
      gradeLpEnergy p μ (fun s : Shape d n => faceBlockSource s.1 h) ≤
        (productGradeSquareConstant p)^(d/p) * sourceLpNorm p J g := by
    let T : ℝ := ∑ s : Shape d n,
      (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p ∂μ) ^ (2/p)
    have hT : 0 ≤ T := by dsimp [T]; exact hsumSourceNonneg
    have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hT _)
      hsumSourcePow (by positivity : 0 ≤ 1/p)
    have hKpow :
        ((productGradeSquareConstant p)^d * sourceLpNorm p J g ^ p)^(1/p) =
          (productGradeSquareConstant p)^(d/p) * sourceLpNorm p J g := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hsourceNormNonneg _)]
      have hKroot : (productGradeSquareConstant p ^ d)^(1/p) =
          (productGradeSquareConstant p)^(d/p) := by
        rw [← Real.rpow_natCast]
        calc
          _ = (productGradeSquareConstant p)^((d:ℝ)*(1/p)) :=
            (Real.rpow_mul hKnonneg _ _).symm
          _ = _ := by congr 1 <;> push_cast <;> ring
      have hSroot : (sourceLpNorm p J g ^ p)^(1/p) = sourceLpNorm p J g := by
        simpa [one_div] using
          (Real.rpow_rpow_inv hsourceNormNonneg (ne_of_gt hp0))
      rw [hKroot, hSroot]
    have hTconvert : T^((1/2:ℝ)) = (T^(p/2))^(1/p) := by
      have hExp : (1/2:ℝ) = (p/2)*(1/p) := by field_simp
      calc
        _ = T^((p/2)*(1/p)) := congrArg (fun r : ℝ => T^r) hExp
        _ = _ := Real.rpow_mul hT _ _
    unfold gradeLpEnergy
    dsimp [T] at hroot ⊢
    calc
      _ = ((∑ s : Shape d n,
          (∫ x : UnitAddTorus (Fin d), ‖faceBlockSource s.1 h x‖ ^ p ∂μ) ^ (2/p)) ^ (p/2)) ^ (1/p) := by
            simpa [T] using hTconvert
      _ ≤ ((productGradeSquareConstant p)^d * sourceLpNorm p J g ^ p)^(1/p) := hroot
      _ = _ := hKpow
  have hfaceμ := calc
      gradeLpEnergy p μ (fun s : Shape d n => faceBlockTarget J s.1 F) ≤
          q * gradeLpEnergy p μ (fun s : Shape d n => faceBlockSource s.1 h) := henergy
      _ ≤ q * ((productGradeSquareConstant p)^(d/p) * sourceLpNorm p J g) :=
        mul_le_mul_of_nonneg_left henergySource hq
  have hμ : (volume : Measure (UnitAddTorus (Fin d))) = μ := by
    simpa [μ] using BrownianSharp.unitAddTorus_volume_eq_productHaar d
  rw [hμ]
  simpa [q, mul_assoc, mul_left_comm, mul_comm] using hfaceμ

/-- Uniform actual-source finite-grade cost in the anchored p<2 range. The
constant is selected from the face Young and product square-function bounds
before the input density and grade are quantified. -/
theorem exists_actualGradeLpCost_bound {d : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : p < 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d),
      ‖g‖ ≤ 1 → ∀ n : ℕ,
        (∑ s : Shape d n,
          (∫ x : UnitAddTorus (Fin d),
            ‖block s.1 (periodicFoldExtension (integrationPath p hp g)) x‖ ^ p
            ∂(volume : Measure (UnitAddTorus (Fin d)))) ^ (2/p)) ^ (p/2) ≤
          D * (2:ℝ)^(-(p*n)) := by
  obtain ⟨Cy, hCy, hYoung⟩ := exists_faceGradeYoung_Lp_bound
    (p := p) hp.le
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hweak := BrownianSharp.AlignmentPaperSignedKernelLp.uniformSignedKernelWeakConstant_nonneg
  have hpminus : 0 < p - 1 := by linarith
  have htwo : 0 < 2 - p := by linarith
  have hKpos : 0 < productGradeSquareConstant p := by
    dsimp [productGradeSquareConstant]
    positivity
  let Cface : ℝ := Cy^d * (productGradeSquareConstant p)^(d/p)
  have hCface : 0 ≤ Cface := by
    dsimp [Cface]
    positivity
  have hCfacePos : 0 < Cface := by
    dsimp [Cface]
    positivity
  let D : ℝ := (Cface * 4^d)^p
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro g hg n
  have hface := actual_face_contract_of_sourceSF (d := d) (n := n)
    hp hp2 g Cy hCy hYoung
  exact actualGradeLpCost_le_of_face_contract hp hp2 g hg Cface hCface hface

end BrownianSharp.AlignmentPaperAnchoredLpActualGradeBudget
