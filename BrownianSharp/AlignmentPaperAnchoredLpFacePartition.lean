import BrownianSharp.AlignmentPaperAnchoredLpParityFourierCube
import BrownianSharp.AlignmentMaternComplexWindow

noncomputable section
open MeasureTheory
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
open BrownianSharp.AlignmentPaperAnchoredLpParityFourier
open BrownianSharp.AlignmentFractionalTensor
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
open BrownianSharp.AlignmentPaperAnchoredLpSourceFourier
open HaarQuarter
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpFacePartition

/-- The coordinate support of an integer frequency. -/
def frequencySupport {d : ℕ} (k : Fin d → ℤ) : Finset (Fin d) :=
  Finset.univ.filter fun i => k i ≠ 0

/-- Any finite Fourier sum splits exactly into its coordinate-support faces.
The identity applies directly to the coefficient sum of each smooth block. -/
theorem finite_sum_eq_sum_support_faces {d : ℕ}
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ) :
    (∑ k ∈ S, a k) =
      ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ k ∈ S.filter (fun k => frequencySupport k = J), a k := by
  classical
  let support : (Fin d → ℤ) → Finset (Fin d) := frequencySupport
  have hmaps : ∀ k ∈ S, support k ∈ (Finset.univ : Finset (Fin d)).powerset := by
    intro k hk
    exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hdecomp := (Finset.sum_fiberwise_of_maps_to hmaps a).symm
  simpa [support, frequencySupport, Finset.sum_filter] using hdecomp

/-- The finite Fourier polynomial carried by one exact coordinate-support face. -/
def supportFacePolynomial {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) (J : Finset (Fin d)) :
    C(UnitAddTorus (Fin d), ℂ) :=
  BrownianSharp.Torus.torusFourierPolynomial
    (S.filter fun k => frequencySupport k = J) a

/-- Summing the exact-support face polynomials recovers the full finite Fourier
polynomial. In particular, this applies to every actual smooth-resolution
block, with its own frequency box and multiplier coefficients. -/
theorem sum_supportFacePolynomial_eq_torusFourierPolynomial {d : ℕ}
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ) :
    (∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
      supportFacePolynomial S a J) =
      BrownianSharp.Torus.torusFourierPolynomial S a := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [supportFacePolynomial,
    BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply,
    ContinuousMap.coe_sum, Finset.sum_apply]
  have hsplit := finite_sum_eq_sum_support_faces S
    (fun k => a k * UnitAddTorus.mFourier k x)
  exact hsplit.symm

/-- Complexifying the parity source preserves its exact Lp cost, so the real
source bound applies directly to the complex convolution/SF operators. -/
theorem complex_anchoredFaceSource_eLpNorm_le {d : ℕ} {p : ℝ}
    (hp : 1 < p) (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    eLpNorm (fun x : UnitAddTorus (Fin d) =>
      (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ))
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) ≤
      ENNReal.ofReal ((2:ℝ)^J.card) *
        eLpNorm (g : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) (cubeMeasure d) := by
  let fold : UnitAddTorus (Fin d) → (Fin d → ℝ) :=
    fun x i => triangleWave (x i)
  let sign : UnitAddTorus (Fin d) → ℝ := fun x =>
    ∏ i ∈ J, anchoredFaceSignCoordinate x i
  let wt : UnitAddTorus (Fin d) → ℝ := fun x =>
    ∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i))
  let c : ℝ := (2:ℝ)^J.card
  have hsign : Measurable sign := by
    classical
    dsimp [sign]
    apply Finset.measurable_prod
    intro i hi
    exact measurable_anchoredFaceSignCoordinate i
  have hwt : Measurable wt := by
    simpa [wt] using measurable_anchoredFaceWeight J
  have hfold : MeasurePreserving fold (volume : Measure (UnitAddTorus (Fin d)))
      (cubeMeasure d) := by
    simpa [fold, cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi,
      unitIntervalMeasure] using measurePreserving_foldCoordinates d
  have hgcomp : AEStronglyMeasurable
      ((g : (Fin d → ℝ) → ℝ) ∘ fold) (volume : Measure (UnitAddTorus (Fin d))) :=
    (Lp.stronglyMeasurable g).aestronglyMeasurable.comp_measurePreserving hfold
  have hreal : AEStronglyMeasurable
      (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    have hrepr : anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) =
        fun x => c * sign x * (((g : (Fin d → ℝ) → ℝ) (fold x)) * wt x) := by
      funext x
      simp [anchoredFaceSource, sign, wt, c, fold]
    rw [hrepr]
    have hmul := (measurable_const : Measurable
      (fun _ : UnitAddTorus (Fin d) => c)).aestronglyMeasurable.mul
        (hsign.aestronglyMeasurable.mul (hgcomp.mul hwt.aestronglyMeasurable))
    convert hmul using 1
    ext x
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  have hcomplex : AEStronglyMeasurable
      (fun x : UnitAddTorus (Fin d) =>
        (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) :=
    (integrable_anchoredFaceSource hp J g).aestronglyMeasurable
  have hnorm := eLpNorm_congr_norm_ae (p := ENNReal.ofReal p) hcomplex hreal
    (ae_of_all _ fun x => by simp)
  rw [hnorm]
  exact anchoredFaceSource_eLpNorm_le J g

/-- The complex parity source is a genuine Lp convolution input for every
finite exponent greater than one. -/
theorem memLp_complex_anchoredFaceSource {d : ℕ} {p : ℝ}
    (hp : 1 < p) (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    MemLp (fun x : UnitAddTorus (Fin d) =>
      (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℂ))
      (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := by
  have hbound := complex_anchoredFaceSource_eLpNorm_le hp J g
  apply (hbound.trans_lt ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp g).eLpNorm_lt_top

/-- Summing the individual parity-source costs over all faces contributes only
a dimension-dependent constant. -/
theorem sum_faceParityCosts_le_four_pow (d : ℕ) :
    (∑ J ∈ (Finset.univ : Finset (Fin d)).powerset,
      (2 : ℝ)^J.card) ≤ 4^d := by
  classical
  calc
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin d)).powerset, (2 : ℝ)^d := by
      apply Finset.sum_le_sum
      intro J hJ
      have hcard : J.card ≤ d := by
        simpa using Finset.card_le_card (Finset.subset_univ J)
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hcard
    _ = (2:ℝ)^d * ((Finset.univ : Finset (Fin d)).powerset.card : ℝ) := by
      simp [Finset.sum_const]
    _ = 4^d := by
      simp [Finset.card_powerset]
      rw [← mul_pow]
      norm_num

end BrownianSharp.AlignmentPaperAnchoredLpFacePartition
