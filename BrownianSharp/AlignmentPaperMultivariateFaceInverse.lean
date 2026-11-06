import BrownianSharp.AlignmentPaperInverseDerivativeNeighborIdentity
import BrownianSharp.TensorBlockKernelLp
import BrownianSharp.TorusComplexYoung
import BrownianSharp.AlignmentPaperAnchoredLpFacePartition
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentPaperTorusTranslation
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Tactic

/-! Product inverse kernels for the exact nonzero-frequency face of a
multivariate anchored Fourier expansion. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperMultivariateFaceInverse

open BrownianSharp.AlignmentPaperInverseDerivativeNeighbor
open BrownianSharp.AlignmentPaperInverseDerivativeNeighborIdentity
open BrownianSharp
open BrownianSharp.ScalarKernelL1
open BrownianSharp.Torus

local instance faceInverseCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance faceInverseTorusMeasureSpace (d : ℕ) :
    MeasureSpace (UnitAddTorus (Fin d)) :=
  ⟨Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)⟩

local instance faceInverseCircleProbability : IsProbabilityMeasure
    (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- On active coordinates use the sum of neighboring inverse blocks. On
inactive coordinates use the constant kernel, which retains only frequency
zero. -/
def faceInverseCoordinateKernel {d : ℕ} (J : Finset (Fin d))
    (s : Fin d → ℕ) (i : Fin d) : C(UnitAddCircle, ℂ) :=
  if i ∈ J then neighborInverseKernel (s i) else 1

def faceInverseKernel {d : ℕ} (J : Finset (Fin d))
    (s : Fin d → ℕ) : C(UnitAddTorus (Fin d), ℂ) :=
  coordinateProductKernel (faceInverseCoordinateKernel J s)

def faceInverseCoordinateSupport {d : ℕ} (J : Finset (Fin d))
    (s : Fin d → ℕ) (i : Fin d) : Finset ℤ :=
  if i ∈ J then neighborFrequencyUnion (s i) else {0}

def faceInverseCoordinateSymbol {d : ℕ} (J : Finset (Fin d))
    (s : Fin d → ℕ) (i : Fin d) (n : ℤ) : ℂ :=
  if i ∈ J then
    ∑ j ∈ neighborScales (s i), BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1 n
  else if n = 0 then 1 else 0

def faceInverseFrequencyBox {d : ℕ} (J : Finset (Fin d))
    (s : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (faceInverseCoordinateSupport J s)

def faceInverseSymbol {d : ℕ} (J : Finset (Fin d))
    (s : Fin d → ℕ) (k : Fin d → ℤ) : ℂ :=
  ∏ i, faceInverseCoordinateSymbol J s i (k i)

theorem faceInverseSymbol_eq_zero_of_active_zero {d : ℕ}
    (J : Finset (Fin d)) (s : Fin d → ℕ) (k : Fin d → ℤ)
    (i : Fin d) (hi : i ∈ J) (hki : k i = 0) :
    faceInverseSymbol J s k = 0 := by
  unfold faceInverseSymbol
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [faceInverseCoordinateSymbol, hi, hki,
    BrownianSharp.ScalarHighFrequency.inverseMultiplier]

private theorem faceInverseBox_coordinates {d : ℕ}
    (J : Finset (Fin d)) (s : Fin d → ℕ) (k : Fin d → ℤ)
    (hk : k ∈ faceInverseFrequencyBox J s) :
    ∀ i, if i ∈ J then k i ∈ neighborFrequencyUnion (s i) else k i = 0 := by
  have hcoord : ∀ i, k i ∈ if i ∈ J then neighborFrequencyUnion (s i) else {0} := by
    simpa [faceInverseFrequencyBox, faceInverseCoordinateSupport,
      Fintype.mem_piFinset] using hk
  intro i
  by_cases hi : i ∈ J
  · simpa [hi] using hcoord i
  · simpa [hi] using hcoord i

/-- A product of scalar Fourier polynomials is the corresponding finite
multivariate Fourier polynomial on the product torus. -/
private theorem coordinateProductKernel_eq_torusFourierPolynomial {d : ℕ}
    (K : Fin d → C(UnitAddCircle, ℂ)) (S : Fin d → Finset ℤ)
    (c : Fin d → ℤ → ℂ)
    (hK : ∀ i, K i = polynomialKernel (S i) (c i)) :
    coordinateProductKernel K = torusFourierPolynomial (Fintype.piFinset S)
      (fun k => ∏ i, c i (k i)) := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [coordinateProductKernel, torusFourierPolynomial,
    ContinuousMap.coe_mk, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Finset.prod_mul_distrib]
  simp_rw [hK]
  simp only [polynomialKernel, ContinuousMap.coe_sum,
    ContinuousMap.smul_apply, smul_eq_mul]
  simp only [Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum (fun i : Fin d => S i)
    (fun i n => c i n * fourier n (x i))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.prod_mul_distrib]

private theorem mFourier_sub_mul {d : ℕ} (k : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x-y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  have hcoord : ∀ i : Fin d,
      fourier (k i) ((x-y) i) = fourier (k i) (x i) * fourier (-k i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

private theorem torusFourierPolynomial_convolution_expansion {d : ℕ}
    (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
    (x : UnitAddTorus (Fin d)) :
    (∫ y : UnitAddTorus (Fin d),
      BrownianSharp.Torus.torusFourierPolynomial S c (x-y) * f y
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∑ k ∈ S, c k * UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x := by
  classical
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
  have hμ : μ = (volume : Measure (UnitAddTorus (Fin d))) := by
    rfl
  have hpol : (BrownianSharp.Torus.torusFourierPolynomial S c :
      UnitAddTorus (Fin d) → ℂ) =
      ∑ k ∈ S, fun z : UnitAddTorus (Fin d) => c k * UnitAddTorus.mFourier k z := by
    funext z
    simp [BrownianSharp.Torus.torusFourierPolynomial, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have hterm (k : Fin d → ℤ) : Integrable
      (fun y : UnitAddTorus (Fin d) =>
        (c k * UnitAddTorus.mFourier k (x-y)) * f y) μ := by
    apply hf.bdd_mul (c := ‖c k‖) (by fun_prop)
    filter_upwards [] with y
    have hm : ‖UnitAddTorus.mFourier k (x-y)‖ ≤ 1 := by
      calc
        _ ≤ ‖UnitAddTorus.mFourier k‖ :=
          (UnitAddTorus.mFourier k).norm_coe_le_norm _
        _ = 1 := UnitAddTorus.mFourier_norm
    calc
      ‖c k * UnitAddTorus.mFourier k (x-y)‖ =
          ‖c k‖ * ‖UnitAddTorus.mFourier k (x-y)‖ := norm_mul _ _
      _ ≤ ‖c k‖ * 1 := by gcongr
      _ = ‖c k‖ := by ring
  rw [hpol]
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [integral_finsetSum S (fun k hk => hterm k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hchar (y : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k (x-y) =
        UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y :=
    mFourier_sub_mul k x y
  calc
    (∫ y : UnitAddTorus (Fin d),
        (c k * UnitAddTorus.mFourier k (x-y)) * f y ∂μ) =
      (c k * UnitAddTorus.mFourier k x) *
        ∫ y : UnitAddTorus (Fin d),
          UnitAddTorus.mFourier (-k) y * f y ∂μ := by
            rw [show (fun y : UnitAddTorus (Fin d) =>
                (c k * UnitAddTorus.mFourier k (x-y)) * f y) =
                fun y => (c k * UnitAddTorus.mFourier k x) *
                  (UnitAddTorus.mFourier (-k) y * f y) by
                  funext y
                  rw [hchar y]
                  ring]
            rw [integral_const_mul]
    _ = c k * UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x := by
          rw [hμ]
          have hcoeff :
              (∫ y : UnitAddTorus (Fin d),
                UnitAddTorus.mFourier (-k) y * f y
                  ∂(volume : Measure (UnitAddTorus (Fin d)))) =
                UnitAddTorus.mFourierCoeff f k := by
            rw [UnitAddTorus.mFourierCoeff]
            simp only [smul_eq_mul]
          rw [hcoeff]
          ring

private theorem faceInverseCoordinateKernel_polynomial {d : ℕ}
    (J : Finset (Fin d)) (s : Fin d → ℕ) (i : Fin d) :
    faceInverseCoordinateKernel J s i =
      polynomialKernel (faceInverseCoordinateSupport J s i)
        (faceInverseCoordinateSymbol J s i) := by
  by_cases hi : i ∈ J
  · rw [faceInverseCoordinateKernel, if_pos hi]
    rw [faceInverseCoordinateSupport, if_pos hi]
    have hsymbol : faceInverseCoordinateSymbol J s i =
        fun n => ∑ j ∈ neighborScales (s i),
          BrownianSharp.ScalarHighFrequency.inverseMultiplier j 1 n := by
      funext n
      simp [faceInverseCoordinateSymbol, hi]
    rw [hsymbol]
    exact neighborInverseKernel_eq_polynomialKernel (s i)
  · apply ContinuousMap.ext
    intro x
    simp [faceInverseCoordinateKernel, faceInverseCoordinateSupport,
      faceInverseCoordinateSymbol, hi, polynomialKernel, fourier_zero]

theorem faceInverseKernel_eq_torusFourierPolynomial {d : ℕ}
    (J : Finset (Fin d)) (s : Fin d → ℕ) :
    faceInverseKernel J s =
      BrownianSharp.Torus.torusFourierPolynomial (faceInverseFrequencyBox J s)
        (faceInverseSymbol J s) := by
  exact coordinateProductKernel_eq_torusFourierPolynomial
    (faceInverseCoordinateKernel J s) (faceInverseCoordinateSupport J s)
    (faceInverseCoordinateSymbol J s)
    (faceInverseCoordinateKernel_polynomial J s)

def faceSmoothBlockCoordinateKernel {d : ℕ} (s : Fin d → ℕ) (i : Fin d) :
    C(UnitAddCircle, ℂ) :=
  BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel
    BrownianSharp.AlignmentPeriodicAdmissibleCutoff.smoothResolutionCutoff (s i)

def faceSmoothBlockKernel {d : ℕ} (s : Fin d → ℕ) :
    C(UnitAddTorus (Fin d), ℂ) :=
  coordinateProductKernel (faceSmoothBlockCoordinateKernel s)

def faceBlockFrequencyBox {d : ℕ} (s : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun i => neighborFrequencyUnion (s i))

theorem faceBlockFrequencyBox_filter_frequencySupport_eq_faceInverseFrequencyBox
    {d : ℕ} (J : Finset (Fin d)) (s : Fin d → ℕ) :
    (faceBlockFrequencyBox s).filter
        (fun k => BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k = J) =
      (faceInverseFrequencyBox J s).filter
        (fun k => BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k = J) := by
  classical
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hkbox, hsupport⟩
    refine ⟨?_, hsupport⟩
    have hkbox' : ∀ i, k i ∈ neighborFrequencyUnion (s i) := by
      simpa [faceBlockFrequencyBox, Fintype.mem_piFinset] using hkbox
    change k ∈ Fintype.piFinset (faceInverseCoordinateSupport J s)
    simp only [Fintype.mem_piFinset]
    intro i
    by_cases hi : i ∈ J
    · simpa [faceInverseCoordinateSupport, hi] using hkbox' i
    · have hzero : k i = 0 := by
        by_contra hne
        have hmem : i ∈ BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k := by
          simp [BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport, hne]
        rw [hsupport] at hmem
        exact hi hmem
      simpa [faceInverseCoordinateSupport, hi, hzero]
  · rintro ⟨hkbox, hsupport⟩
    refine ⟨?_, hsupport⟩
    have hkbox' : ∀ i, k i ∈ faceInverseCoordinateSupport J s i := by
      simpa [faceInverseFrequencyBox, Fintype.mem_piFinset] using hkbox
    change k ∈ Fintype.piFinset (fun i => neighborFrequencyUnion (s i))
    simp only [Fintype.mem_piFinset]
    intro i
    by_cases hi : i ∈ J
    · have hki := hkbox' i
      simpa [faceInverseCoordinateSupport, hi] using hki
    · have hzero : k i = 0 := by
        by_contra hne
        have hmem : i ∈ BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k := by
          simp [BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport, hne]
        rw [hsupport] at hmem
        exact hi hmem
      have hscale : s i ∈ neighborScales (s i) := by simp [neighborScales]
      have hzeroBox : (0 : ℤ) ∈ BrownianSharp.ScalarAtomVariance.scalarFrequencyBox (s i) := by
        simp [BrownianSharp.ScalarAtomVariance.scalarFrequencyBox]
      have hzeroUnion : (0 : ℤ) ∈ neighborFrequencyUnion (s i) :=
        Finset.mem_biUnion.mpr ⟨s i, hscale, hzeroBox⟩
      simpa [hzero] using hzeroUnion

def faceBlockSymbol {d : ℕ} (s : Fin d → ℕ) (k : Fin d → ℤ) : ℂ :=
  ∏ i, (BrownianSharp.SmoothResolution.scalarBlock (s i) (k i : ℝ) : ℂ)

private theorem faceSmoothBlockCoordinateKernel_polynomial {d : ℕ}
    (s : Fin d → ℕ) (i : Fin d) :
    faceSmoothBlockCoordinateKernel s i =
      polynomialKernel (neighborFrequencyUnion (s i))
        (fun n => (BrownianSharp.SmoothResolution.scalarBlock (s i) (n:ℝ) : ℂ)) := by
  exact smoothBlockKernel_eq_polynomialKernel_union (s i)

theorem faceSmoothBlockKernel_eq_torusFourierPolynomial {d : ℕ}
    (s : Fin d → ℕ) :
    faceSmoothBlockKernel s =
      BrownianSharp.Torus.torusFourierPolynomial (faceBlockFrequencyBox s)
        (faceBlockSymbol s) := by
  exact coordinateProductKernel_eq_torusFourierPolynomial
    (faceSmoothBlockCoordinateKernel s) (fun i => neighborFrequencyUnion (s i))
    (fun i n => (BrownianSharp.SmoothResolution.scalarBlock (s i) (n:ℝ) : ℂ))
    (faceSmoothBlockCoordinateKernel_polynomial s)

def faceBlockSource {d : ℕ} (s : Fin d → ℕ)
    (h : UnitAddTorus (Fin d) → ℂ) : UnitAddTorus (Fin d) → ℂ :=
  fun x => ∫ y : UnitAddTorus (Fin d),
    faceSmoothBlockKernel s (x-y) * h y
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)

def faceBlockTarget {d : ℕ} (J : Finset (Fin d)) (s : Fin d → ℕ)
    (F : UnitAddTorus (Fin d) → ℂ) : C(UnitAddTorus (Fin d), ℂ) :=
  BrownianSharp.AlignmentPaperAnchoredLpFacePartition.supportFacePolynomial
    (faceBlockFrequencyBox s)
    (fun k => faceBlockSymbol s k * UnitAddTorus.mFourierCoeff F k) J

theorem faceBlockTarget_eq_zero_of_inactive_positive_grade {d : ℕ}
    (J : Finset (Fin d)) (s : Fin d → ℕ)
    (F : UnitAddTorus (Fin d) → ℂ) (i : Fin d)
    (hi : i ∉ J) (hs : 0 < s i) : faceBlockTarget J s F = 0 := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [faceBlockTarget,
    BrownianSharp.AlignmentPaperAnchoredLpFacePartition.supportFacePolynomial,
    BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hsupp := (Finset.mem_filter.mp hk).2
  have hki : k i = 0 := by
    by_contra hne
    have himem : i ∈ BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k := by
      simp [BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport, hne]
    rw [hsupp] at himem
    exact hi himem
  have hblock : BrownianSharp.SmoothResolution.scalarBlock (s i) 0 = 0 := by
    rw [BrownianSharp.SmoothResolution.scalarBlock, if_neg (by omega)]
    have hz : BrownianSharp.SmoothResolution.cutoff 0 = 1 := by
      exact BrownianSharp.SmoothResolution.cutoff_eq_one (by norm_num)
    simp [hz]
  have hsymbol : faceBlockSymbol s k = 0 := by
    unfold faceBlockSymbol
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hki, hblock]
  simp [hsymbol]

theorem sum_faceBlockTarget_eq_torusFourierPolynomial {d : ℕ}
    (s : Fin d → ℕ) (F : UnitAddTorus (Fin d) → ℂ) :
    (∑ J ∈ (Finset.univ : Finset (Fin d)).powerset, faceBlockTarget J s F) =
      BrownianSharp.Torus.torusFourierPolynomial (faceBlockFrequencyBox s)
        (fun k => faceBlockSymbol s k * UnitAddTorus.mFourierCoeff F k) := by
  simpa [faceBlockTarget] using
    BrownianSharp.AlignmentPaperAnchoredLpFacePartition.sum_supportFacePolynomial_eq_torusFourierPolynomial
      (faceBlockFrequencyBox s)
      (fun k => faceBlockSymbol s k * UnitAddTorus.mFourierCoeff F k)

theorem faceBlockSource_eq_torusFourierPolynomial {d : ℕ}
    (s : Fin d → ℕ) {h : UnitAddTorus (Fin d) → ℂ}
    (hh : Integrable h (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) :
    faceBlockSource s h =
      fun x => BrownianSharp.Torus.torusFourierPolynomial (faceBlockFrequencyBox s)
        (fun k => faceBlockSymbol s k * UnitAddTorus.mFourierCoeff h k) x := by
  funext x
  rw [faceBlockSource]
  calc
    (∫ y : UnitAddTorus (Fin d), faceSmoothBlockKernel s (x-y) * h y
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∫ y : UnitAddTorus (Fin d),
        BrownianSharp.Torus.torusFourierPolynomial (faceBlockFrequencyBox s)
          (faceBlockSymbol s) (x-y) * h y
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
          apply integral_congr_ae
          filter_upwards [] with y
          exact congrArg (fun z : ℂ => z * h y)
            (congrArg (fun K : C(UnitAddTorus (Fin d), ℂ) => K (x-y))
              (faceSmoothBlockKernel_eq_torusFourierPolynomial s))
    _ = ∑ k ∈ faceBlockFrequencyBox s,
        faceBlockSymbol s k * UnitAddTorus.mFourierCoeff h k *
          UnitAddTorus.mFourier k x :=
            torusFourierPolynomial_convolution_expansion _ _ h hh x
    _ = BrownianSharp.Torus.torusFourierPolynomial (faceBlockFrequencyBox s)
        (fun k => faceBlockSymbol s k * UnitAddTorus.mFourierCoeff h k) x := by
          simp [BrownianSharp.Torus.torusFourierPolynomial,
            ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]

theorem faceBlockSource_fourierCoeff {d : ℕ}
    (s : Fin d → ℕ) {h : UnitAddTorus (Fin d) → ℂ}
    (hh : Integrable h (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
    (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (faceBlockSource s h) k =
      if k ∈ faceBlockFrequencyBox s then
        faceBlockSymbol s k * UnitAddTorus.mFourierCoeff h k else 0 := by
  rw [faceBlockSource_eq_torusFourierPolynomial s hh]
  rw [BrownianSharp.AlignmentPeriodicFourierReconstruction.fourierPolynomial_coefficient]

private theorem faceInverse_symbol_reconstructs_on_exact_support {d : ℕ}
    (J : Finset (Fin d)) (s : Fin d → ℕ) (k : Fin d → ℤ)
    (hsupp : BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k = J) :
    faceInverseSymbol J s k * faceBlockSymbol s k *
        (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) =
      faceBlockSymbol s k := by
  classical
  have hprodD :
      (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) =
        ∏ i : Fin d, if i ∈ J then
          (2 * Real.pi * Complex.I * (k i : ℂ)) else 1 := by
    simp [Finset.prod_ite_mem]
  have hcoord (i : Fin d) :
      faceInverseCoordinateSymbol J s i (k i) *
        (BrownianSharp.SmoothResolution.scalarBlock (s i) (k i : ℝ) : ℂ) *
        (if i ∈ J then (2 * Real.pi * Complex.I * (k i : ℂ)) else 1) =
      (BrownianSharp.SmoothResolution.scalarBlock (s i) (k i : ℝ) : ℂ) := by
    by_cases hi : i ∈ J
    · have hki : k i ≠ 0 := by
        have hmem : i ∈ BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k := by
          rw [hsupp]
          exact hi
        simpa [BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport] using hmem
      have hm := inverseNeighbor_multiplier_reconstructs_block (s i) (k i) 1
        (by intro hzero; exact False.elim (hki hzero))
      simpa [faceInverseCoordinateSymbol, hi, hki, mul_assoc] using hm
    · have hki : k i = 0 := by
        by_contra hne
        have hmem : i ∈ BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k := by
          simp [BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport, hne]
        rw [hsupp] at hmem
        exact hi hmem
      simp [faceInverseCoordinateSymbol, hi, hki,
        BrownianSharp.ScalarHighFrequency.inverseMultiplier]
  calc
    _ = ∏ i : Fin d,
        faceInverseCoordinateSymbol J s i (k i) *
          (BrownianSharp.SmoothResolution.scalarBlock (s i) (k i : ℝ) : ℂ) *
          (if i ∈ J then (2 * Real.pi * Complex.I * (k i : ℂ)) else 1) := by
            have hmulprod :
                (∏ i : Fin d, faceInverseCoordinateSymbol J s i (k i)) *
                  (∏ i : Fin d, (BrownianSharp.SmoothResolution.scalarBlock
                    (s i) (k i : ℝ) : ℂ)) *
                  (∏ i : Fin d, if i ∈ J then
                    (2 * Real.pi * Complex.I * (k i : ℂ)) else 1) =
                ∏ i : Fin d, faceInverseCoordinateSymbol J s i (k i) *
                  (BrownianSharp.SmoothResolution.scalarBlock
                    (s i) (k i : ℝ) : ℂ) *
                  (if i ∈ J then (2 * Real.pi * Complex.I * (k i : ℂ)) else 1) := by
              rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            change (∏ i : Fin d, faceInverseCoordinateSymbol J s i (k i)) *
                (∏ i : Fin d, (BrownianSharp.SmoothResolution.scalarBlock
                  (s i) (k i : ℝ) : ℂ)) *
                (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) = _
            rw [hprodD]
            exact hmulprod
    _ = ∏ i : Fin d,
        (BrownianSharp.SmoothResolution.scalarBlock (s i) (k i : ℝ) : ℂ) :=
          Finset.prod_congr rfl (fun i _ => hcoord i)
    _ = faceBlockSymbol s k := rfl

private theorem faceBlockSource_integrable {d : ℕ}
    (s : Fin d → ℕ) {h : UnitAddTorus (Fin d) → ℂ}
    (hh : Integrable h (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) :
    Integrable (faceBlockSource s h)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  rw [faceBlockSource_eq_torusFourierPolynomial s hh]
  exact (BrownianSharp.Torus.torusFourierPolynomial (faceBlockFrequencyBox s)
    (fun k => faceBlockSymbol s k * UnitAddTorus.mFourierCoeff h k)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

private theorem torusFourierPolynomial_reflectedConvolution_expansion {d : ℕ}
    (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
    (x : UnitAddTorus (Fin d)) :
    (∫ y : UnitAddTorus (Fin d),
      BrownianSharp.Torus.torusFourierPolynomial S c y * f (x-y)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∑ k ∈ S, c k * UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x := by
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)
  letI hmp := BrownianSharp.AlignmentPaperTorusTranslation.sub_left_measurePreserving
    (d := d) x
  let e : Homeomorph (UnitAddTorus (Fin d)) (UnitAddTorus (Fin d)) :=
    { toFun := fun y => x-y
      invFun := fun y => x-y
      left_inv := by intro y; simp [sub_sub_cancel]
      right_inv := by intro y; simp [sub_sub_cancel]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hchange (g : UnitAddTorus (Fin d) → ℂ) :
      (∫ y : UnitAddTorus (Fin d), g (x-y) ∂μ) = ∫ y, g y ∂μ := by
    simpa [e, μ, BrownianSharp.AlignmentPaperTorusTranslation.torusMeasure] using
      hmp.integral_comp e.measurableEmbedding g
  calc
    _ = ∫ z : UnitAddTorus (Fin d),
        BrownianSharp.Torus.torusFourierPolynomial S c (x-z) * f z
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            simpa [sub_sub_cancel] using hchange
              (fun z : UnitAddTorus (Fin d) =>
                BrownianSharp.Torus.torusFourierPolynomial S c (x-z) * f z)
    _ = ∑ k ∈ S, c k * UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x :=
      torusFourierPolynomial_convolution_expansion S c f hf x

theorem faceInverse_reconstructs_actual_faceBlock {d : ℕ}
    (J : Finset (Fin d)) (s : Fin d → ℕ)
    {F h : UnitAddTorus (Fin d) → ℂ}
    (hh : Integrable h (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
    (hderiv : ∀ k : Fin d → ℤ,
      BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k = J →
        UnitAddTorus.mFourierCoeff h k =
          (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) *
            UnitAddTorus.mFourierCoeff F k) :
    ∀ x : UnitAddTorus (Fin d),
      (∫ y : UnitAddTorus (Fin d),
        faceInverseKernel J s y * faceBlockSource s h (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
        faceBlockTarget J s F x := by
  classical
  intro x
  let support : (Fin d → ℤ) → Finset (Fin d) :=
    BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport
  let S := faceInverseFrequencyBox J s
  have hsourceInt := faceBlockSource_integrable s hh
  have hkernelExpansion :
      (∫ y : UnitAddTorus (Fin d),
        faceInverseKernel J s y * faceBlockSource s h (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
        ∑ k ∈ S,
          faceInverseSymbol J s k * UnitAddTorus.mFourierCoeff (faceBlockSource s h) k *
            UnitAddTorus.mFourier k x := by
    calc
      _ = ∫ y : UnitAddTorus (Fin d),
          BrownianSharp.Torus.torusFourierPolynomial S (faceInverseSymbol J s) y *
            faceBlockSource s h (x-y)
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
              apply integral_congr_ae
              filter_upwards [] with y
              exact congrArg (fun K : C(UnitAddTorus (Fin d), ℂ) =>
                K y * faceBlockSource s h (x-y)) (faceInverseKernel_eq_torusFourierPolynomial J s)
      _ = _ := torusFourierPolynomial_reflectedConvolution_expansion
        S (faceInverseSymbol J s) (faceBlockSource s h) hsourceInt x
  rw [hkernelExpansion]
  simp only [faceBlockTarget,
    BrownianSharp.AlignmentPaperAnchoredLpFacePartition.supportFacePolynomial,
    BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply]
  rw [faceBlockFrequencyBox_filter_frequencySupport_eq_faceInverseFrequencyBox J s]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hs : support k = J
  · have htargetMem : k ∈ (faceBlockFrequencyBox s).filter (fun k => support k = J) := by
      rw [faceBlockFrequencyBox_filter_frequencySupport_eq_faceInverseFrequencyBox J s]
      exact Finset.mem_filter.mpr ⟨hk, hs⟩
    have hblockMem : k ∈ faceBlockFrequencyBox s :=
      (Finset.mem_filter.mp htargetMem).1
    rw [faceBlockSource_fourierCoeff s hh k]
    simp only [hblockMem, ↓reduceIte]
    rw [hderiv k hs]
    have hmult := faceInverse_symbol_reconstructs_on_exact_support J s k hs
    calc
      _ = (faceInverseSymbol J s k * faceBlockSymbol s k *
            (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ)))) *
            (UnitAddTorus.mFourierCoeff F k * UnitAddTorus.mFourier k x) := by ring
      _ = faceBlockSymbol s k *
            (UnitAddTorus.mFourierCoeff F k * UnitAddTorus.mFourier k x) := by
              rw [hmult]
      _ = if BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k = J then
            faceBlockSymbol s k * UnitAddTorus.mFourierCoeff F k * UnitAddTorus.mFourier k x else 0 := by
              have hs' : BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport k = J := by
                simpa [support] using hs
              rw [if_pos hs']
              ring
  · have hsubset : support k ⊆ J := by
      intro i hi
      have hki : k i ≠ 0 := by
        simpa [support, BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport] using hi
      have hcoord := faceInverseBox_coordinates J s k hk i
      by_cases hJ : i ∈ J
      · exact hJ
      · have hzero : k i = 0 := by simpa [hJ] using hcoord
        exact (hki hzero).elim
    have hmissing : ∃ i ∈ J, i ∉ support k := by
      by_contra hnone
      push_neg at hnone
      have hJsubset : J ⊆ support k := by
        intro i hi
        exact hnone i hi
      exact hs (Finset.Subset.antisymm hsubset hJsubset)
    obtain ⟨i, hiJ, hinot⟩ := hmissing
    have hzero : k i = 0 := by
      by_contra hne
      have himem : i ∈ support k := by
        simp [support, BrownianSharp.AlignmentPaperAnchoredLpFacePartition.frequencySupport, hne]
      exact hinot himem
    rw [faceInverseSymbol_eq_zero_of_active_zero J s k i hiJ hzero]
    simp [support, hs]

/-- The product inverse kernel has its actual coordinatewise L1 budget. The
constant is chosen before the face, dimension, and scale vector. -/
theorem exists_faceInverseKernel_L1_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {d : ℕ} (J : Finset (Fin d)) (s : Fin d → ℕ),
      (∫ x : UnitAddTorus (Fin d), ‖faceInverseKernel J s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
        C ^ d * ∏ i ∈ J, ((2:ℝ)^(s i))⁻¹ := by
  obtain ⟨C₀, hC₀, hneighbor⟩ :=
    BrownianSharp.AlignmentPaperInverseDerivativeNeighbor.exists_neighborInverseKernel_L1_bound
  let C : ℝ := max 1 C₀
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀ ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro d J s
  let B : Fin d → ℝ := fun i => C * if i ∈ J then ((2:ℝ)^(s i))⁻¹ else 1
  have hB : ∀ i, 0 ≤ B i := by
    intro i
    dsimp [B]
    split_ifs <;> positivity
  have hcoord : ∀ i,
      (∫ y : UnitAddCircle,
        ‖faceInverseCoordinateKernel J s i y‖ ∂AddCircle.haarAddCircle) ≤ B i := by
    intro i
    by_cases hi : i ∈ J
    · simp [faceInverseCoordinateKernel, hi, B]
      calc
        (∫ y : UnitAddCircle, ‖neighborInverseKernel (s i) y‖
            ∂AddCircle.haarAddCircle) ≤ C₀ * ((2:ℝ)^(s i))⁻¹ := hneighbor (s i)
        _ ≤ C * ((2:ℝ)^(s i))⁻¹ := by
          exact mul_le_mul_of_nonneg_right hC₀C (by positivity)
    · simp [faceInverseCoordinateKernel, hi, B]
      exact hC
  have hprod := coordinateProductKernel_norm_integral_le
    (faceInverseCoordinateKernel J s) B hB hcoord
  refine hprod.trans ?_
  dsimp [B]
  rw [Finset.prod_mul_distrib]
  have hCprod : (∏ i : Fin d, C) = C ^ d := by simp
  rw [hCprod]
  simp [Finset.prod_ite_mem]

end BrownianSharp.AlignmentPaperMultivariateFaceInverse

end
