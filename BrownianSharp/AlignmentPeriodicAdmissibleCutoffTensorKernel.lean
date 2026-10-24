import BrownianSharp.AlignmentPeriodicAdmissibleCutoff
import BrownianSharp.TensorBlockKernelLp

noncomputable section
open MeasureTheory
open scoped BigOperators
open UnitAddTorus

namespace BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel

open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.ScalarAtomVariance
open BrownianSharp.ScalarKernelL1
open BrownianSharp.Torus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance (d : ℕ) : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin d))) := by
  change IsProbabilityMeasure
    (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  infer_instance

def admissibleBlockSymbol {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) (k : Fin d → ℤ) : ℂ :=
  ∏ i, (scalarBlock φ (s i) (k i : ℝ) : ℂ)

def admissibleBlockKernel {d : ℕ} (φ : AdmissibleCutoff) (s : Fin d → ℕ) :
    C(UnitAddTorus (Fin d), ℂ) :=
  torusFourierPolynomial (SmoothResolution.frequencyBox s)
    (admissibleBlockSymbol φ s)

def admissibleBlockKernelProduct {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) : C(UnitAddTorus (Fin d), ℂ) :=
  BrownianSharp.coordinateProductKernel
    (fun i => BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel φ (s i))

theorem admissibleBlockKernel_eq_product {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) : admissibleBlockKernel φ s = admissibleBlockKernelProduct φ s := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [admissibleBlockKernel, admissibleBlockKernelProduct,
    BrownianSharp.coordinateProductKernel, ContinuousMap.coe_mk,
    BrownianSharp.Torus.torusFourierPolynomial, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul,
    BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel,
    ScalarKernelL1.polynomialKernel]
  simp only [SmoothResolution.frequencyBox]
  have hterm (k : Fin d → ℤ) :
      admissibleBlockSymbol φ s k * UnitAddTorus.mFourier k x =
        ∏ i : Fin d,
          ((scalarBlock φ (s i) (k i : ℝ) : ℂ) *
            fourier (k i) (x i)) := by
    rw [admissibleBlockSymbol, UnitAddTorus.mFourier]
    simp only [ContinuousMap.coe_mk]
    rw [← Finset.prod_mul_distrib]
  have hbox (i : Fin d) :
      Finset.Icc (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1)) =
        ScalarAtomVariance.scalarFrequencyBox (s i) := by rfl
  simp_rw [hbox]
  simp_rw [hterm]
  rw [Finset.prod_univ_sum
    (fun i : Fin d => ScalarAtomVariance.scalarFrequencyBox (s i))
    (fun i n => (scalarBlock φ (s i) (n:ℝ) : ℂ) * fourier n (x i))]

theorem admissibleBlockKernel_integral_le {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d := by
  obtain ⟨L, hL, hscalar⟩ := exists_admissibleScalarBlockKernel_uniform_L1_bound φ
  refine ⟨L, hL, ?_⟩
  rw [admissibleBlockKernel_eq_product]
  have hprod := BrownianSharp.coordinateProductKernel_norm_integral_le
    (fun i => BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel φ (s i))
    (fun _ => L) (fun _ => hL)
    (fun i => hscalar (s i))
  simpa [admissibleBlockKernelProduct, Fintype.card_fin] using hprod


theorem exists_admissibleBlockKernel_uniform_L1_bound {d : ℕ}
    (φ : AdmissibleCutoff) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d := by
  obtain ⟨L, hL, hscalar⟩ := exists_admissibleScalarBlockKernel_uniform_L1_bound φ
  refine ⟨L, hL, ?_⟩
  intro s
  rw [admissibleBlockKernel_eq_product]
  have hprod := BrownianSharp.coordinateProductKernel_norm_integral_le
    (fun i => BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlockKernel φ (s i))
    (fun _ => L) (fun _ => hL) (fun i => hscalar (s i))
  simpa [admissibleBlockKernelProduct, Fintype.card_fin] using hprod

end BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
