import BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity
import BrownianSharp.AlignmentPaperFiniteMixedSquareLp
import BrownianSharp.AlignmentPaperLpJointDvp
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperProductGradeSquareFunctionLp

open BrownianSharp
open BrownianSharp.AlignmentPaperProductSquareFunctionLp
open BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity
open BrownianSharp.AlignmentPaperFiniteKernelLpDensity
open BrownianSharp.AlignmentPaperFiniteMixedSquareLp
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open UnitAddTorus

set_option maxHeartbeats 1000000

local instance gradeTorusMeasureSpace (d : ℕ) : MeasureSpace (UnitAddTorus (Fin d)) :=
  ⟨Measure.pi fun _ : Fin d => AddCircle.haarAddCircle⟩
local instance gradeTorusProbability (d : ℕ) :
    IsProbabilityMeasure
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  infer_instance

def productGradeSquareConstant (p : ℝ) : ℝ :=
  (24*(2:ℝ)^(p/2))^2 *
    (2^p*(p*BrownianSharp.AlignmentPaperSignedKernelLp.uniformSignedKernelWeakConstant/
      (p-1)+p/(2-p)))

/-- The finite grade of actual smooth product blocks has the same dimensionwise
square-function bound as the enclosing depth box, with no shape-count loss. -/
theorem productSmoothGrade_mixedLp_le_of_memLp
    (n d : ℕ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : Lp ℂ (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) :
    (∑ s : Shape d n,
      (∫ x : UnitAddTorus (Fin d),
        ‖productSmoothBlockConvolution (fun i => s.1 i) (f : _ → ℂ) x‖^p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))^(2/p))^(p/2) ≤
      (productGradeSquareConstant p)^d *
        ∫ x : UnitAddTorus (Fin d), ‖f x‖^p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  let ι := Fin d → Fin (n+1)
  let C := productGradeSquareConstant p
  have hp0 : 0 < p := by linarith
  have hpE : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : 1 ≤ p)
  haveI : Fact ((1:ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨hpE⟩
  have hfin : Integrable (f : UnitAddTorus (Fin d) → ℂ) μ :=
    (Lp.memLp f).integrable hpE
  let φ : Shape d n → ι := fun s i =>
    ⟨s.1 i, Nat.lt_succ_of_le (shapeCoordinate_le_grade s i)⟩
  have hφ_inj : Function.Injective φ := by
    intro s t hst
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun hst i)
  have hC : 0 ≤ C := by
    dsimp [C, productGradeSquareConstant]
    have hW := BrownianSharp.AlignmentPaperSignedKernelLp.uniformSignedKernelWeakConstant_nonneg
    positivity
  have hCpow : 0 ≤ C^d := pow_nonneg hC _
  let block : (Fin d → ℕ) → C(UnitAddTorus (Fin d),ℂ) := fun s =>
    ⟨applyKernel (μ := μ) (productBlockIntegralKernel s)
        (f : UnitAddTorus (Fin d) → ℂ),
      applyKernel_continuous (μ := μ)
        (productBlockIntegralKernel s) hfin⟩
  let u : Shape d n → C(UnitAddTorus (Fin d),ℂ) := fun s => block s.1
  let v : ι → C(UnitAddTorus (Fin d),ℂ) := fun t =>
    block (fun i => (t i).val)
  have hblock (s : Shape d n) (x : UnitAddTorus (Fin d)) :
      u s x = productSmoothBlockConvolution (fun i => s.1 i) (f : _ → ℂ) x := by
    exact applyKernel_productBlockIntegralKernel (fun i => s.1 i) (f : _ → ℂ) x
  have hvblock (t : ι) (x : UnitAddTorus (Fin d)) :
      v t x = productSmoothBlockConvolution (fun i => (t i).val) (f : _ → ℂ) x := by
    exact applyKernel_productBlockIntegralKernel (fun i => (t i).val) (f : _ → ℂ) x
  have hgrade_le_full (x : UnitAddTorus (Fin d)) :
      (∑ s : Shape d n,
        ‖productSmoothBlockConvolution (fun i => s.1 i) (f : _ → ℂ) x‖^2) ≤
      (∑ t : ι,
        ‖productSmoothBlockConvolution (fun i => (t i).val) (f : _ → ℂ) x‖^2) := by
    have hsumimg :
        (∑ s : Shape d n,
          ‖productSmoothBlockConvolution (fun i => s.1 i) (f : _ → ℂ) x‖^2) =
        ∑ t ∈ (Finset.univ.image φ),
          ‖productSmoothBlockConvolution (fun i => (t i).val) (f : _ → ℂ) x‖^2 := by
      exact (Finset.sum_image
        (f := fun t : ι =>
          ‖productSmoothBlockConvolution (fun i => (t i).val) (f : _ → ℂ) x‖^2)
        (fun _ _ _ _ hab => hφ_inj hab)).symm
    rw [hsumimg]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (by intro t ht hnot; positivity)
  let fullSq : UnitAddTorus (Fin d) → ℝ := fun x =>
    (∑ t : ι,
      ‖productSmoothBlockConvolution (fun i => (t i).val) (f : _ → ℂ) x‖^2)^(p/2)
  have hfull_cont : Continuous fullSq := by
    have hvsum : Continuous (fun x : UnitAddTorus (Fin d) =>
        ∑ t : ι, ‖v t x‖^2) :=
      continuous_finset_sum _ (fun t _ => by fun_prop)
    have heq : fullSq = fun x => (∑ t : ι, ‖v t x‖^2)^(p/2) := by
      funext x
      congr 2
    rw [heq]
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ p/2)).comp hvsum
  have hfull_int : Integrable fullSq μ :=
    hfull_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfull_nonneg : 0 ≤ᵐ[μ] fullSq := ae_of_all _ (fun x => by
    dsimp [fullSq]
    positivity)
  have hsrc_power : Integrable (fun x : UnitAddTorus (Fin d) => ‖f x‖^p) μ := by
    have h := (Lp.memLp f).integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top
    simpa [ENNReal.toReal_ofReal hp0.le] using h
  have hfull_to_lintegral :
      ENNReal.ofReal (∫ x, fullSq x ∂μ) = ∫⁻ x, ENNReal.ofReal (fullSq x) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hfull_int hfull_nonneg
  have hsrc_to_lintegral :
      ENNReal.ofReal (∫ x, ‖f x‖^p ∂μ) =
        ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hsrc_power
      (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg (f x)) _))
  have hbox := productSmoothSquareFunction_lintegral_lp_le_of_memLp
    n d hp1 hp2 f
  have hbox' :
      (∫⁻ x, ENNReal.ofReal (fullSq x) ∂μ) ≤
        ENNReal.ofReal (C^d) *
          (∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ) := by
    simpa [μ, ι, C, fullSq, productGradeSquareConstant] using hbox
  have hmixed := finite_mixed_square_le_integral
    (μ := μ) (p := p) hp1 (le_of_lt hp2) u
  have hgrade_integral :
      (∑ s : Shape d n,
        (∫ x, ‖u s x‖^p ∂μ)^(2/p))^(p/2) ≤ ∫ x, fullSq x ∂μ := by
    let gradeSq : UnitAddTorus (Fin d) → ℝ := fun x =>
      (∑ s : Shape d n, ‖u s x‖^2)^(p/2)
    have hgrade_cont : Continuous gradeSq := by
      dsimp [gradeSq]
      apply (Real.continuous_rpow_const (by linarith : 0 ≤ p/2)).comp
      exact continuous_finset_sum _ fun s _ => by fun_prop
    have hgrade_int : Integrable gradeSq μ :=
      hgrade_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hpoint (x : UnitAddTorus (Fin d)) :
        (∑ s : Shape d n, ‖u s x‖^2)^(p/2) ≤ fullSq x := by
      have hsquares := hgrade_le_full x
      apply Real.rpow_le_rpow (by positivity) hsquares
      linarith
    calc
      _ ≤ ∫ x, gradeSq x ∂μ := by simpa [gradeSq] using hmixed
      _ ≤ ∫ x, fullSq x ∂μ := by
        apply integral_mono hgrade_int hfull_int
        · intro x
          exact hpoint x
  have hgrade_nonneg : 0 ≤
      (∑ s : Shape d n,
        (∫ x, ‖u s x‖^p ∂μ)^(2/p))^(p/2) := by positivity
  have hsrc_nonneg : 0 ≤ ∫ x, ‖f x‖^p ∂μ :=
    integral_nonneg (fun x => by positivity)
  have hRHS_nonneg : 0 ≤ C^d * ∫ x, ‖f x‖^p ∂μ :=
    mul_nonneg hCpow hsrc_nonneg
  have hbox_real :
      ENNReal.ofReal (∫ x, fullSq x ∂μ) ≤
        ENNReal.ofReal (C^d * ∫ x, ‖f x‖^p ∂μ) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (fullSq x) ∂μ := hfull_to_lintegral
      _ ≤ ENNReal.ofReal (C^d) *
          (∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ) := hbox'
      _ = ENNReal.ofReal (C^d) * ENNReal.ofReal (∫ x, ‖f x‖^p ∂μ) := by
        rw [← hsrc_to_lintegral]
      _ = ENNReal.ofReal (C^d * ∫ x, ‖f x‖^p ∂μ) := by
        rw [← ENNReal.ofReal_mul hCpow]
  have hreal_enn :
      ENNReal.ofReal
        ((∑ s : Shape d n,
          (∫ x, ‖u s x‖^p ∂μ)^(2/p))^(p/2)) ≤
        ENNReal.ofReal (C^d * ∫ x, ‖f x‖^p ∂μ) := by
    apply (ENNReal.ofReal_le_ofReal_iff hRHS_nonneg).2
    calc
      _ ≤ ∫ x, fullSq x ∂μ := hgrade_integral
      _ ≤ C^d * ∫ x, ‖f x‖^p ∂μ := by
        apply (ENNReal.ofReal_le_ofReal_iff hRHS_nonneg).1
        exact hbox_real
  exact (ENNReal.ofReal_le_ofReal_iff hRHS_nonneg).1 hreal_enn

end BrownianSharp.AlignmentPaperProductGradeSquareFunctionLp
