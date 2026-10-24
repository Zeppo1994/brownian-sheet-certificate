import BrownianSharp.AlignmentOrdinaryIntegrationLower
import BrownianSharp.AlignmentFractionalDensity
import BrownianSharp.AlignmentOperatorKernelTrace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Lower bounds for integer-order RL operators from smooth trigonometric
source subspaces. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff

namespace BrownianSharp.AlignmentIntegerFractionalApproximationLower

open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentOrdinaryIntegrationLower
open BrownianSharp.AlignmentFractionalL2

def shiftedSineMode (K : ℕ) (i : ℕ) : UnitL2 :=
  profileToL2 (sineProfile (K+i))

theorem shiftedSineMode_orthonormal (K D : ℕ) :
    Orthonormal ℝ (fun i : Fin D => shiftedSineMode K i.val) := by
  apply sineSource_orthonormal.comp (fun i : Fin D => K+i.val)
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel hij)

/-- The single nonautomatic boundary jet for a finite sum of sine modes
through order two. -/
def sineFirstJet (K D : ℕ) : (Fin D → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ i : Fin D, c i * halfFrequency (K+i.val)
  map_add' c e := by simp [Finset.sum_add_distrib, add_mul]
  map_smul' a c := by simp [Finset.mul_sum, mul_assoc]

def sineJetKernel (K D : ℕ) : Submodule ℝ (Fin D → ℝ) :=
  LinearMap.ker (sineFirstJet K D)

theorem sineJetKernel_finrank_lower (K D : ℕ) :
    D - 1 ≤ Module.finrank ℝ (sineJetKernel K D) := by
  classical
  have hdim := (sineFirstJet K D).finrank_range_add_finrank_ker
  have hrank : Module.finrank ℝ (LinearMap.range (sineFirstJet K D)) ≤ 1 := by
    calc
      Module.finrank ℝ (LinearMap.range (sineFirstJet K D)) ≤ Module.finrank ℝ ℝ :=
        by simpa using (Submodule.finrank_mono
          (show LinearMap.range (sineFirstJet K D) ≤ ⊤ from le_top))
      _ = 1 := by simp
  have hD : Module.finrank ℝ (Fin D → ℝ) = D := by simp
  have hker : Module.finrank ℝ (sineJetKernel K D) =
      Module.finrank ℝ ((sineFirstJet K D).ker) := rfl
  rw [hD] at hdim
  rw [← hker] at hdim
  omega

/-- Source vectors obtained by taking two derivatives of shifted sine modes. -/
def sineSecondSourceMap (K D : ℕ) : (Fin D → ℝ) →ₗ[ℝ] UnitL2 where
  toFun c := ∑ i : Fin D,
    (c i * (halfFrequency (K+i.val))^2) • shiftedSineMode K i.val
  map_add' c e := by
    change (∑ i, ((c i + e i) * (halfFrequency (K+i.val))^2) •
      shiftedSineMode K i.val) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [add_mul, add_smul]
  map_smul' a c := by
    change (∑ i, (a * c i * (halfFrequency (K+i.val))^2) •
      shiftedSineMode K i.val) = _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
    congr 1
    simp only [RingHom.id_apply]
    ring

theorem sineSecondSourceMap_eq_zero_iff (K D : ℕ) (c : Fin D → ℝ) :
    sineSecondSourceMap K D c = 0 ↔ c = 0 := by
  constructor
  · intro hc
    funext j
    have hinner : ⟪sineSecondSourceMap K D c, shiftedSineMode K j.val⟫_ℝ = 0 := by
      rw [hc]
      simp
    have hs := shiftedSineMode_orthonormal K D
    rw [orthonormal_iff_ite] at hs
    have hformula : ⟪sineSecondSourceMap K D c, shiftedSineMode K j.val⟫_ℝ =
        c j * (halfFrequency (K+j.val))^2 := by
      change ⟪∑ i : Fin D, (c i * (halfFrequency (K+i.val))^2) •
        shiftedSineMode K i.val, shiftedSineMode K j.val⟫_ℝ = _
      rw [sum_inner]
      simp only [real_inner_smul_left]
      simp [hs]
    rw [hformula] at hinner
    have hfreq : halfFrequency (K+j.val) ≠ 0 := by
      dsimp [halfFrequency]
      positivity
    have hsq : (halfFrequency (K+j.val))^2 ≠ 0 := pow_ne_zero 2 hfreq
    exact (mul_eq_zero.mp hinner).resolve_right hsq
  · rintro rfl
    ext i
    simp [sineSecondSourceMap]

def sineJetGoodSource (K D : ℕ) : Submodule ℝ UnitL2 :=
  LinearMap.range ((sineSecondSourceMap K D).comp (sineJetKernel K D).subtype)

theorem sineJetGoodSource_finrank_lower (K D : ℕ) :
    D - 1 ≤ Module.finrank ℝ (sineJetGoodSource K D) := by
  classical
  let f := (sineSecondSourceMap K D).comp (sineJetKernel K D).subtype
  have hinj : Function.Injective f := by
    intro c e h
    apply Subtype.ext
    have hz : sineSecondSourceMap K D (c.val-e.val) = 0 := by
      rw [map_sub]
      change f c - f e = 0
      rw [h, sub_self]
    exact sub_eq_zero.mp ((sineSecondSourceMap_eq_zero_iff K D (c.val-e.val)).1 hz)
  have hrange := LinearMap.finrank_range_of_inj hinj
  have hker := sineJetKernel_finrank_lower K D
  change D - 1 ≤ Module.finrank ℝ (LinearMap.range f)
  exact hker.trans_eq hrange.symm

def sineCombination (K D : ℕ) (c : Fin D → ℝ) : ℝ → ℝ :=
  fun x => ∑ i : Fin D, c i * (Real.sqrt 2 *
    Real.sin (halfFrequency (K+i.val) * x))

theorem sineCombination_contDiff (K D : ℕ) (c : Fin D → ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (sineCombination K D c) := by
  unfold sineCombination
  fun_prop

def integerTwoOutput (K D : ℕ) (c : Fin D → ℝ) : ℝ → ℝ :=
  -sineCombination K D c

theorem integerTwoOutput_contDiff (K D : ℕ) (c : Fin D → ℝ) :
    ContDiff ℝ (∞ : ℕ∞ω) (integerTwoOutput K D c) := by
  unfold integerTwoOutput
  exact (sineCombination_contDiff K D c).neg

theorem iteratedDeriv_sineCombination (K D : ℕ) (c : Fin D → ℝ)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (sineCombination K D c) x =
      ∑ i : Fin D, c i * iteratedDeriv j
        (fun y : ℝ => Real.sqrt 2 * Real.sin (halfFrequency (K+i.val)*y)) x := by
  unfold sineCombination
  have hsum : ∀ i : Fin D, ContDiffAt ℝ j
      (fun y : ℝ => c i * (Real.sqrt 2 * Real.sin (halfFrequency (K+i.val)*y))) x := by
    intro i
    fun_prop
  rw [iteratedDeriv_fun_sum (fun i hi => hsum i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_const_mul (c i) (by fun_prop)]

/-- Explicit iterated derivative of one manuscript-normalized sine mode. -/
theorem iteratedDeriv_sineProfile_formula (m n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ =>
      Real.sqrt 2 * Real.sin (halfFrequency m * y)) x =
      Real.sqrt 2 * (halfFrequency m)^n * iteratedDeriv n Real.sin
        (halfFrequency m * x) := by
  have hs : ContDiff ℝ n Real.sin := Real.contDiff_sin
  have hcomp := iteratedDeriv_comp_const_mul hs (halfFrequency m)
  have hscomp : ContDiff ℝ n (fun y : ℝ => Real.sin (halfFrequency m * y)) :=
    hs.comp (contDiff_const.mul contDiff_id)
  have hfun : (fun y : ℝ => Real.sqrt 2 * Real.sin (halfFrequency m * y)) =
      fun y => Real.sqrt 2 * (fun z : ℝ => Real.sin (halfFrequency m * z)) y := rfl
  rw [hfun, iteratedDeriv_const_mul (n:=n) (f:=fun z : ℝ =>
    Real.sin (halfFrequency m * z)) (c:=Real.sqrt 2) hscomp.contDiffAt, hcomp]
  ring

/-- Even derivatives of the sine mode vanish at the left endpoint. -/
theorem iteratedDeriv_sineProfile_even_zero (m q : ℕ) :
    iteratedDeriv (2*q) (fun y : ℝ =>
      Real.sqrt 2 * Real.sin (halfFrequency m * y)) 0 = 0 := by
  rw [iteratedDeriv_sineProfile_formula]
  rw [Real.iteratedDeriv_even_sin]
  simp

/-- Odd derivatives of a sine mode at zero, including the frequency weight. -/
theorem iteratedDeriv_sineProfile_odd_at_zero (m q : ℕ) :
    iteratedDeriv (2*q+1) (fun y : ℝ =>
      Real.sqrt 2 * Real.sin (halfFrequency m * y)) 0 =
        Real.sqrt 2 * (halfFrequency m)^(2*q+1) * (-1)^q := by
  rw [iteratedDeriv_sineProfile_formula]
  rw [Real.iteratedDeriv_odd_sin]
  simp

theorem iteratedDeriv_sineProfile_two (m : ℕ) (x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => Real.sqrt 2 *
      Real.sin (halfFrequency m*y)) x =
        -(halfFrequency m)^2 * (Real.sqrt 2 * Real.sin (halfFrequency m*x)) := by
  rw [iteratedDeriv_sineProfile_formula]
  change Real.sqrt 2 * (halfFrequency m)^2 *
    iteratedDeriv (2*1) Real.sin (halfFrequency m*x) = _
  rw [Real.iteratedDeriv_even_sin]
  simp
  ring

theorem integerTwoOutput_jets_zero (K D : ℕ) (c : Fin D → ℝ)
    (hc : c ∈ sineJetKernel K D) :
    ∀ j ≤ 2, iteratedDeriv j (integerTwoOutput K D c) 0 = 0 := by
  intro j hj
  interval_cases j
  · simp [integerTwoOutput, sineCombination]
  · have hjet : sineFirstJet K D c = 0 := hc
    change iteratedDeriv 1 (fun x : ℝ => -(sineCombination K D c x)) 0 = 0
    rw [iteratedDeriv_fun_neg, iteratedDeriv_sineCombination]
    change -(∑ i : Fin D, c i * iteratedDeriv 1
      (fun y : ℝ => Real.sqrt 2 * Real.sin (halfFrequency (K+i.val)*y)) 0) = 0
    have hmode (i : Fin D) : iteratedDeriv 1
        (fun y : ℝ => Real.sqrt 2 * Real.sin (halfFrequency (K+i.val)*y)) 0 =
        Real.sqrt 2 * halfFrequency (K+i.val) := by
      simpa using iteratedDeriv_sineProfile_odd_at_zero (K+i.val) 0
    simp_rw [hmode]
    change (∑ i : Fin D, c i * halfFrequency (K+i.val)) = 0 at hjet
    have hmul : ∑ i : Fin D, c i * (Real.sqrt 2 * halfFrequency (K+i.val)) = 0 := by
      calc
        _ = Real.sqrt 2 * ∑ i : Fin D, c i * halfFrequency (K+i.val) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := by simpa using congrArg (fun z : ℝ => Real.sqrt 2*z) hjet
    rw [hmul]
    simp
  · change iteratedDeriv 2 (fun x : ℝ => -(sineCombination K D c x)) 0 = 0
    rw [iteratedDeriv_fun_neg, iteratedDeriv_sineCombination]
    change -(∑ i : Fin D, c i * iteratedDeriv 2
      (fun y : ℝ => Real.sqrt 2 * Real.sin (halfFrequency (K+i.val)*y)) 0) = 0
    have hmode (i : Fin D) : iteratedDeriv 2
        (fun y : ℝ => Real.sqrt 2 * Real.sin (halfFrequency (K+i.val)*y)) 0 = 0 := by
      rw [iteratedDeriv_sineProfile_two]
      simp
    simp_rw [hmode]
    simp

theorem integerTwoOutput_derivativeProfile_eq (K D : ℕ) (c : Fin D → ℝ) :
    derivativeProfile 2 (integerTwoOutput K D c) (integerTwoOutput_contDiff K D c) =
      ∑ i : Fin D, (c i * (halfFrequency (K+i.val))^2) •
        sineProfile (K+i.val) := by
  ext t
  change iteratedDeriv 2 (integerTwoOutput K D c) t.val = _
  change iteratedDeriv 2 (fun x : ℝ => -(sineCombination K D c x)) t.val = _
  rw [iteratedDeriv_fun_neg, iteratedDeriv_sineCombination]
  simp_rw [iteratedDeriv_sineProfile_two]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, sineProfile,
    ContinuousMap.coe_mk, smul_eq_mul]
  have harg (i : Fin D) : halfFrequency (K+i.val) * t.val =
      t.val * halfFrequency (K+i.val) := by ring
  simp_rw [harg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change -(c i *
      (-(halfFrequency (K+i.val))^2 *
        (Real.sqrt 2 * Real.sin (t.val*halfFrequency (K+i.val))))) =
    (c i * (halfFrequency (K+i.val))^2) *
      (Real.sqrt 2 * Real.sin (t.val*halfFrequency (K+i.val)))
  ring

theorem integerTwoOutput_source_eq (K D : ℕ) (c : Fin D → ℝ) :
    profileToL2 (derivativeProfile 2 (integerTwoOutput K D c)
      (integerTwoOutput_contDiff K D c)) = sineSecondSourceMap K D c := by
  rw [integerTwoOutput_derivativeProfile_eq]
  simp [sineSecondSourceMap, shiftedSineMode, map_sum, map_smul]

noncomputable def integerTwoOperator : UnitL2 →L[ℝ] C(UnitInterval,ℝ) :=
  fractionalRL 2 (by norm_num)

theorem integerTwoOperator_source_apply (K D : ℕ) (c : Fin D → ℝ)
    (hc : c ∈ sineJetKernel K D) :
    integerTwoOperator (sineSecondSourceMap K D c) =
      restrictProfile (integerTwoOutput K D c)
        (integerTwoOutput_contDiff K D c).continuous := by
  rw [integerTwoOperator, ← integerTwoOutput_source_eq]
  change fractionalOnC 2 (by norm_num) (derivativeProfile 2
    (integerTwoOutput K D c) (integerTwoOutput_contDiff K D c)) = _
  have horder : fractionalOnC 2 (by norm_num) = oneIntegralIterate 2 := by
    simpa using integerOrder_eq_iterate 2 (by norm_num)
  rw [horder]
  exact oneIntegralIterate_derivative_recovery 2 (integerTwoOutput K D c)
    (integerTwoOutput_contDiff K D c) (integerTwoOutput_jets_zero K D c hc)

theorem sineSecondSourceMap_norm_sq (K D : ℕ) (c : Fin D → ℝ) :
    ‖sineSecondSourceMap K D c‖^2 =
      ∑ i : Fin D, (c i * (halfFrequency (K+i.val))^2)^2 := by
  simpa [sineSecondSourceMap] using
    orthonormal_sum_norm_sq (fun i : Fin D => shiftedSineMode K i.val)
      (shiftedSineMode_orthonormal K D)
      (fun i : Fin D => c i * (halfFrequency (K+i.val))^2)

theorem integerTwoOutput_restrict_eq (K D : ℕ) (c : Fin D → ℝ) :
    restrictProfile (integerTwoOutput K D c)
      (integerTwoOutput_contDiff K D c).continuous =
      -∑ i : Fin D, c i • sineProfile (K+i.val) := by
  ext t
  simp [integerTwoOutput, sineCombination, restrictProfile, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, sineProfile, ContinuousMap.coe_mk, smul_eq_mul]

theorem integerTwoOutput_L2_norm_sq (K D : ℕ) (c : Fin D → ℝ) :
    ‖profileToL2 (restrictProfile (integerTwoOutput K D c)
      (integerTwoOutput_contDiff K D c).continuous)‖^2 =
        ∑ i : Fin D, (c i)^2 := by
  rw [integerTwoOutput_restrict_eq]
  have hsum := orthonormal_sum_norm_sq
    (fun i : Fin D => shiftedSineMode K i.val)
    (shiftedSineMode_orthonormal K D) (fun i => -c i)
  have hmap : profileToL2 (-∑ i : Fin D, c i • sineProfile (K+i.val)) =
      ∑ i : Fin D, (-c i) • shiftedSineMode K i.val := by
    simp [shiftedSineMode, map_neg, map_sum, map_smul]
  rw [hmap]
  calc
    ‖∑ i : Fin D, (-c i) • shiftedSineMode K i.val‖^2 =
        ∑ i : Fin D, ((-c i))^2 := hsum
    _ = ∑ i : Fin D, (c i)^2 := by simp

/-- The order-two map, followed by the canonical embedding of continuous
profiles into the target Hilbert space. -/
noncomputable def integerTwoL2Operator : UnitL2 →L[ℝ] UnitL2 :=
  profileToL2.comp integerTwoOperator

theorem integerTwoL2Operator_source_apply (K D : ℕ) (c : Fin D → ℝ)
    (hc : c ∈ sineJetKernel K D) :
    integerTwoL2Operator (sineSecondSourceMap K D c) =
      -∑ i : Fin D, c i • shiftedSineMode K i.val := by
  rw [integerTwoL2Operator, ContinuousLinearMap.comp_apply,
    integerTwoOperator_source_apply K D c hc,
    integerTwoOutput_restrict_eq]
  simp [shiftedSineMode, map_neg, map_sum, map_smul]

/-- Disjoint sine-frequency blocks have orthogonal order-two images in the
target L² Hilbert space. -/
theorem integerTwoL2Operator_disjoint_block_orthogonal
    (K D K' D' : ℕ) (c : Fin D → ℝ) (e : Fin D' → ℝ)
    (hc : c ∈ sineJetKernel K D) (he : e ∈ sineJetKernel K' D')
    (hdisj : ∀ i j : ℕ, i < D → j < D' → K+i ≠ K'+j) :
    ⟪integerTwoL2Operator (sineSecondSourceMap K D c),
      integerTwoL2Operator (sineSecondSourceMap K' D' e)⟫_ℝ = 0 := by
  rw [integerTwoL2Operator_source_apply K D c hc,
    integerTwoL2Operator_source_apply K' D' e he]
  have hs := sineSource_orthonormal
  rw [orthonormal_iff_ite] at hs
  have hcross (i : Fin D) (j : Fin D') :
      ⟪shiftedSineMode K i.val, shiftedSineMode K' j.val⟫_ℝ = 0 := by
    have hij : K+i.val ≠ K'+j.val := hdisj i.val j.val i.isLt j.isLt
    simpa [shiftedSineMode, hs, hij]
  simp [inner_sum, sum_inner, inner_smul_left, inner_smul_right, hcross]

theorem integerTwoOperator_energy_lower_of_jet (K D : ℕ) (hD : 0 < D)
    (c : Fin D → ℝ) (hc : c ∈ sineJetKernel K D)
    (hnorm : ‖sineSecondSourceMap K D c‖ = 1) :
    (((halfFrequency (K+D))^2)⁻¹)^2 ≤
      ∫ t, (integerTwoOperator (sineSecondSourceMap K D c) t)^2
        ∂unitTargetMeasure := by
  let freqMax : ℝ := halfFrequency (K+D)
  have hfreqMax : 0 < freqMax := by
    dsimp [freqMax, halfFrequency]
    positivity
  have hfreq (i : Fin D) : 0 < halfFrequency (K+i.val) ∧
      halfFrequency (K+i.val) ≤ freqMax := by
    constructor
    · dsimp [halfFrequency]
      positivity
    · dsimp [freqMax, halfFrequency]
      have hi : (K+i.val:ℕ) ≤ K+D := by omega
      have hcast : ((K+i.val:ℕ):ℝ) ≤ (K+D:ℕ) := by exact_mod_cast hi
      have hpi := Real.pi_pos
      nlinarith
  have hsumle :
      (∑ i : Fin D, (c i * (halfFrequency (K+i.val))^2)^2) ≤
        freqMax^4 * ∑ i : Fin D, (c i)^2 := by
    calc
      _ ≤ ∑ i : Fin D, (c i)^2 * freqMax^4 := by
        apply Finset.sum_le_sum
        intro i hi
        have hf := hfreq i
        have hsquare : (halfFrequency (K+i.val))^4 ≤ freqMax^4 := by
          gcongr
          exact (hfreq i).1.le
          exact hf.2
        have hc2 : 0 ≤ (c i)^2 := sq_nonneg _
        nlinarith [sq_nonneg (c i * (halfFrequency (K+i.val))^2)]
      _ = freqMax^4 * ∑ i : Fin D, (c i)^2 := by
        calc
          _ = ∑ i : Fin D, freqMax^4 * (c i)^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [Finset.mul_sum]
  have hone : 1 = ∑ i : Fin D,
      (c i * (halfFrequency (K+i.val))^2)^2 := by
    rw [← sineSecondSourceMap_norm_sq, hnorm]
    norm_num
  have hcoef : 1 ≤ freqMax^4 * ∑ i : Fin D, (c i)^2 := by linarith
  have hbound : (freqMax^4)⁻¹ ≤ ∑ i : Fin D, (c i)^2 := by
    have hfreq4 : 0 < freqMax^4 := by positivity
    rw [← one_div]
    rw [div_le_iff₀ hfreq4]
    nlinarith [hcoef]
  have houtput : (((freqMax^2)⁻¹)^2) ≤
      ‖profileToL2 (restrictProfile (integerTwoOutput K D c)
        (integerTwoOutput_contDiff K D c).continuous)‖^2 := by
    rw [integerTwoOutput_L2_norm_sq]
    calc
      ((freqMax^2)⁻¹)^2 = (freqMax^4)⁻¹ := by
        rw [← inv_pow]
        congr 1
        ring
      _ ≤ ∑ i : Fin D, (c i)^2 := hbound
  calc
    (((halfFrequency (K+D))^2)⁻¹)^2 = ((freqMax^2)⁻¹)^2 := by rfl
    _ ≤ ‖profileToL2 (restrictProfile (integerTwoOutput K D c)
        (integerTwoOutput_contDiff K D c).continuous)‖^2 := houtput
    _ = ∫ t, (integerTwoOperator (sineSecondSourceMap K D c) t)^2
        ∂unitTargetMeasure := by
      rw [← integerTwoOperator_source_apply K D c hc]
      exact (integral_unitTargetMeasure _).symm

/-- Dyadic block maximal frequency is bounded uniformly by a fixed multiple
of its lower scale. -/
theorem halfFrequency_dyadic_block_upper (s : ℕ) :
    halfFrequency (2^(s+2)) ≤ 5 * Real.pi * (2:ℝ)^s := by
  have hbase : 1 ≤ (2:ℝ)^s := by
    induction s with
    | zero => norm_num
    | succ s ih =>
        rw [pow_succ]
        nlinarith [ih]
  have hpowNat : 2^(s+2) = 4*2^s := by
    rw [pow_add]
    norm_num
    ring
  have hpow : ((2^(s+2):ℕ):ℝ) = 4*(2:ℝ)^s := by exact_mod_cast hpowNat
  rw [halfFrequency, hpow]
  have hcoef : 4*(2:ℝ)^s + 1/2 ≤ 5*(2:ℝ)^s := by nlinarith [hbase]
  have hm := mul_le_mul_of_nonneg_right hcoef (le_of_lt Real.pi_pos)
  calc
    (4*(2:ℝ)^s + 1/2) * Real.pi ≤ 5*(2:ℝ)^s * Real.pi := hm
    _ = 5 * Real.pi * (2:ℝ)^s := by ring

/-- The minimum image norm on a selected dyadic sine block has the scale
`(25 π² 2^(2s))⁻¹`. -/
theorem integerTwo_dyadic_block_sigma_lower (s : ℕ) :
    (25 * Real.pi^2 * (2:ℝ)^(2*s))⁻¹ ≤
      ((halfFrequency (2^(s+2)))^2)⁻¹ := by
  have hfreq : 0 < halfFrequency (2^(s+2)) := by
    dsimp [halfFrequency]
    positivity
  have hupper := halfFrequency_dyadic_block_upper s
  have hden : (halfFrequency (2^(s+2)))^2 ≤
      25 * Real.pi^2 * (2:ℝ)^(2*s) := by
    have hsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hupper
    calc
      _ ≤ (5 * Real.pi * (2:ℝ)^s)^2 := hsq
      _ = 25 * Real.pi^2 * (2:ℝ)^(2*s) := by
        calc
          _ = 25 * Real.pi^2 * ((2:ℝ)^s)^2 := by ring
          _ = _ := by rw [← pow_mul]; congr 1; ring
  simpa [one_div] using
    (one_div_le_one_div_of_le (by positivity :
      0 < (halfFrequency (2^(s+2)))^2) hden)

/-- Product form for a tensor shape. This is the factorwise estimate needed
before collecting the dyadic exponents by their total grade. -/
theorem integerTwo_dyadic_block_product_sigma_lower {d : ℕ}
    (s : Fin d → ℕ) :
    (∏ i : Fin d, (25 * Real.pi^2 * (2:ℝ)^(2*s i))⁻¹) ≤
      ∏ i : Fin d, ((halfFrequency (2^(s i+2)))^2)⁻¹ := by
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    exact integerTwo_dyadic_block_sigma_lower (s i)

/-- Trace lower bound for the actual order-two RL map. The source subspace is
the image of the codimension-one first-jet kernel in a block of sine modes. -/
theorem integerTwoOperator_approximationNumber_lower
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ D₀ : ℕ, 2*k+1 ≤ D₀ ∧
      ENNReal.ofReal (((halfFrequency (2*k+2))^2)⁻¹ *
        Real.sqrt ((D₀-(k-1):ℕ):ℝ)) ≤
        BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
          integerTwoOperator k := by
  classical
  let K : ℕ := 0
  let D : ℕ := 2*k+2
  haveI : FiniteDimensional ℝ (Fin D → ℝ) := inferInstance
  haveI : FiniteDimensional ℝ (sineJetKernel K D) :=
    Submodule.finiteDimensional_of_le (le_top : sineJetKernel K D ≤ ⊤)
  let f : (sineJetKernel K D) →ₗ[ℝ] UnitL2 :=
    (sineSecondSourceMap K D).comp (sineJetKernel K D).subtype
  haveI : FiniteDimensional ℝ (LinearMap.range f) := Module.Finite.range f
  let V : Submodule ℝ UnitL2 := LinearMap.range f
  let T : UnitL2 →L[ℝ] C(UnitInterval,ℝ) := integerTwoOperator
  let σ : ℝ := ((halfFrequency (K+D))^2)⁻¹
  have hDpos : 0 < D := by dsimp [D]; omega
  letI : FiniteDimensional ℝ V := by simpa [V] using
    (inferInstance : FiniteDimensional ℝ (LinearMap.range f))
  let D₀ : ℕ := Module.finrank ℝ V
  have hD₀ : 2*k+1 ≤ D₀ := by
    have hlower : D-1 ≤ Module.finrank ℝ V := by
      change D-1 ≤ Module.finrank ℝ (sineJetGoodSource K D)
      exact sineJetGoodSource_finrank_lower K D
    dsimp [D₀, D] at hlower ⊢
    omega
  have hdim : Module.finrank ℝ V = D₀ := rfl
  have hkD₀ : k ≤ D₀ := by omega
  have hσ : 0 ≤ σ := by
    dsimp [σ]
    positivity
  have henergy : ∀ v : V, ‖(v : UnitL2)‖ = 1 →
      σ^2 ≤ ∫ t, (T (v : UnitL2) t)^2 ∂unitTargetMeasure := by
    intro v hv
    have hvmem : (v : UnitL2) ∈ LinearMap.range f := v.property
    let cSubtype : sineJetKernel K D := Classical.choose (LinearMap.mem_range.mp hvmem)
    have hcSubtype : f cSubtype = (v : UnitL2) :=
      Classical.choose_spec (LinearMap.mem_range.mp hvmem)
    let c : Fin D → ℝ := cSubtype.val
    have hck' : c ∈ sineJetKernel K D := cSubtype.property
    have hsource : sineSecondSourceMap K D c = (v : UnitL2) := by
      simpa [f, c] using hcSubtype
    have hnormc : ‖sineSecondSourceMap K D c‖ = 1 := by
      simpa [hsource] using hv
    have hσenergy := integerTwoOperator_energy_lower_of_jet K D hDpos c hck' hnormc
    simpa [σ, T, hsource] using hσenergy
  have htrace := AlignmentOperatorKernelTrace.approximationNumber_lower_of_subspace_trace
    unitTargetMeasure T V hdim hk hkD₀ σ hσ henergy
  refine ⟨D₀, hD₀, ?_⟩
  simpa [σ, T, K, D] using htrace

/-- A transparent polynomial-rate corollary of the order-two sine-block
construction. -/
theorem integerTwoOperator_approximationNumber_lower_rate
    {k : ℕ} (hk : 1 ≤ k) :
    ENNReal.ofReal (Real.sqrt (k:ℝ) /
      (25 * Real.pi^2 * (k:ℝ)^2)) ≤
      BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
        integerTwoOperator k := by
  obtain ⟨D₀, hD₀, hlow⟩ := integerTwoOperator_approximationNumber_lower hk
  have hrad : 1 ≤ 2*k+2 := by omega
  have hdiff : k ≤ D₀-(k-1) := by omega
  have hsqrt : Real.sqrt (k:ℝ) ≤
      Real.sqrt ((D₀-(k-1):ℕ):ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hdiff
  have hkR : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have hfreqpos : 0 < halfFrequency (2*k+2) := by
    dsimp [halfFrequency]
    positivity
  have hfrequpper : halfFrequency (2*k+2) ≤ 5 * Real.pi * (k:ℝ) := by
    have hcoef : (2:ℝ) * (k:ℝ) + 2 + 1/2 ≤ 5 * (k:ℝ) := by
      nlinarith [hkR]
    have hm := mul_le_mul_of_nonneg_right hcoef (le_of_lt Real.pi_pos)
    calc
      halfFrequency (2*k+2) = (2 * (k:ℝ) + 2 + 1/2) * Real.pi := by
        simp [halfFrequency]
      _ ≤ 5 * (k:ℝ) * Real.pi := hm
      _ = 5 * Real.pi * (k:ℝ) := by ring
  have hinv : 1 / (5 * Real.pi * (k:ℝ))^2 ≤
      1 / (halfFrequency (2*k+2))^2 := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [hfreqpos, hfrequpper]
  have hfactor : 0 ≤ Real.sqrt (k:ℝ) := Real.sqrt_nonneg _
  have hreal : Real.sqrt (k:ℝ) /
      (25 * Real.pi^2 * (k:ℝ)^2) ≤
      ((halfFrequency (2*k+2))^2)⁻¹ *
        Real.sqrt ((D₀-(k-1):ℕ):ℝ) := by
    have hinv' : 1 / (25 * Real.pi^2 * (k:ℝ)^2) ≤
        ((halfFrequency (2*k+2))^2)⁻¹ := by
      convert hinv using 1 <;> field_simp <;> ring
    calc
      _ = (1 / (25 * Real.pi^2 * (k:ℝ)^2)) * Real.sqrt (k:ℝ) := by ring
      _ ≤ ((halfFrequency (2*k+2))^2)⁻¹ *
          Real.sqrt ((D₀-(k-1):ℕ):ℝ) :=
        mul_le_mul hinv' hsqrt (Real.sqrt_nonneg _) (by positivity)
  exact (ENNReal.ofReal_le_ofReal hreal).trans hlow

end BrownianSharp.AlignmentIntegerFractionalApproximationLower
