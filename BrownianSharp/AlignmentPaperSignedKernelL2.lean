import BrownianSharp.AlignmentPeriodicCutoffYoung
import BrownianSharp.AlignmentPeriodicSpectralEnergy
import BrownianSharp.AlignmentTrigonometricL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

/-! Depth-uniform strong L² control of the actual signed smooth dyadic kernel
convolution. The source is the actual complex L² space on the one-dimensional
torus; no continuity assumption is imposed on it. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPaperSignedKernelL2

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.AlignmentFiniteFourierMultiplierConvolution
open BrownianSharp.AlignmentPeriodicFourierReconstruction
open BrownianSharp.AlignmentTrigonometricL2
open UnitAddTorus

local instance : MeasureSpace (UnitAddTorus (Fin 1)) :=
  ⟨Measure.pi fun _ : Fin 1 => AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin 1))) := by
  infer_instance
local instance : Measure.IsAddHaarMeasure (volume : Measure (UnitAddTorus (Fin 1))) := by
  change Measure.IsAddHaarMeasure
    (Measure.pi fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  infer_instance

private def scalarScale (s : ℕ) : Fin 1 → ℕ := fun _ => s

def signedDyadicSupport (N : ℕ) : Finset (Fin 1 → ℤ) :=
  frequencyBox (scalarScale N)

def signedDyadicSymbol (N : ℕ) (ε : Fin (N+1) → ℝ)
    (k : Fin 1 → ℤ) : ℂ :=
  ∑ s : Fin (N+1),
    (ε s : ℂ) *
      (BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
        smoothResolutionCutoff s.val (k 0 : ℝ) : ℂ)

def signedDyadicL2Multiplier (N : ℕ) (ε : Fin (N+1) → ℝ)
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1)))) :
    Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1))) :=
  (torusFourierPolynomial (signedDyadicSupport N)
    (fun k => signedDyadicSymbol N ε k * UnitAddTorus.mFourierCoeff g k)).toLp
      2 (volume : Measure (UnitAddTorus (Fin 1))) ℂ

def signedDyadicL2MultiplierFunction (N : ℕ) (ε : Fin (N+1) → ℝ)
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1)))) :
    UnitAddTorus (Fin 1) → ℂ :=
  torusFourierPolynomial (signedDyadicSupport N)
    (fun k => signedDyadicSymbol N ε k * UnitAddTorus.mFourierCoeff g k)

private theorem scalarBlock_nonneg (s : ℕ) (ξ : ℝ) :
    0 ≤ BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock smoothResolutionCutoff s ξ := by
  by_cases hs : s = 0
  · subst s
    exact (BrownianSharp.SmoothResolution.cutoff_bounds ξ).1
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    unfold BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
    rw [if_neg hs]
    have harg : |ξ / (2 : ℝ)^s| ≤ |ξ / (2 : ℝ)^(s-1)| := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ)<2^s),
        abs_div, abs_of_pos (by positivity : (0:ℝ)<2^(s-1))]
      apply div_le_div_of_nonneg_left (abs_nonneg ξ)
      · positivity
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hsq : (ξ/(2:ℝ)^s)^2 ≤ (ξ/(2:ℝ)^(s-1))^2 := by
      calc
        (ξ/(2:ℝ)^s)^2 = |ξ/(2:ℝ)^s|^2 := by rw [sq_abs]
        _ ≤ |ξ/(2:ℝ)^(s-1)|^2 := by
          exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 harg
        _ = (ξ/(2:ℝ)^(s-1))^2 := by rw [sq_abs]
    have hmono : cutoff (ξ/(2:ℝ)^(s-1)) ≤ cutoff (ξ/(2:ℝ)^s) := by
      have harg' : ((ξ/(2:ℝ)^s)^2-1)/3 ≤
          ((ξ/(2:ℝ)^(s-1))^2-1)/3 := by nlinarith [hsq]
      have ht := Real.smoothTransition.monotone harg'
      unfold cutoff
      linarith
    simpa [smoothResolutionCutoff] using sub_nonneg.mpr hmono

private theorem scalarBlock_sum_le_one (N : ℕ) (ξ : ℝ) :
    (∑ s ∈ Finset.range (N+1), BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock smoothResolutionCutoff s ξ) ≤ 1 := by
  have hnonneg : ∀ s ∈ Finset.range (N+1),
      0 ≤ BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock smoothResolutionCutoff s ξ := by
    intro s hs
    exact scalarBlock_nonneg s ξ
  have hsum := BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock_sum
    smoothResolutionCutoff N ξ
  have hsum_le : (∑ s ∈ Finset.range (N+1), BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock smoothResolutionCutoff s ξ) ≤ 1 := by
    rw [hsum]
    exact (BrownianSharp.SmoothResolution.cutoff_bounds _).2
  exact hsum_le

private theorem signedDyadicSymbol_norm_le (N : ℕ) (ε : Fin (N+1) → ℝ)
    (hε : ∀ s, |ε s| ≤ 1) (k : Fin 1 → ℤ) :
    ‖signedDyadicSymbol N ε k‖ ≤ 1 := by
  have hterms (s : Fin (N+1)) :
      ‖(ε s : ℂ) *
        (BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
          smoothResolutionCutoff s.val (k 0 : ℝ) : ℂ)‖ ≤
        BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
          smoothResolutionCutoff s.val (k 0 : ℝ) := by
    rw [norm_mul, Complex.norm_real]
    have hsε := hε s
    have hb := scalarBlock_nonneg s.val (k 0 : ℝ)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
    calc
      |ε s| * BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
          smoothResolutionCutoff s.val (k 0 : ℝ) ≤
          1 * BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
            smoothResolutionCutoff s.val (k 0 : ℝ) :=
        mul_le_mul_of_nonneg_right hsε hb
      _ = _ := by ring
  have hsumfin :
      (∑ s : Fin (N+1),
        BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
          smoothResolutionCutoff s.val (k 0 : ℝ)) ≤ 1 := by
    have hsum := scalarBlock_sum_le_one N (k 0 : ℝ)
    have heq :
        (∑ s : Fin (N+1),
          BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
            smoothResolutionCutoff s.val (k 0 : ℝ)) =
          ∑ s ∈ Finset.range (N+1),
            BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
              smoothResolutionCutoff s (k 0 : ℝ) := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun s => BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
          smoothResolutionCutoff s (k 0 : ℝ)) (N+1))
    rw [heq]
    exact hsum
  calc
    ‖signedDyadicSymbol N ε k‖ ≤
        ∑ s : Fin (N+1),
          ‖(ε s : ℂ) *
            (BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
              smoothResolutionCutoff s.val (k 0 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ s : Fin (N+1),
          BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
            smoothResolutionCutoff s.val (k 0 : ℝ) := by
            apply Finset.sum_le_sum
            intro s hs
            exact hterms s
    _ ≤ 1 := hsumfin

/-- The actual signed cutoff multiplier has L² operator norm at most one,
uniformly in depth and every real sign sequence with |ε_s|≤1. -/
theorem signedDyadicL2Multiplier_norm_sq_le (N : ℕ)
    (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1)))) :
    ‖signedDyadicL2Multiplier N ε g‖^2 ≤ ‖g‖^2 := by
  classical
  let S := signedDyadicSupport N
  let a := signedDyadicSymbol N ε
  have hpoly := AlignmentTrigonometricL2.fourierPolynomial_L2_norm_sq
    S (fun k => a k * UnitAddTorus.mFourierCoeff g k)
  have hcoeff_nonneg (k : Fin 1 → ℤ) : 0 ≤ ‖UnitAddTorus.mFourierCoeff g k‖^2 := by positivity
  have hsum :
      (∑ k ∈ S, ‖a k * UnitAddTorus.mFourierCoeff g k‖^2) ≤
        ∑ k ∈ S, ‖UnitAddTorus.mFourierCoeff g k‖^2 := by
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul]
    have ha := signedDyadicSymbol_norm_le N ε hε k
    have haSq : ‖a k‖^2 ≤ 1 := by
      nlinarith [ha, norm_nonneg (a k)]
    calc
      (‖a k‖ * ‖UnitAddTorus.mFourierCoeff g k‖)^2 =
          ‖a k‖^2 * ‖UnitAddTorus.mFourierCoeff g k‖^2 := by rw [mul_pow]
      _ ≤ 1 * ‖UnitAddTorus.mFourierCoeff g k‖^2 :=
        mul_le_mul_of_nonneg_right haSq (hcoeff_nonneg k)
      _ = _ := by ring
  have horth : Orthonormal ℂ (fun k : Fin 1 → ℤ =>
      (UnitAddTorus.mFourierLp (d := Fin 1) (2 : ℝ≥0∞) k :
        Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1))))) :=
    UnitAddTorus.orthonormal_mFourier (d := Fin 1)
  have hB := horth.sum_inner_products_le g (s := S)
  have hInner (k : Fin 1 → ℤ) :
      inner ℂ (UnitAddTorus.mFourierLp 2 k) g = UnitAddTorus.mFourierCoeff g k := by
    rw [← UnitAddTorus.coe_mFourierBasis,
      ← UnitAddTorus.mFourierBasis.repr_apply_apply,
      UnitAddTorus.mFourierBasis_repr]
  have hB' : (∑ k ∈ S, ‖UnitAddTorus.mFourierCoeff g k‖^2) ≤ ‖g‖^2 := by
    simpa only [hInner] using hB
  change ‖(torusFourierPolynomial S
    (fun k => a k * UnitAddTorus.mFourierCoeff g k)).toLp
      2 (volume : Measure (UnitAddTorus (Fin 1))) ℂ‖^2 ≤ ‖g‖^2
  rw [hpoly]
  exact hsum.trans hB'

/-- The actual finite signed sum of the smooth dyadic kernels, pulled back to
`UnitAddTorus (Fin 1)` by the canonical coordinate product kernel. -/
def signedDyadicKernel (N : ℕ) (ε : Fin (N+1) → ℝ) :
    C(UnitAddTorus (Fin 1), ℂ) :=
  ∑ s : Fin (N+1), (ε s : ℂ) •
    admissibleBlockKernel smoothResolutionCutoff (scalarScale s.val)

def signedDyadicConvolutionFunction (N : ℕ) (ε : Fin (N+1) → ℝ)
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1)))) :
    UnitAddTorus (Fin 1) → ℂ :=
  fun x => ∫ y : UnitAddTorus (Fin 1),
    signedDyadicKernel N ε y * g (x-y)
      ∂(volume : Measure (UnitAddTorus (Fin 1)))

private theorem scalarScale_frequencyBox_subset (N : ℕ) (s : Fin (N+1)) :
    frequencyBox (scalarScale s.val) ⊆ signedDyadicSupport N := by
  intro k hk
  change k ∈ frequencyBox (scalarScale N)
  simp only [frequencyBox, Fintype.mem_piFinset] at hk ⊢
  intro i
  have hki := hk i
  simp only [Finset.mem_Icc] at hki ⊢
  have hpowR : (2:ℝ)^(s.val+1) ≤ (2:ℝ)^(N+1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hpowZ : (2:ℤ)^(s.val+1) ≤ (2:ℤ)^(N+1) := by exact_mod_cast hpowR
  constructor
  · exact (neg_le_neg hpowZ).trans hki.1
  · exact hki.2.trans hpowZ

private theorem admissibleBlockSymbol_eq_scalarBlock (s : Fin (N+1))
    (k : Fin 1 → ℤ) :
    admissibleBlockSymbol smoothResolutionCutoff (scalarScale s.val) k =
      (BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
        smoothResolutionCutoff s.val (k 0 : ℝ) : ℂ) := by
  simp [admissibleBlockSymbol, scalarScale]

private theorem scalarBlock_zero_of_not_frequencyBox (N : ℕ) (s : Fin (N+1))
    {k : Fin 1 → ℤ} (hk : k ∉ frequencyBox (scalarScale s.val)) :
    BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
      smoothResolutionCutoff s.val (k 0 : ℝ) = 0 := by
  have hk0 : k 0 ∉ Finset.Icc (-((2:ℤ)^(s.val+1))) ((2:ℤ)^(s.val+1)) := by
    intro hmem
    apply hk
    simp only [frequencyBox, Fintype.mem_piFinset]
    intro i
    fin_cases i
    simpa [scalarScale] using hmem
  have hout : (2:ℝ)^(s.val+1) ≤ |((k 0 : ℤ) : ℝ)| := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hk0
    rcases hk0 with hlow | hhigh
    · have hc : ((k 0:ℤ):ℝ) < -((2:ℝ)^(s.val+1)) := by exact_mod_cast hlow
      have h := (show (2:ℝ)^(s.val+1) ≤ -((k 0:ℤ):ℝ) by linarith)
      exact h.trans (neg_le_abs _)
    · have hc : (2:ℝ)^(s.val+1) < ((k 0:ℤ):ℝ) := by exact_mod_cast hhigh
      exact hc.le.trans (le_abs_self _)
  exact BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock_eq_zero_of_two_pow_le_abs
    smoothResolutionCutoff s.val hout

private theorem admissibleBlockKernel_expand_common (N : ℕ) (s : Fin (N+1)) :
    admissibleBlockKernel smoothResolutionCutoff (scalarScale s.val) =
      torusFourierPolynomial (signedDyadicSupport N)
        (admissibleBlockSymbol smoothResolutionCutoff (scalarScale s.val)) := by
  apply ContinuousMap.ext
  intro x
  rw [admissibleBlockKernel]
  simp only [torusFourierPolynomial, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_subset (scalarScale_frequencyBox_subset N s)
  intro k hk hnot
  rw [admissibleBlockSymbol_eq_scalarBlock]
  simp [scalarBlock_zero_of_not_frequencyBox N s hnot]

/-- The signed kernel is exactly the finite Fourier polynomial with symbol
`Σ ε_s scalarBlock_s`; this identifies the actual smooth kernels with the
finite multiplier used in the L² estimate. -/
theorem signedDyadicKernel_eq_finiteKernel (N : ℕ)
    (ε : Fin (N+1) → ℝ) :
    signedDyadicKernel N ε =
      finiteKernel (signedDyadicSupport N) (signedDyadicSymbol N ε) := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [signedDyadicKernel, finiteKernel, torusFourierPolynomial,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [admissibleBlockKernel_expand_common]
  simp only [torusFourierPolynomial, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  have hswap := Finset.sum_comm
    (s := (Finset.univ : Finset (Fin (N+1))))
    (t := signedDyadicSupport N)
    (f := fun s k => (ε s : ℂ) *
      (admissibleBlockSymbol smoothResolutionCutoff (scalarScale s.val) k *
        UnitAddTorus.mFourier k x))
  calc
    _ = ∑ k ∈ signedDyadicSupport N,
        ∑ s ∈ (Finset.univ : Finset (Fin (N+1))),
          (ε s : ℂ) *
            (admissibleBlockSymbol smoothResolutionCutoff (scalarScale s.val) k *
              UnitAddTorus.mFourier k x) := by
          simpa using hswap
    _ = ∑ k ∈ signedDyadicSupport N,
        signedDyadicSymbol N ε k * UnitAddTorus.mFourier k x := by
          apply Finset.sum_congr rfl
          intro k hk
          simp_rw [admissibleBlockSymbol_eq_scalarBlock]
          have hfactor := Finset.sum_mul
            (Finset.univ : Finset (Fin (N+1)))
            (fun s => (ε s : ℂ) *
              (BrownianSharp.AlignmentPeriodicAdmissibleCutoff.scalarBlock
                smoothResolutionCutoff s.val (k 0 : ℝ) : ℂ))
            (UnitAddTorus.mFourier k x)
          simpa [signedDyadicSymbol, scalarScale, mul_assoc] using hfactor.symm

private theorem mFourier_sub_mul (k : Fin 1 → ℤ)
    (x y : UnitAddTorus (Fin 1)) :
    UnitAddTorus.mFourier k (x-y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  classical
  have hcoord : ∀ i : Fin 1,
      fourier (k i) ((x-y) i) = fourier (k i) (x i) * fourier (-k i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

private theorem measurePreserving_subLeft (x : UnitAddTorus (Fin 1)) :
    MeasurePreserving (fun y : UnitAddTorus (Fin 1) => x-y)
      (volume : Measure (UnitAddTorus (Fin 1))) volume := by
  let μ : Measure (UnitAddTorus (Fin 1)) := volume
  letI : Measure.IsAddLeftInvariant μ := inferInstance
  have hneg : MeasurePreserving (fun y : UnitAddTorus (Fin 1) => -y) μ μ := by
    change MeasurePreserving (fun y : (Fin 1 → UnitAddCircle) => -y)
      (Measure.pi fun _ : Fin 1 => AddCircle.haarAddCircle)
      (Measure.pi fun _ : Fin 1 => AddCircle.haarAddCircle)
    exact measurePreserving_pi
      (fun _ : Fin 1 => AddCircle.haarAddCircle)
      (fun _ : Fin 1 => AddCircle.haarAddCircle)
      (fun i : Fin 1 => Measure.measurePreserving_neg AddCircle.haarAddCircle)
  have hadd : MeasurePreserving (fun y : UnitAddTorus (Fin 1) => x+y) μ μ :=
    measurePreserving_add_left μ x
  convert hadd.comp hneg using 1 <;> ext y <;> simp [sub_eq_add_neg]

/-- A finite trigonometric kernel convolved with an actual L² source is the
corresponding finite Fourier multiplier, pointwise for the chosen L²
representative. -/
theorem finiteKernel_L2_convolution_eq_multiplier
    (S : Finset (Fin 1 → ℤ)) (a : (Fin 1 → ℤ) → ℂ)
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1))))
    (x : UnitAddTorus (Fin 1)) :
    ∫ y : UnitAddTorus (Fin 1),
      finiteKernel S a y * g (x-y) ∂(volume : Measure (UnitAddTorus (Fin 1))) =
    torusFourierPolynomial S (fun k => a k * UnitAddTorus.mFourierCoeff g k) x := by
  classical
  let μ : Measure (UnitAddTorus (Fin 1)) := volume
  let hsub := measurePreserving_subLeft x
  have hgint : Integrable (fun y : UnitAddTorus (Fin 1) => g (x-y)) μ := by
    have hgi : Integrable (fun y : UnitAddTorus (Fin 1) => g y) μ :=
      (Lp.memLp g).integrable (by norm_num)
    exact (hsub.integrable_comp_emb (Homeomorph.subLeft x).measurableEmbedding).mpr hgi
  have hmodeInt (k : Fin 1 → ℤ) :
      Integrable (fun y : UnitAddTorus (Fin 1) =>
        UnitAddTorus.mFourier k y * g (x-y)) μ := by
    have hchar : AEStronglyMeasurable (fun y : UnitAddTorus (Fin 1) =>
        UnitAddTorus.mFourier k y) μ := (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable
    have hbound : ∀ᵐ y ∂μ, ‖UnitAddTorus.mFourier k y‖ ≤ 1 := by
      filter_upwards [] with y
      calc
        ‖UnitAddTorus.mFourier k y‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
          (UnitAddTorus.mFourier k).norm_coe_le_norm y
        _ = 1 := UnitAddTorus.mFourier_norm
    have hmul := hgint.bdd_mul hchar hbound
    simpa [mul_assoc] using hmul
  have htermInt (k : Fin 1 → ℤ) :
      Integrable (fun y : UnitAddTorus (Fin 1) =>
        (a k * UnitAddTorus.mFourier k y) * g (x-y)) μ := by
    simpa [mul_assoc] using (hmodeInt k).const_mul (a k)
  have hchange (k : Fin 1 → ℤ) :
      ∫ y : UnitAddTorus (Fin 1),
          (a k * UnitAddTorus.mFourier k y) * g (x-y) ∂μ =
        ∫ z : UnitAddTorus (Fin 1),
          (a k * UnitAddTorus.mFourier k (x-z)) * g z ∂μ := by
    let F : UnitAddTorus (Fin 1) → ℂ := fun y =>
      (a k * UnitAddTorus.mFourier k y) * g (x-y)
    have hcomp := hsub.integral_comp (Homeomorph.subLeft x).measurableEmbedding F
    calc
      _ = ∫ z : UnitAddTorus (Fin 1), F (x-z) ∂μ := hcomp.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp [F, sub_sub_cancel]
  have hmode (k : Fin 1 → ℤ) :
      a k * UnitAddTorus.mFourierCoeff g k * UnitAddTorus.mFourier k x =
        ∫ y : UnitAddTorus (Fin 1),
          (a k * UnitAddTorus.mFourier k y) * g (x-y) ∂μ := by
    calc
      _ = (a k * UnitAddTorus.mFourier k x) *
          (∫ z : UnitAddTorus (Fin 1),
            UnitAddTorus.mFourier (-k) z * g z ∂μ) := by
            rw [UnitAddTorus.mFourierCoeff]
            simp only [smul_eq_mul]
            ring
      _ = ∫ z : UnitAddTorus (Fin 1),
          (a k * UnitAddTorus.mFourier k x) *
            (UnitAddTorus.mFourier (-k) z * g z) ∂μ := by
            rw [integral_const_mul]
      _ = ∫ y : UnitAddTorus (Fin 1),
          (a k * UnitAddTorus.mFourier k y) * g (x-y) ∂μ := by
            symm
            calc
              _ = ∫ z : UnitAddTorus (Fin 1),
                  (a k * UnitAddTorus.mFourier k (x-z)) * g z ∂μ := hchange k
              _ = ∫ z : UnitAddTorus (Fin 1),
                  (a k * UnitAddTorus.mFourier k x) *
                    (UnitAddTorus.mFourier (-k) z * g z) ∂μ := by
                    apply integral_congr_ae
                    filter_upwards [] with z
                    rw [mFourier_sub_mul]
                    ring
  calc
    _ = ∫ y : UnitAddTorus (Fin 1),
          (∑ k ∈ S, (a k * UnitAddTorus.mFourier k y) * g (x-y)) ∂μ := by
          congr 1
          funext y
          simp [finiteKernel, torusFourierPolynomial,
            ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
            Finset.sum_mul]
    _ = ∑ k ∈ S, ∫ y : UnitAddTorus (Fin 1),
          (a k * UnitAddTorus.mFourier k y) * g (x-y) ∂μ := by
          apply integral_finsetSum
          intro k hk
          exact htermInt k
    _ = ∑ k ∈ S,
          a k * UnitAddTorus.mFourierCoeff g k * UnitAddTorus.mFourier k x := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (hmode k).symm
    _ = torusFourierPolynomial S
          (fun k => a k * UnitAddTorus.mFourierCoeff g k) x := by
          simp [torusFourierPolynomial, ContinuousMap.sum_apply,
            ContinuousMap.smul_apply, smul_eq_mul]

/-- The actual signed convolution output for an L² source is the finite
multiplier polynomial and therefore has the depth-uniform L² bound. -/
theorem signedDyadicConvolutionFunction_eq_multiplier (N : ℕ)
    (ε : Fin (N+1) → ℝ)
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1))))
    (x : UnitAddTorus (Fin 1)) :
    signedDyadicConvolutionFunction N ε g x =
      signedDyadicL2MultiplierFunction N ε g x := by
  rw [signedDyadicConvolutionFunction, signedDyadicKernel_eq_finiteKernel]
  exact finiteKernel_L2_convolution_eq_multiplier
    (signedDyadicSupport N) (signedDyadicSymbol N ε) g x

/-- The ENNReal energy of the actual representative of an `L²` function is
the square of its `Lp` norm. -/
theorem lintegral_enorm_sq_eq_norm_sq
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1)))) :
    ∫⁻ x : UnitAddTorus (Fin 1), ‖g x‖ₑ ^ (2 : ℝ) ∂volume =
      ENNReal.ofReal (‖g‖ ^ 2) := by
  have hae : AEStronglyMeasurable (fun x : UnitAddTorus (Fin 1) => g x) volume :=
    Lp.aestronglyMeasurable g
  have hE : eLpNorm (fun x : UnitAddTorus (Fin 1) => g x)
      (2 : ℝ≥0∞) volume = eLpNorm g (2 : ℝ≥0∞) volume := by
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    rfl
  calc
    _ = eLpNorm' (fun x : UnitAddTorus (Fin 1) => g x) 2 volume ^ (2 : ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := fun x => g x)
        (q := 2) (μ := volume) (by norm_num)
    _ = eLpNorm g (2 : ℝ≥0∞) volume ^ (2 : ℝ) := by
      have h' : eLpNorm' (fun x : UnitAddTorus (Fin 1) => g x) 2 volume =
          eLpNorm (fun x : UnitAddTorus (Fin 1) => g x) (2 : ℝ≥0∞) volume := by
        simpa using (eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hae).symm
      rw [h', hE]
    _ = ‖g‖ₑ ^ (2 : ℝ) := by rw [Lp.enorm_def]
    _ = ENNReal.ofReal (‖g‖ ^ 2) := by
      simp [ENNReal.ofReal_pow]

/-- The actual signed smooth-kernel convolution has a strong `L²` bound
uniform in the number of dyadic scales and the signs. The constant is one. -/
theorem signedDyadicConvolution_lintegral_sq_le (N : ℕ)
    (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    (g : Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin 1)))) :
    ∫⁻ x : UnitAddTorus (Fin 1),
      ENNReal.ofReal (‖signedDyadicConvolutionFunction N ε g x‖ ^ 2) ∂volume ≤
      ∫⁻ x : UnitAddTorus (Fin 1), ENNReal.ofReal (‖g x‖ ^ 2) ∂volume := by
  have hconv (x : UnitAddTorus (Fin 1)) :=
    signedDyadicConvolutionFunction_eq_multiplier N ε g x
  have hmult_ae : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin 1))),
      signedDyadicL2MultiplierFunction N ε g x = signedDyadicL2Multiplier N ε g x := by
    change torusFourierPolynomial (signedDyadicSupport N)
        (fun k => signedDyadicSymbol N ε k * UnitAddTorus.mFourierCoeff g k) =ᵐ[volume]
      (torusFourierPolynomial (signedDyadicSupport N)
        (fun k => signedDyadicSymbol N ε k * UnitAddTorus.mFourierCoeff g k)).toLp
          2 volume ℂ
    exact (ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) (μ:=volume)
      (torusFourierPolynomial (signedDyadicSupport N)
        (fun k => signedDyadicSymbol N ε k * UnitAddTorus.mFourierCoeff g k))).symm
  have hleft :
      ∫⁻ x : UnitAddTorus (Fin 1),
        ENNReal.ofReal (‖signedDyadicConvolutionFunction N ε g x‖ ^ 2) ∂volume =
      ENNReal.ofReal (‖signedDyadicL2Multiplier N ε g‖ ^ 2) := by
    rw [lintegral_congr_ae]
    · exact lintegral_enorm_sq_eq_norm_sq (signedDyadicL2Multiplier N ε g)
    · filter_upwards [hmult_ae] with x hx
      rw [hconv x, hx]
      simp [ENNReal.ofReal_pow]
  have hright :
      ∫⁻ x : UnitAddTorus (Fin 1), ENNReal.ofReal (‖g x‖ ^ 2) ∂volume =
        ENNReal.ofReal (‖g‖ ^ 2) := by
    rw [← lintegral_enorm_sq_eq_norm_sq g]
    congr 1
    funext x
    simp [ENNReal.ofReal_pow]
  rw [hleft, hright]
  exact ENNReal.ofReal_le_ofReal
    (signedDyadicL2Multiplier_norm_sq_le N ε hε g)

end BrownianSharp.AlignmentPaperSignedKernelL2
