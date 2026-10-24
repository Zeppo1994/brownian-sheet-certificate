import BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
import BrownianSharp.AlignmentFiniteFourierMultiplierConvolution
import BrownianSharp.AlignmentPeriodicCutoffClasses
import BrownianSharp.AlignmentCountableFiniteOverlapRpow
import BrownianSharp.AlignmentContinuousPointwiseLpTop
import BrownianSharp.AlignmentPeriodicCutoffTransferStatement
import BrownianSharp.AlignmentPeriodicBesovBallRescaling
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
open MeasureTheory
open Classical
open scoped BigOperators ENNReal
open UnitAddTorus

namespace BrownianSharp.AlignmentPeriodicCutoffYoung

open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.AlignmentFiniteFourierMultiplierConvolution
open BrownianSharp.AlignmentPeriodicCutoffClasses


private def phiSymbol {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) (k : Fin d → ℤ) : ℂ :=
  ∏ i, (scalarBlock φ (s i) (k i : ℝ) : ℂ)

private def maxFrequencyBox {d : ℕ} (s t : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  SmoothResolution.frequencyBox (fun i => max (s i) (t i))


private theorem phiSymbol_eq_zero_of_not_mem_box {d : ℕ}
    (φ : AdmissibleCutoff) (s : Fin d → ℕ) {k : Fin d → ℤ}
    (hk : k ∉ SmoothResolution.frequencyBox s) : phiSymbol φ s k = 0 := by
  classical
  have hnot : ¬ ∀ i, k i ∈ Finset.Icc
      (-((2:ℤ)^(s i+1))) ((2:ℤ)^(s i+1)) := by
    simpa [SmoothResolution.frequencyBox] using hk
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hout : (2:ℝ)^(s i+1) ≤ |(k i:ℝ)| := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · have h : (k i:ℝ) < -((2:ℝ)^(s i+1)) := by exact_mod_cast hi
      exact (by linarith : (2:ℝ)^(s i+1) ≤ -(k i:ℝ)).trans (neg_le_abs _)
    · have h : (2:ℝ)^(s i+1) < (k i:ℝ) := by exact_mod_cast hi
      exact h.le.trans (le_abs_self _)
  have hz := scalarBlock_eq_zero_of_two_pow_le_abs φ (s i) hout
  unfold phiSymbol
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by exact_mod_cast hz)

set_option maxHeartbeats 600000 in
theorem finiteKernel_phi_eq_admissibleBlockKernel {d : ℕ}
    (φ : AdmissibleCutoff) (s t : Fin d → ℕ) :
    finiteKernel (maxFrequencyBox s t) (phiSymbol φ s) =
      admissibleBlockKernel φ s := by
  classical
  apply ContinuousMap.ext
  intro x
  change torusFourierPolynomial (maxFrequencyBox s t) (phiSymbol φ s) x =
    torusFourierPolynomial (SmoothResolution.frequencyBox s)
      (admissibleBlockSymbol φ s) x
  rw [BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply,
    BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply]
  have hsub : SmoothResolution.frequencyBox s ⊆ maxFrequencyBox s t := by
    intro k hk
    apply Fintype.mem_piFinset.mpr
    intro i
    have hkIcc : ∀ j, k j ∈ Finset.Icc
        (-((2:ℤ)^(s j+1))) ((2:ℤ)^(s j+1)) := by
      simpa [SmoothResolution.frequencyBox] using hk
    have hi := hkIcc i
    simp only [Finset.mem_Icc] at hi ⊢
    constructor
    · have hp : (2:ℝ)^(s i+1) ≤ (2:ℝ)^(max (s i) (t i)+1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hp' : (2:ℤ)^(s i+1) ≤ (2:ℤ)^(max (s i) (t i)+1) := by
        exact_mod_cast hp
      exact le_trans (neg_le_neg hp') hi.1
    · have hp : (2:ℝ)^(s i+1) ≤ (2:ℝ)^(max (s i) (t i)+1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hp' : (2:ℤ)^(s i+1) ≤ (2:ℤ)^(max (s i) (t i)+1) := by
        exact_mod_cast hp
      exact le_trans hi.2 hp'
  change (∑ k ∈ maxFrequencyBox s t, phiSymbol φ s k * UnitAddTorus.mFourier k x) =
    ∑ k ∈ SmoothResolution.frequencyBox s,
      phiSymbol φ s k * UnitAddTorus.mFourier k x
  symm
  apply Finset.sum_subset hsub
  intro k hk hknot
  rw [phiSymbol_eq_zero_of_not_mem_box φ s hknot]
  simp

theorem admissibleCrossBlock_eq_complexFiniteMultiplier {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d) :
    admissibleCrossBlock φ ψ s t f =
      complexFiniteMultiplier (maxFrequencyBox s t) (phiSymbol φ s)
        (admissibleBlock ψ t f) := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [admissibleCrossBlock,
    BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply,
    complexFiniteMultiplier, torusFourierPolynomial,
    ContinuousMap.coe_mk, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, maxFrequencyBox, phiSymbol]
  apply Finset.sum_congr rfl
  intro k hk
  rw [admissibleBlock_coefficient]
  simp only [admissibleCrossTensorSymbol]
  rw [Finset.prod_mul_distrib]
  ring

theorem admissibleCrossBlock_eq_convolution {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d)
    (x : UnitAddTorus (Fin d)) :
    admissibleCrossBlock φ ψ s t f x =
      ∫ y : UnitAddTorus (Fin d),
        finiteKernel (maxFrequencyBox s t) (phiSymbol φ s) y *
          admissibleBlock ψ t f (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  rw [admissibleCrossBlock_eq_complexFiniteMultiplier]
  exact complexFiniteMultiplier_eq_kernel_convolution _ _ _ _


theorem admissibleCrossBlock_eq_admissibleKernel_convolution {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d)
    (x : UnitAddTorus (Fin d)) :
    admissibleCrossBlock φ ψ s t f x =
      ∫ y : UnitAddTorus (Fin d),
        admissibleBlockKernel φ s y * admissibleBlock ψ t f (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  rw [admissibleCrossBlock_eq_convolution]
  simp_rw [finiteKernel_phi_eq_admissibleBlockKernel]

private theorem admissibleBlockKernel_l1_uniform {d : ℕ}
    (φ : AdmissibleCutoff) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d :=
  exists_admissibleBlockKernel_uniform_L1_bound φ

theorem admissibleCrossBlock_sup_le {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d)
    (x : UnitAddTorus (Fin d)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ‖admissibleCrossBlock φ ψ s t f x‖ ≤ L ^ d * ‖admissibleBlock ψ t f‖ := by
  obtain ⟨L,hL,hK⟩ := admissibleBlockKernel_l1_uniform φ
  refine ⟨L,hL,?_⟩
  have hyoung := convolution_sup_bound_of_eq
    (admissibleBlockKernel φ s) (admissibleBlock ψ t f)
    (admissibleCrossBlock φ ψ s t f)
    (fun x => admissibleCrossBlock_eq_admissibleKernel_convolution φ ψ s t f x)
  have hpoint := hyoung x
  have hnorm : (∫ y : UnitAddTorus (Fin d),
      ‖admissibleBlockKernel φ s y‖
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d := hK s
  exact hpoint.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

theorem admissibleCrossBlock_eLpNorm_top_le_of_kernel_bound {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d)
    (L : ℝ) (hL : 0 ≤ L)
    (hK : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d) :
    eLpNorm (admissibleCrossBlock φ ψ s t f) ⊤
      (volume : Measure (UnitAddTorus (Fin d))) ≤
      ENNReal.ofReal (L ^ d) * eLpNorm (admissibleBlock ψ t f) ⊤
        (volume : Measure (UnitAddTorus (Fin d))) := by
  let g := admissibleCrossBlock φ ψ s t f
  let u := admissibleBlock ψ t f
  have hyoung := convolution_sup_bound_of_eq (admissibleBlockKernel φ s) u g
    (fun y => admissibleCrossBlock_eq_admissibleKernel_convolution φ ψ s t f y)
  have hsup : ‖g‖ ≤ L ^ d * ‖u‖ := by
    apply (ContinuousMap.norm_le g (mul_nonneg (by positivity) (norm_nonneg _))).2
    intro x
    exact (hyoung x).trans
      (mul_le_mul_of_nonneg_right (hK s) (norm_nonneg _))
  have hnormg := BrownianSharp.AlignmentContinuousPointwiseLpTop.continuous_eLpNorm_top_eq_ofReal_norm
    (volume : Measure (UnitAddTorus (Fin d))) g
  have hnormu := BrownianSharp.AlignmentContinuousPointwiseLpTop.continuous_eLpNorm_top_eq_ofReal_norm
    (volume : Measure (UnitAddTorus (Fin d))) u
  rw [hnormg, hnormu]
  calc
    ENNReal.ofReal ‖g‖ ≤ ENNReal.ofReal (L ^ d * ‖u‖) :=
      ENNReal.ofReal_le_ofReal hsup
    _ = ENNReal.ofReal (L ^ d) * ENNReal.ofReal ‖u‖ :=
      ENNReal.ofReal_mul (by positivity)


private theorem eLpNorm_eq_integral_root {d : ℕ}
    (f : C(UnitAddTorus (Fin d), ℂ)) (p : ℝ) (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) =
      ENNReal.ofReal ((∫ x : UnitAddTorus (Fin d), ‖f x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ (1 / p)) := by
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  have hcircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have hmeasure : (volume : Measure (UnitAddTorus (Fin d))) = μ := by
    change Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)) = μ
    rw [hcircle]
  rw [hmeasure]
  have hmem : MemLp f (ENNReal.ofReal p) μ := by
    apply MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    filter_upwards [] with x
    exact f.norm_coe_le_norm x
  have hnorm := lpNorm_eq_integral_norm_rpow_toReal
    (f := f) (p := ENNReal.ofReal p) (ENNReal.ofReal_pos.mpr hp).ne'
    (by simp : ENNReal.ofReal p ≠ ∞) (μ := μ) f.continuous.aestronglyMeasurable
  have hnorm' : lpNorm f (ENNReal.ofReal p) μ =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
    simpa [ENNReal.toReal_ofReal hp.le] using hnorm
  rw [← ofReal_lpNorm hmem, hnorm']

theorem admissibleCrossBlock_eLpNorm_le_of_kernel_bound {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d)
    (p L : ℝ) (hp : 1 ≤ p) (hL : 0 ≤ L)
    (hK : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d) :
      eLpNorm (admissibleCrossBlock φ ψ s t f) (ENNReal.ofReal p)
          (volume : Measure (UnitAddTorus (Fin d))) ≤
        ENNReal.ofReal (L ^ d) *
          eLpNorm (admissibleBlock ψ t f) (ENNReal.ofReal p)
            (volume : Measure (UnitAddTorus (Fin d))) := by
  let g := admissibleCrossBlock φ ψ s t f
  let u := admissibleBlock ψ t f
  have hyoung := convolution_Lp_bound_of_eq (admissibleBlockKernel φ s) u g p hp
    (fun x => admissibleCrossBlock_eq_admissibleKernel_convolution φ ψ s t f x)
  have hKpow : (∫ y : UnitAddTorus (Fin d),
      ‖admissibleBlockKernel φ s y‖
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p ≤ (L ^ d) ^ p := by
    exact Real.rpow_le_rpow (by positivity) (hK s) (by linarith)
  have hInt : (∫ x : UnitAddTorus (Fin d), ‖g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (L ^ d)^p * (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
    calc
      _ ≤ (∫ y : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
          (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := hyoung
      _ ≤ _ := mul_le_mul_of_nonneg_right hKpow (by positivity)
  have hIg : 0 ≤ ∫ x : UnitAddTorus (Fin d), ‖g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by positivity
  have hIu : 0 ≤ ∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by positivity
  rw [eLpNorm_eq_integral_root g p (by linarith),
    eLpNorm_eq_integral_root u p (by linarith)]
  have hroot := Real.rpow_le_rpow hIg hInt (by positivity : 0 ≤ 1/p)
  have hfactor : ((L ^ d)^p *
      (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))) ^ (1/p) =
      L ^ d * (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ (1/p) := by
    rw [Real.mul_rpow (by positivity) hIu]
    rw [← Real.rpow_mul (by positivity : 0 ≤ L ^ d)]
    have hpow : p * (1/p) = 1 := by field_simp
    rw [hpow, Real.rpow_one]
  rw [hfactor] at hroot
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ d)]
  exact ENNReal.ofReal_le_ofReal hroot

 theorem admissibleCrossBlock_eLpNorm_le {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ L : ℝ, 0 ≤ L ∧
      eLpNorm (admissibleCrossBlock φ ψ s t f) (ENNReal.ofReal p)
          (volume : Measure (UnitAddTorus (Fin d))) ≤
        ENNReal.ofReal (L ^ d) *
          eLpNorm (admissibleBlock ψ t f) (ENNReal.ofReal p)
            (volume : Measure (UnitAddTorus (Fin d))) := by
  obtain ⟨L,hL,hK⟩ := admissibleBlockKernel_l1_uniform φ
  refine ⟨L,hL,?_⟩
  let g := admissibleCrossBlock φ ψ s t f
  let u := admissibleBlock ψ t f
  have hyoung := convolution_Lp_bound_of_eq (admissibleBlockKernel φ s) u g p hp
    (fun x => admissibleCrossBlock_eq_admissibleKernel_convolution φ ψ s t f x)
  have hKpow : (∫ y : UnitAddTorus (Fin d),
      ‖admissibleBlockKernel φ s y‖
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p ≤ (L ^ d) ^ p := by
    exact Real.rpow_le_rpow (by positivity) (hK s) (by linarith)
  have hInt : (∫ x : UnitAddTorus (Fin d), ‖g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (L ^ d)^p * (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
    calc
      _ ≤ (∫ y : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
          (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := hyoung
      _ ≤ _ := mul_le_mul_of_nonneg_right hKpow (by positivity)
  have hIg : 0 ≤ ∫ x : UnitAddTorus (Fin d), ‖g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by positivity
  have hIu : 0 ≤ ∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by positivity
  rw [eLpNorm_eq_integral_root g p (by linarith),
    eLpNorm_eq_integral_root u p (by linarith)]
  have hroot := Real.rpow_le_rpow hIg hInt (by positivity : 0 ≤ 1/p)
  have hfactor : ((L ^ d)^p *
      (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))) ^ (1/p) =
      L ^ d * (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ (1/p) := by
    rw [Real.mul_rpow (by positivity) hIu]
    rw [← Real.rpow_mul (by positivity : 0 ≤ L ^ d)]
    have hpow : p * (1/p) = 1 := by field_simp
    rw [hpow, Real.rpow_one]
  rw [hfactor] at hroot
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ d)]
  exact ENNReal.ofReal_le_ofReal hroot




theorem admissibleCrossBlock_eLpNorm_le_of_kernel_bound_ennreal {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s t : Fin d → ℕ) (f : RealPeriodic d)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (L : ℝ) (hL : 0 ≤ L)
    (hK : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d) :
      eLpNorm (admissibleCrossBlock φ ψ s t f) p
          (volume : Measure (UnitAddTorus (Fin d))) ≤
        ENNReal.ofReal (L ^ d) *
          eLpNorm (admissibleBlock ψ t f) p
            (volume : Measure (UnitAddTorus (Fin d))) := by
  by_cases htop : p = ⊤
  · subst p
    exact admissibleCrossBlock_eLpNorm_top_le_of_kernel_bound φ ψ s t f L hL hK
  · have hcast : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal htop
    have hpR : 1 ≤ p.toReal := by
      have hh := (ENNReal.toReal_le_toReal ENNReal.one_ne_top htop).2 hp
      simpa using hh
    simpa only [hcast] using
      admissibleCrossBlock_eLpNorm_le_of_kernel_bound φ ψ s t f p.toReal L hpR hL hK

def closeIndices {d : ℕ} (s t : Fin d → ℕ) : Prop :=
  ∀ i, s i ≤ t i + 2 ∧ t i ≤ s i + 2

private def closeBox {d : ℕ} (s : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc (s i - 2) (s i + 2))

noncomputable def closeRow {d : ℕ} (s : Fin d → ℕ) : Finset (Fin d → ℕ) := by
  classical
  exact (closeBox s).filter (closeIndices s)

noncomputable def closeCol {d : ℕ} (t : Fin d → ℕ) : Finset (Fin d → ℕ) := by
  classical
  exact (closeBox t).filter (fun s => closeIndices s t)

private def localBox {d : ℕ} (s : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (s i + 3))

theorem closeRow_spec {d : ℕ} (s t : Fin d → ℕ) :
    t ∈ closeRow s ↔ closeIndices s t := by
  classical
  simp only [closeRow, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hi := h i
      simp only [Finset.mem_Icc]
      omega
    · exact h

theorem closeCol_spec {d : ℕ} (s t : Fin d → ℕ) :
    s ∈ closeCol t ↔ closeIndices s t := by
  classical
  simp only [closeCol, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      have hi := h i
      simp only [Finset.mem_Icc]
      omega
    · exact h

private theorem card_closeBox_le {d : ℕ} (s : Fin d → ℕ) :
    (closeBox s).card ≤ 5 ^ d := by
  classical
  rw [closeBox, Fintype.card_piFinset]
  calc
    ∏ i, (Finset.Icc (s i - 2) (s i + 2)).card ≤ ∏ _i : Fin d, 5 := by
      apply Finset.prod_le_prod
      · intro i hi
        rw [Nat.card_Icc]
        omega
    _ = 5 ^ d := by simp

private theorem closeRow_card_le {d : ℕ} (s : Fin d → ℕ) :
    (closeRow s).card ≤ 5 ^ d := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_closeBox_le s)

private theorem closeCol_card_le {d : ℕ} (t : Fin d → ℕ) :
    (closeCol t).card ≤ 5 ^ d := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_closeBox_le t)

private theorem closeRow_subset_localBox {d : ℕ}
    (s : Fin d → ℕ) : closeRow s ⊆ localBox s := by
  classical
  intro t ht
  rw [closeRow_spec] at ht
  apply Fintype.mem_piFinset.mpr
  intro i
  simp only [localBox, Finset.mem_range]
  have hi := (ht i).2
  omega

private theorem admissibleBlock_eq_closeRow_sum {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s : Fin d → ℕ) (f : RealPeriodic d) :
    admissibleBlock φ s f =
      ∑ t ∈ closeRow s, admissibleCrossBlock φ ψ s t f := by
  classical
  rw [admissibleBlock_eq_local_cross_sum]
  change (∑ t ∈ localBox s, admissibleCrossBlock φ ψ s t f) = _
  symm
  apply Finset.sum_subset (closeRow_subset_localBox s)
  intro t htLocal htNotClose
  rw [closeRow_spec] at htNotClose
  have htmem : t ∈ localBox s := htLocal
  have htcoord : ∀ i, t i ≤ s i + 2 := by
    intro i
    have hi := Fintype.mem_piFinset.mp htmem i
    simp only [localBox, Finset.mem_range] at hi
    omega
  have hbad : ¬ ∀ i, s i ≤ t i + 2 := by
    intro h
    exact htNotClose (fun i => ⟨h i, htcoord i⟩)
  obtain ⟨i, hi⟩ := not_forall.mp hbad
  have hgap : t i + 2 < s i := by omega
  exact admissibleCrossBlock_eq_zero_of_far_lower φ ψ s t i hgap f

private theorem dyadic_weight_close_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (s t : Fin d → ℕ) (hst : closeIndices s t) :
    (2:ℝ) ^ (r * ∑ i, (s i : ℝ)) ≤
      (2:ℝ) ^ (2 * r * d) * (2:ℝ) ^ (r * ∑ i, (t i : ℝ)) := by
  have hsum : (∑ i, (s i : ℝ)) ≤ (∑ i, (t i : ℝ)) + 2 * d := by
    calc
      (∑ i, (s i : ℝ)) ≤ ∑ i, ((t i : ℝ) + 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast (hst i).1
      _ = (∑ i, (t i : ℝ)) + 2 * d := by
        simp [Finset.sum_add_distrib]
        ring
  have hexp : r * (∑ i, (s i : ℝ)) ≤
      r * (∑ i, (t i : ℝ)) + 2 * r * d := by nlinarith
  calc
    (2:ℝ) ^ (r * ∑ i, (s i : ℝ)) ≤
        (2:ℝ) ^ (r * (∑ i, (t i : ℝ)) + 2 * r * d) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2:ℝ) ^ (2 * r * d) * (2:ℝ) ^ (r * ∑ i, (t i : ℝ)) := by
      rw [Real.rpow_add (by norm_num : 0 < (2:ℝ))]
      ring_nf

theorem admissibleBlock_eLpNorm_le_closeRow_sum {d : ℕ}
    (φ ψ : AdmissibleCutoff) (s : Fin d → ℕ) (f : RealPeriodic d)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (admissibleBlock φ s f) p (volume : Measure (UnitAddTorus (Fin d))) ≤
      ∑ t ∈ closeRow s,
        eLpNorm (admissibleCrossBlock φ ψ s t f) p
          (volume : Measure (UnitAddTorus (Fin d))) := by
  classical
  rw [admissibleBlock_eq_closeRow_sum φ ψ s f]
  have htri := MeasureTheory.eLpNorm_sum_le
    (μ := (volume : Measure (UnitAddTorus (Fin d))))
    (p := p) (f := fun t => admissibleCrossBlock φ ψ s t f)
    (s := closeRow s) hp
  have hsumfun : (∑ t ∈ closeRow s, fun x : UnitAddTorus (Fin d) =>
      admissibleCrossBlock φ ψ s t f x) =
      (fun x => ∑ t ∈ closeRow s, admissibleCrossBlock φ ψ s t f x) := by
    funext x
    simp
  have htri' : eLpNorm (fun x : UnitAddTorus (Fin d) =>
      ∑ t ∈ closeRow s, admissibleCrossBlock φ ψ s t f x) p
      (volume : Measure (UnitAddTorus (Fin d))) ≤
      ∑ t ∈ closeRow s, eLpNorm (admissibleCrossBlock φ ψ s t f) p
        (volume : Measure (UnitAddTorus (Fin d))) := by
    rw [← hsumfun]
    exact htri
  have hfun : (∑ t ∈ closeRow s, admissibleCrossBlock φ ψ s t f) =
      (fun x => ∑ t ∈ closeRow s, admissibleCrossBlock φ ψ s t f x) := by
    ext x
    simp
  rw [hfun]
  exact htri'

theorem weightedBlockNorm_le_neighbor_sum {d : ℕ}
    (φ ψ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ) (hp : 1 ≤ p) (hr : 0 ≤ r)
    (s : Fin d → ℕ) (f : RealPeriodic d) (L : ℝ) (hL : 0 ≤ L)
    (hK : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d) :
    weightedBlockNorm φ p r s f ≤
      ENNReal.ofReal ((L ^ d) * (2:ℝ)^(2*r*d)) *
        ∑' t : Fin d → ℕ,
          if closeIndices s t then weightedBlockNorm ψ p r t f else 0 := by
  classical
  let A : ℝ := L ^ d * (2:ℝ)^(2*r*d)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  unfold weightedBlockNorm
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) *
        ∑ t ∈ closeRow s, eLpNorm (admissibleCrossBlock φ ψ s t f)
          p (volume : Measure (UnitAddTorus (Fin d))) := by
      exact mul_le_mul_of_nonneg_left
        (admissibleBlock_eLpNorm_le_closeRow_sum φ ψ s f p hp) (by positivity)
    _ ≤ ∑ t ∈ closeRow s,
        ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) *
          eLpNorm (admissibleCrossBlock φ ψ s t f) p
            (volume : Measure (UnitAddTorus (Fin d))) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ closeRow s,
        ENNReal.ofReal A * weightedBlockNorm ψ p r t f := by
      apply Finset.sum_le_sum
      intro t ht
      have hclose : closeIndices s t := (closeRow_spec s t).1 ht
      have hw := dyadic_weight_close_le r hr s t hclose
      have hreal : (2:ℝ)^(r*∑ i,(s i:ℝ)) * L^d ≤
          A * (2:ℝ)^(r*∑ i,(t i:ℝ)) := by
        dsimp [A]
        calc
          _ ≤ ((2:ℝ)^(2*r*d) * (2:ℝ)^(r*∑ i,(t i:ℝ))) * L^d :=
            mul_le_mul_of_nonneg_right hw (by positivity)
          _ = A * (2:ℝ)^(r*∑ i,(t i:ℝ)) := by dsimp [A]; ring
      have hcross := admissibleCrossBlock_eLpNorm_le_of_kernel_bound_ennreal
        φ ψ s t f p hp L hL hK
      unfold weightedBlockNorm
      calc
        _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ)) * L^d) *
            eLpNorm (admissibleBlock ψ t f) (p)
              (volume : Measure (UnitAddTorus (Fin d))) := by
          calc
            _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) *
                (ENNReal.ofReal (L^d) * eLpNorm (admissibleBlock ψ t f)
                  p (volume : Measure (UnitAddTorus (Fin d)))) :=
              by exact mul_le_mul_of_nonneg_left hcross (by positivity)
            _ = (ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) *
                ENNReal.ofReal (L^d)) * eLpNorm (admissibleBlock ψ t f)
                  p (volume : Measure (UnitAddTorus (Fin d))) := by ac_rfl
            _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2:ℝ)^(r*∑ i,(s i:ℝ)))]
        _ ≤ _ := by
          have hcoef : ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) *
              ENNReal.ofReal (L^d) ≤ ENNReal.ofReal A *
                ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ))) := by
            calc
              _ = ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ)) * L^d) := by
                rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2:ℝ)^(r*∑ i,(s i:ℝ)))]
              _ ≤ ENNReal.ofReal (A * (2:ℝ)^(r*∑ i,(t i:ℝ))) :=
                ENNReal.ofReal_le_ofReal hreal
              _ = _ := by
                rw [ENNReal.ofReal_mul (by positivity : 0 ≤ A)]
          calc
            _ = (ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) * ENNReal.ofReal (L^d)) *
                eLpNorm (admissibleBlock ψ t f) (p)
                  (volume : Measure (UnitAddTorus (Fin d))) := by
              rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2:ℝ)^(r*∑ i,(s i:ℝ)))]
            _ ≤ (ENNReal.ofReal A * ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ)))) *
                eLpNorm (admissibleBlock ψ t f) (p)
                  (volume : Measure (UnitAddTorus (Fin d))) :=
              mul_le_mul_of_nonneg_right hcoef (by positivity)
            _ = _ := by ac_rfl
    _ ≤ ENNReal.ofReal A *
        ∑' t : Fin d → ℕ,
          if closeIndices s t then weightedBlockNorm ψ p r t f else 0 := by
      rw [← Finset.mul_sum]
      have hsum : (∑ t ∈ closeRow s,
          weightedBlockNorm ψ p r t f) =
        ∑' t : Fin d → ℕ,
          if closeIndices s t then weightedBlockNorm ψ p r t f else 0 := by
        calc
          _ = ∑ t ∈ closeRow s,
              (if closeIndices s t then weightedBlockNorm ψ p r t f else 0) := by
                apply Finset.sum_congr rfl
                intro t ht
                simp only [if_pos ((closeRow_spec s t).1 ht)]
          _ = _ := (tsum_eq_sum
            (f := fun t : Fin d → ℕ =>
              if closeIndices s t then weightedBlockNorm ψ p r t f else 0)
            (L := SummationFilter.unconditional (Fin d → ℕ)) (s := closeRow s)
            (fun t ht => if_neg (fun hct => ht ((closeRow_spec s t).2 hct)))).symm
      rw [hsum]


/-- Arbitrary admissible smooth cutoffs define equivalent mixed Besov balls.
The constant is obtained from the uniform tensor-kernel L¹ estimate and the
finite overlap of the dyadic frequency boxes. -/
theorem cutoffBesovScaleTransfer_certified :
    BrownianSharp.AlignmentPeriodicCutoffTransferStatement.BesovScaleTransferStatement := by
  intro φ ψ d p hp r hr theta htheta
  obtain ⟨L₀, hL₀, hKernel⟩ := admissibleBlockKernel_l1_uniform φ
  let L : ℝ := max 1 L₀
  have hL : 0 ≤ L := by positivity
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hL₀L : L₀ ≤ L := by dsimp [L]; exact le_max_right _ _
  have hKernel' : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖admissibleBlockKernel φ s x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d := by
    intro s
    exact (hKernel s).trans (by
      gcongr)
  let A : ℝ := L ^ d * (2:ℝ)^(2*r*d)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  let N : ℕ := 5 ^ d
  have hN : 0 < N := by dsimp [N]; positivity
  have htheta' : theta ≠ ⊤ → 1 ≤ theta.toReal := by
    intro htop
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top htop).2 htheta
  exact BrownianSharp.AlignmentPeriodicBesovBallRescaling.besovUnitBall_transfer_of_neighbor_comparison
    φ ψ p r theta closeIndices closeRow closeCol closeRow_spec closeCol_spec
    A hA N hN htheta' closeRow_card_le closeCol_card_le (by
      intro f s
      exact weightedBlockNorm_le_neighbor_sum φ ψ p r hp hr s f L hL hKernel')



end BrownianSharp.AlignmentPeriodicCutoffYoung
