import BrownianSharp.CameronMartin
import BrownianSharp.NativeProjection
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Finite Gaussian Cameron--Martin cutoff

This module isolates the coefficient-ball part of the direct Gaussian-cover route.  It proves
that a standard finite Gaussian coefficient vector lies in a Euclidean ball of radius
`2 * sqrt(D)` with probability at least `3/4`, and that any contraction from those coefficients
into the cube integrand space maps that ball, after normalization, into the manuscript's actual
restricted-cube Cameron--Martin image.  The confinement estimate and covering argument are
separate inputs in the surrounding certificate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace BrownianSharp.CameronMartinEntropy

/-- Squared Euclidean energy of a finite Gaussian coefficient vector. -/
def coefficientEnergy {κ : Type*} [Fintype κ] (x : κ → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- Synthesis of finitely many ambient integrands with scalar coefficients. -/
def coefficientIntegrandMap {κ : Type*} [Fintype κ] {d : ℕ}
    (basis : κ → CameronMartin.AmbientL2 d) :
    (κ → ℝ) →ₗ[ℝ] CameronMartin.AmbientL2 d where
  toFun x := ∑ i, x i • basis i
  map_add' x y := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [add_smul]
  map_smul' c x := by
    simp [Finset.smul_sum, smul_smul]

/-- An orthonormal family of cube integrands realizes coefficient energy exactly. -/
theorem coefficientIntegrandMap_norm_sq {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}
    (basis : κ → CameronMartin.AmbientL2 d)
    (horth : ∀ i j, ⟪basis i, basis j⟫ = if i = j then 1 else 0)
    (x : κ → ℝ) :
    ‖coefficientIntegrandMap basis x‖ ^ 2 = coefficientEnergy x := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(∑ i, x i • basis i), (∑ j, x j • basis j)⟫ = _
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  simp_rw [horth]
  simp [coefficientEnergy, pow_two]


private theorem standardGaussian_secondMoment :
    ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hvar : variance (id : ℝ → ℝ) (gaussianReal 0 1) = 1 := by simp
  have hmean : (gaussianReal 0 1)[id] = 0 := by simp
  have hmoment := variance_of_integral_eq_zero measurable_id'.aemeasurable hmean
  calc
    ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) =
        variance (id : ℝ → ℝ) (gaussianReal 0 1) := by simpa using hmoment.symm
    _ = 1 := hvar

/-- The expected squared Euclidean norm of a finite vector of independent standard Gaussians is
the dimension.  This is an exact product-Gaussian computation, not a moment hypothesis. -/
theorem standardGaussian_coefficientEnergy_integral (κ : Type*) [Fintype κ] :
    ∫ x : κ → ℝ, coefficientEnergy x ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
      (Fintype.card κ : ℝ) := by
  let μ : κ → Measure ℝ := fun _ => gaussianReal 0 1
  have hsq : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) := by
    have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := by
      exact memLp_id_gaussianReal' (2 : ℝ≥0∞) (by norm_num)
    simpa using hmem.integrable_sq
  have hcoord : ∀ i, ∫ x : κ → ℝ, (x i) ^ 2 ∂(Measure.pi μ) = 1 := by
    intro i
    calc
      ∫ x : κ → ℝ, (x i) ^ 2 ∂(Measure.pi μ) =
          ∫ t : ℝ, t ^ 2 ∂μ i :=
            integral_comp_eval (μ := μ) (i := i) (f := fun t : ℝ => t ^ 2)
              (by fun_prop)
      _ = 1 := by simpa [μ] using standardGaussian_secondMoment
  have hint : ∀ i ∈ (Finset.univ : Finset κ),
      Integrable (fun x : κ → ℝ => (x i) ^ 2) (Measure.pi μ) := by
    intro i hi
    exact integrable_comp_eval (μ := μ) (i := i) hsq
  change ∫ x : κ → ℝ, ∑ i, (x i) ^ 2 ∂(Measure.pi μ) = _
  rw [integral_finsetSum Finset.univ hint]
  simp [hcoord]

/-- The standard Gaussian coefficient cutoff retains at least three quarters of its mass.
The proof is Markov's inequality applied to the exact expected energy `D`. -/
theorem standardGaussian_coefficientCutoff_mass (κ : Type*) [Fintype κ] [Nonempty κ] :
    (3 / 4 : ℝ≥0∞) ≤
      (Measure.pi fun _ : κ => gaussianReal 0 1)
        {x | coefficientEnergy x ≤ 4 * (Fintype.card κ : ℝ)} := by
  let μ : Measure (κ → ℝ) := Measure.pi fun _ : κ => gaussianReal 0 1
  let D : ℝ := Fintype.card κ
  let bad : Set (κ → ℝ) := {x | 4 * D < coefficientEnergy x}
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty κ))
  have hEnergyInt : Integrable coefficientEnergy μ := by
    rw [show coefficientEnergy = fun x => ∑ i, (x i) ^ 2 by rfl]
    apply integrable_finsetSum Finset.univ
    intro i hi
    have hsq : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) := by
      have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := by
        exact memLp_id_gaussianReal' (2 : ℝ≥0∞) (by norm_num)
      simpa using hmem.integrable_sq
    exact integrable_comp_eval (μ := fun _ : κ => gaussianReal 0 1) (i := i) hsq
  have hEnergyMean : ∫ x, coefficientEnergy x ∂μ = D := by
    dsimp [μ, D]
    exact standardGaussian_coefficientEnergy_integral κ
  have hnonneg : 0 ≤ᵐ[μ] coefficientEnergy := ae_of_all _ (fun x => by
    dsimp [coefficientEnergy]
    positivity)
  let scaled : (κ → ℝ) → ℝ := fun x => coefficientEnergy x / (4 * D)
  have hscaledInt : Integrable scaled μ := by
    simpa [scaled, div_eq_mul_inv, mul_comm] using hEnergyInt.const_mul (4 * D)⁻¹
  have hscaledNonneg : 0 ≤ᵐ[μ] scaled := by
    filter_upwards [hnonneg] with x hx
    dsimp [scaled]
    rw [div_eq_mul_inv]
    exact mul_nonneg hx (inv_nonneg.mpr (le_of_lt (by positivity : 0 < 4 * D)))
  have hden : 0 < 4 * D := by positivity
  have hmarkov := hscaledInt.measure_le_integral hscaledNonneg
    (s := bad) (by
      intro x hx
      have hx' : 4 * D < coefficientEnergy x := hx
      dsimp [scaled]
      rw [one_le_div hden]
      linarith)
  have hscaledMean : ∫ x, scaled x ∂μ = 1 / 4 := by
    dsimp [scaled]
    rw [show (fun x => coefficientEnergy x / (4 * D)) =
      fun x => (4 * D)⁻¹ * coefficientEnergy x by
        funext x
        ring,
      integral_const_mul, hEnergyMean]
    dsimp [D]
    field_simp
  have hbad : μ bad ≤ (1 / 4 : ℝ≥0∞) := by
    calc
      μ bad ≤ ENNReal.ofReal (∫ x, scaled x ∂μ) := hmarkov
      _ = (1 / 4 : ℝ≥0∞) := by
        rw [hscaledMean]
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (4 : ℝ))]
        norm_num
  have hbadMeas : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    fun_prop [coefficientEnergy]
  have hgood : {x | coefficientEnergy x ≤ 4 * D} = badᶜ := by
    ext x
    simp [bad]
  have hbad_ne : μ bad ≠ ∞ := ne_of_lt (lt_of_le_of_lt hbad (by norm_num))
  have hbad_le_one : μ bad ≤ 1 := hbad.trans (by norm_num)
  rw [show (Measure.pi fun _ : κ => gaussianReal 0 1) = μ by rfl, hgood,
    measure_compl hbadMeas hbad_ne, measure_univ]
  apply (ENNReal.le_sub_iff_add_le_right hbad_ne hbad_le_one).2
  calc
    (3 / 4 : ℝ≥0∞) + μ bad ≤
        (3 / 4 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞) := by
      simpa [add_comm] using add_le_add_left hbad (3 / 4 : ℝ≥0∞)
    _ = (3 + 1) * (4 : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    _ = 4 * (4 : ℝ≥0∞)⁻¹ := by norm_num
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by simp)

/-- The coefficient Gaussian's normalized image in the actual restricted-cube integrand space.
`H` is the finite-dimensional Hilbert-space map into cube integrands. -/
noncomputable def normalizedCubeIntegrand {κ : Type*} [Fintype κ] {d : ℕ}
    (H : (κ → ℝ) →ₗ[ℝ] CameronMartin.UnitCubeL2 d) (x : κ → ℝ) :
    CameronMartin.UnitCubeL2 d :=
  ((2 * Real.sqrt (Fintype.card κ : ℝ))⁻¹) • H x

/-- On the coefficient cutoff, a Hilbert contraction maps the normalized vector into the unit
ball of the exact restricted-cube Cameron--Martin space. -/
theorem normalizedCubeIntegrand_mem_unitBall {κ : Type*} [Fintype κ] [Nonempty κ]
    {d : ℕ} (H : (κ → ℝ) →ₗ[ℝ] CameronMartin.UnitCubeL2 d)
    (hcontract : ∀ x, ‖H x‖ ^ 2 ≤ coefficientEnergy x)
    (x : κ → ℝ)
    (hcut : coefficientEnergy x ≤ 4 * (Fintype.card κ : ℝ)) :
    ‖normalizedCubeIntegrand H x‖ ≤ 1 := by
  have hD : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty κ))
  have hden : 0 < 2 * Real.sqrt (Fintype.card κ : ℝ) := by positivity
  have hnorm : ‖H x‖ ≤ 2 * Real.sqrt (Fintype.card κ : ℝ) := by
    have hsq : ‖H x‖ ^ 2 ≤ (2 * Real.sqrt (Fintype.card κ : ℝ)) ^ 2 := by
      calc
        ‖H x‖ ^ 2 ≤ coefficientEnergy x := hcontract x
        _ ≤ 4 * (Fintype.card κ : ℝ) := hcut
        _ = (2 * Real.sqrt (Fintype.card κ : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hD)]
          ring
    nlinarith [norm_nonneg (H x)]
  rw [normalizedCubeIntegrand, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hden)]
  calc
    (2 * Real.sqrt (Fintype.card κ : ℝ))⁻¹ * ‖H x‖ ≤
        (2 * Real.sqrt (Fintype.card κ : ℝ))⁻¹ *
          (2 * Real.sqrt (Fintype.card κ : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.mpr hden))
    _ = 1 := inv_mul_cancel₀ (by positivity)

/-- The ambient Brownian native layer as a finite orthonormal family in `L²(ℝ^d)`. -/
noncomputable def nativeAmbientBasis {d n : ℕ} (a : LayerIndex d n) :
    CameronMartin.AmbientL2 d := nativeLayerVector a

theorem nativeAmbientBasis_orthonormal {d n : ℕ} (a b : LayerIndex d n) :
    ⟪nativeAmbientBasis a, nativeAmbientBasis b⟫ = if a = b then 1 else 0 := by
  exact nativeLayerVector_orthonormal a b

/-- Native synthesis has exactly the coefficient energy, by the actual Haar Gram identity. -/
noncomputable def nativeAmbientSynthesis {d n : ℕ} :
    (LayerIndex d n → ℝ) →ₗ[ℝ] CameronMartin.AmbientL2 d :=
  coefficientIntegrandMap nativeAmbientBasis

theorem nativeAmbientSynthesis_norm_sq {d n : ℕ} (x : LayerIndex d n → ℝ) :
    ‖nativeAmbientSynthesis x‖ ^ 2 = coefficientEnergy x := by
  exact coefficientIntegrandMap_norm_sq nativeAmbientBasis
    (nativeAmbientBasis_orthonormal) x

/-- The ambient normalized synthesis from native Gaussian coefficients. -/
noncomputable def normalizedAmbientIntegrand {d n : ℕ}
    (x : LayerIndex d n → ℝ) : CameronMartin.AmbientL2 d :=
  ((2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ))⁻¹) •
    nativeAmbientSynthesis x

/-- A cutoff coefficient vector synthesizes a vector in the ambient unit ball. -/
theorem normalizedAmbientIntegrand_mem_unitBall {d n : ℕ}
    [Nonempty (LayerIndex d n)] (x : LayerIndex d n → ℝ)
    (hcut : coefficientEnergy x ≤ 4 * (Fintype.card (LayerIndex d n) : ℝ)) :
    ‖normalizedAmbientIntegrand x‖ ≤ 1 := by
  have hD : 0 < (Fintype.card (LayerIndex d n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (LayerIndex d n)))
  have hden : 0 < 2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ) := by positivity
  have hnormsq : ‖nativeAmbientSynthesis x‖ ^ 2 ≤
      (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) ^ 2 := by
    rw [nativeAmbientSynthesis_norm_sq]
    calc
      coefficientEnergy x ≤ 4 * (Fintype.card (LayerIndex d n) : ℝ) := hcut
      _ = (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hD)]
        ring
  have hnorm : ‖nativeAmbientSynthesis x‖ ≤
      2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ) := by
    nlinarith [norm_nonneg (nativeAmbientSynthesis x)]
  rw [normalizedAmbientIntegrand, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hden)]
  calc
    (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ))⁻¹ *
        ‖nativeAmbientSynthesis x‖ ≤ 1 := by
      calc
        _ ≤ (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ))⁻¹ *
            (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)) :=
          mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.mpr hden))
        _ = 1 := inv_mul_cancel₀ (by positivity)

/-- The native coefficient cutoff maps into the ambient `K_d`, hence also into the exact
restricted-cube image by the zero-extension/restriction equality of Cameron--Martin balls. -/
theorem nativeNormalizedPath_mem_KdUnitCube {d n : ℕ}
    [Nonempty (LayerIndex d n)] (x : LayerIndex d n → ℝ)
    (hcut : coefficientEnergy x ≤ 4 * (Fintype.card (LayerIndex d n) : ℝ)) :
    CameronMartin.anchoredIntegrationPath (normalizedAmbientIntegrand x) ∈
      CameronMartin.KdUnitCube d := by
  have hmem : CameronMartin.anchoredIntegrationPath (normalizedAmbientIntegrand x) ∈
      CameronMartin.Kd d := by
    exact ⟨normalizedAmbientIntegrand x,
      normalizedAmbientIntegrand_mem_unitBall x hcut, rfl⟩
  rw [← CameronMartin.KdUnitCube_eq_Kd d] at hmem
  exact hmem


end BrownianSharp.CameronMartinEntropy
