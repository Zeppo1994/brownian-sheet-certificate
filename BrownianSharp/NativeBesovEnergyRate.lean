import BrownianSharp.NativeLayerGeneralMean
import BrownianSharp.NativeEnergyRate

/-! Uniform scale normalization and the unconditional finite-theta periodic
Besov entropy conclusion for the actual native Gaussian layer. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BrownianSharp.NativeBesovEnergyRate

open BrownianSharp.NativeLayerGeneralMean
open BrownianSharp.NativeLayerThetaLow
open BrownianSharp.NativeLayerBudget
open BrownianSharp.LayerBlockVariance
open BrownianSharp.AtomicTensorFactorization
open BrownianSharp.PeriodicCover
open BrownianSharp.SmoothResolution
open BrownianSharp
open BrownianSharp.Torus

def nativeBesovRateConstant (K d : ℕ) (C p theta r : ℝ) : ℝ :=
  1 + (2^(max p theta) * gaussianAbsoluteMoment (max p theta))^(theta/max p theta) *
    (if theta ≤ 2 then
      (sourceNormalizedVarianceBudget C r K theta).toReal ^ d
     else
      (scalarLayerBudget C r K)^(d*(theta/2)))

theorem nativeBesovRateConstant_pos
    (K d : ℕ) (C p theta r : ℝ) (hp : 1 ≤ p) (htheta : 1 ≤ theta)
    (hK : 1 ≤ K) (hr : 0 ≤ r) (hgap : 2*r < 2*(K:ℝ)-1) :
    0 < nativeBesovRateConstant K d C p theta r := by
  unfold nativeBesovRateConstant
  have hq : 0 ≤ gaussianAbsoluteMoment (max p theta) :=
    gaussianAbsoluteMoment_nonneg _
  have hlow : 0 ≤ (sourceNormalizedVarianceBudget C r K theta).toReal := by positivity
  have hB : 0 < scalarLayerBudget C r K := by
    unfold scalarLayerBudget scalarTailRatio
    have hqpow : (2:ℝ)^(2*r-(2*(K:ℝ)-1)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      linarith
    have hd : 0 < 1-(2:ℝ)^(2*r-(2*(K:ℝ)-1)) := sub_pos.mpr hqpow
    positivity
  have hbase : 0 ≤ 2^(max p theta) * gaussianAbsoluteMoment (max p theta) := by
    positivity
  split_ifs <;> positivity

private theorem nativeClassScale_theta_pow
    {d n : ℕ} (hd : 2 ≤ d) (r theta : ℝ) (htheta : 1 ≤ theta) :
    nativeClassNormScale d n r theta⁻¹ ^ theta =
      (2:ℝ)^(r*theta*(n:ℝ)) * hyperbolicCount d n := by
  have hH : 0 < hyperbolicCount d n := hyperbolicCount_pos (by omega)
  have htheta0 : 0 < theta := by linarith
  unfold nativeClassNormScale
  change ((2:ℝ)^(r*(n:ℝ)) * hyperbolicCount d n ^ theta⁻¹)^theta = _
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hH.le _)]
  have hpow2 : ((2:ℝ)^(r*(n:ℝ)))^theta = (2:ℝ)^(r*theta*(n:ℝ)) := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2)]
    congr 1 <;> ring
  have hpowH : (hyperbolicCount d n ^ theta⁻¹)^theta = hyperbolicCount d n := by
    rw [← Real.rpow_mul hH.le]
    have hmul : theta⁻¹ * theta = 1 := by field_simp [ne_of_gt htheta0]
    rw [hmul, Real.rpow_one]
  rw [hpow2, hpowH]

/-- The geometric variance budget supplies the exact normalized mean estimate
required by `NativeEnergyRate`, uniformly for every native grade. -/
theorem native_smoothBesov_general_expected_energy_rate
    {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p theta r : ℝ) (hp : 1 < p) (htheta : 1 ≤ theta) (hr : 0 < r)
    (hgap : 2*r < 2*(K:ℝ)-1) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ,
      (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
        smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
          (gaussianSynthesis (nativeFinAtoms d n) z)
        ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      ENNReal.ofReal (A*(nativeClassNormScale d n r theta⁻¹)^theta) := by
  let A := nativeBesovRateConstant K d C p theta r
  have hA : 0 < A := by
    dsimp [A]
    exact nativeBesovRateConstant_pos K d C p theta r (by linarith) htheta hK hr.le hgap
  refine ⟨A,hA,?_⟩
  intro n
  let q : ℝ := max p theta
  let D : ℝ := (2^q * gaussianAbsoluteMoment q)^(theta/q)
  have hp1 : 1 ≤ p := le_of_lt hp
  have henergy := nativeSmoothBesov_general_expected_energy_le
    d n K hK C hC p theta r hp1 htheta hr.le hgap
  have hD : 0 ≤ D := by
    dsimp [D,q]
    exact Real.rpow_nonneg (mul_nonneg (by positivity)
      (gaussianAbsoluteMoment_nonneg _)) _
  have hshapeCard : (Fintype.card (Shape d n) : ℝ) = hyperbolicCount d n := by
    unfold hyperbolicCount
    exact_mod_cast shape_card d n (by omega)
  have hscale := nativeClassScale_theta_pow (d:=d) (n:=n) hd r theta htheta
  by_cases hsmall : theta ≤ 2
  · have hbudgetFinite := sourceNormalizedVarianceBudget_ne_top (C:=C) hK hr.le hgap htheta
    have hbudgetPow :
        sourceNormalizedVarianceBudget C r K theta ^ d =
          ENNReal.ofReal ((sourceNormalizedVarianceBudget C r K theta).toReal ^ d) := by
      calc
        _ = (ENNReal.ofReal (sourceNormalizedVarianceBudget C r K theta).toReal)^d := by
          rw [ENNReal.ofReal_toReal hbudgetFinite]
        _ = _ := by
          rw [ENNReal.ofReal_pow (ENNReal.toReal_nonneg : 0 ≤
            (sourceNormalizedVarianceBudget C r K theta).toReal)]
    have hbound : nativeThetaVarianceBound d n K C r theta =
        ENNReal.ofReal ((Fintype.card (Shape d n) : ℝ) *
          (2:ℝ)^(r*theta*(n:ℝ)) *
          (sourceNormalizedVarianceBudget C r K theta).toReal^d) := by
      unfold nativeThetaVarianceBound
      rw [if_pos hsmall, hbudgetPow]
      rw [show (Fintype.card (Shape d n) : ℝ≥0∞) =
        ENNReal.ofReal (Fintype.card (Shape d n) : ℝ) by norm_num]
      calc
        _ = ENNReal.ofReal (Fintype.card (Shape d n) : ℝ) *
            ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ)) *
              (sourceNormalizedVarianceBudget C r K theta).toReal^d) := by
                rw [← ENNReal.ofReal_mul (by positivity :
                  0 ≤ (2:ℝ)^(r*theta*(n:ℝ)))]
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity :
            0 ≤ (Fintype.card (Shape d n) : ℝ))]
          congr 1 <;> ring
    have hreal : D * ((Fintype.card (Shape d n) : ℝ) *
        (2:ℝ)^(r*theta*(n:ℝ)) *
        (sourceNormalizedVarianceBudget C r K theta).toReal^d) ≤
        A * (nativeClassNormScale d n r theta⁻¹)^theta := by
      dsimp [A,nativeBesovRateConstant,D,q]
      rw [hshapeCard,hscale]
      have hbud : 0 ≤ (sourceNormalizedVarianceBudget C r K theta).toReal^d := by positivity
      have hHpos : 0 < hyperbolicCount d n := hyperbolicCount_pos (by omega)
      have hterm : 0 ≤ (2:ℝ)^(r*theta*(n:ℝ)) := by positivity
      have hcoefle : D*(sourceNormalizedVarianceBudget C r K theta).toReal^d ≤
          1+D*(sourceNormalizedVarianceBudget C r K theta).toReal^d := by linarith
      have hweight : 0 ≤ hyperbolicCount d n * (2:ℝ)^(r*theta*(n:ℝ)) :=
        mul_nonneg hHpos.le hterm
      have hcoefle' : (2 ^ max p theta * gaussianAbsoluteMoment (max p theta)) ^
          (theta / max p theta) * (sourceNormalizedVarianceBudget C r K theta).toReal^d ≤
          1 + (2 ^ max p theta * gaussianAbsoluteMoment (max p theta)) ^
            (theta / max p theta) * (sourceNormalizedVarianceBudget C r K theta).toReal^d := by
        simpa [D,q] using hcoefle
      simp only [if_pos hsmall]
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoefle') hweight]
    calc
      _ ≤ ENNReal.ofReal D * nativeThetaVarianceBound d n K C r theta := henergy
      _ = ENNReal.ofReal (D * ((Fintype.card (Shape d n) : ℝ) *
            (2:ℝ)^(r*theta*(n:ℝ)) *
            (sourceNormalizedVarianceBudget C r K theta).toReal^d)) := by
          rw [hbound]
          rw [← ENNReal.ofReal_mul hD]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  · have hlarge : 2 ≤ theta := le_of_not_ge hsmall
    have hB : 0 < scalarLayerBudget C r K := by
      unfold scalarLayerBudget scalarTailRatio
      have hqpow : (2:ℝ)^(2*r-(2*(K:ℝ)-1)) < 1 := by
        apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        linarith
      have hd' : 0 < 1-(2:ℝ)^(2*r-(2*(K:ℝ)-1)) := sub_pos.mpr hqpow
      positivity
    let u : ℝ := theta/2
    have hpow : (scalarLayerBudget C r K ^ d *
        (2:ℝ)^(2*r*(n:ℝ)))^u =
        scalarLayerBudget C r K^(d*u) * (2:ℝ)^(r*theta*(n:ℝ)) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_natCast_mul hB.le d u]
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2)]
      all_goals (dsimp [u]; ring)
    have hbound : nativeThetaVarianceBound d n K C r theta =
        ENNReal.ofReal ((Fintype.card (Shape d n) : ℝ) *
          scalarLayerBudget C r K^(d*u) *
          (2:ℝ)^(r*theta*(n:ℝ))) := by
      unfold nativeThetaVarianceBound
      rw [if_neg hsmall]
      rw [show (Fintype.card (Shape d n) : ℝ≥0∞) =
        ENNReal.ofReal (Fintype.card (Shape d n) : ℝ) by norm_num]
      rw [show theta / 2 = u by rfl, hpow]
      calc
        _ = ENNReal.ofReal (Fintype.card (Shape d n) : ℝ) *
            ENNReal.ofReal (scalarLayerBudget C r K^(d*u) *
              (2:ℝ)^(r*theta*(n:ℝ))) := by rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity :
            0 ≤ (Fintype.card (Shape d n) : ℝ))]
          congr 1 <;> ring
    have hreal : D * ((Fintype.card (Shape d n) : ℝ) *
        scalarLayerBudget C r K^(d*u) * (2:ℝ)^(r*theta*(n:ℝ))) ≤
        A * (nativeClassNormScale d n r theta⁻¹)^theta := by
      dsimp [A,nativeBesovRateConstant,D,q]
      rw [hshapeCard,hscale]
      have hHpos : 0 < hyperbolicCount d n := hyperbolicCount_pos (by omega)
      have hcoefle : D*scalarLayerBudget C r K^(d*u) ≤
          1+D*scalarLayerBudget C r K^(d*u) := by linarith
      have hweight : 0 ≤ hyperbolicCount d n * (2:ℝ)^(r*theta*(n:ℝ)) := by positivity
      have hcoefle' : (2 ^ max p theta * gaussianAbsoluteMoment (max p theta)) ^
          (theta / max p theta) * scalarLayerBudget C r K^(d*u) ≤
          1 + (2 ^ max p theta * gaussianAbsoluteMoment (max p theta)) ^
            (theta / max p theta) * scalarLayerBudget C r K^(d*u) := by
        simpa [D,q] using hcoefle
      simp only [if_neg hsmall]
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoefle') hweight]
    calc
      _ ≤ ENNReal.ofReal D * nativeThetaVarianceBound d n K C r theta := henergy
      _ = ENNReal.ofReal (D * ((Fintype.card (Shape d n) : ℝ) *
            scalarLayerBudget C r K^(d*u) *
            (2:ℝ)^(r*theta*(n:ℝ)))) := by
          rw [hbound]
          rw [← ENNReal.ofReal_mul hD]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- Unconditional finite-theta periodic Besov entropy at the manuscript's
native normalization, for every finite `p>1`, `theta≥1`, and `r>0`. -/
theorem periodicBesov_entropy_of_actual_native_energy
    {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p theta r : ℝ) (hp : 1 < p) (htheta : 1 ≤ theta) (hr : 0 < r)
    (hgap : 2*r < 2*(K:ℝ)-1) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        ((r+1/2-theta⁻¹)*((d-1:ℕ):ℝ)+1/2)) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p)
            r (ENNReal.ofReal theta) f} := by
  obtain ⟨A,hA,hmean⟩ := native_smoothBesov_general_expected_energy_rate
    hd hK C hC p theta r hp htheta hr hgap
  have hp0 : 0 < p := by linarith
  exact BrownianSharp.periodicBesov_entropy_of_native_expected_energy_rate
    hd p theta r A hp0 htheta hr hA hmean

end BrownianSharp.NativeBesovEnergyRate
