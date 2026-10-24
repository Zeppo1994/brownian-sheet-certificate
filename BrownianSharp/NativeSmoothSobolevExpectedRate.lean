import BrownianSharp.NativeSmoothSobolevHigherPRate
import BrownianSharp.NativeSmoothSobolevLowerPRate

/-! One all-`p>1` expected-energy estimate for the actual native layer.
The constant is chosen strictly positive to feed directly into the entropy
normalization theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BrownianSharp

open Torus PeriodicCover SmoothResolution NativeLayerBudget

/-- A positive rate constant dominating both Jensen regimes. -/
def nativeSmoothSobolevRateConstant (d K : ℕ) (C p r : ℝ) : ℝ :=
  1 + max
    ((4 * gaussianAbsoluteMoment 2 * scalarLayerBudget C r K ^ d) ^ (p / 2))
    ((4 * gaussianAbsoluteMoment p ^ (2 / p) * scalarLayerBudget C r K ^ d) ^ (p / 2))

theorem nativeSmoothSobolevRateConstant_pos (d K : ℕ) (C p r : ℝ)
    (hgap : 2 * r < 2 * (K : ℝ) - 1) :
    0 < nativeSmoothSobolevRateConstant d K C p r := by
  unfold nativeSmoothSobolevRateConstant
  have hbudget : 0 ≤ scalarLayerBudget C r K := by
    unfold scalarLayerBudget scalarTailRatio
    have hq : (2 : ℝ) ^ (2 * r - (2 * (K : ℝ) - 1)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      linarith
    positivity
  have hg2 : 0 ≤ gaussianAbsoluteMoment 2 := by
    unfold gaussianAbsoluteMoment
    exact integral_nonneg fun _ => by positivity
  have hgp : 0 ≤ gaussianAbsoluteMoment p := by
    unfold gaussianAbsoluteMoment
    exact integral_nonneg fun _ => by positivity
  have h1 : 0 ≤ (4 * gaussianAbsoluteMoment 2 * scalarLayerBudget C r K ^ d) ^ (p / 2) := by
    apply Real.rpow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) hg2) (pow_nonneg hbudget _)
  have h2 : 0 ≤ (4 * gaussianAbsoluteMoment p ^ (2 / p) * scalarLayerBudget C r K ^ d) ^ (p / 2) := by
    apply Real.rpow_nonneg
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hgp _))
      (pow_nonneg hbudget _)
  positivity

/-- The actual native finite Gaussian layer has the sharp Sobolev expected
energy rate for every `p>1`. The proof uses lower-moment Jensen below two and
the Gaussian block moment plus countable Minkowski above two. -/
theorem nativeSmoothSobolev_expected_energy_rate_all_p
    (d n K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p r : ℝ) (hp : 1 < p) (hr : 0 ≤ r)
    (hgap : 2 * r < 2 * (K : ℝ) - 1) :
    (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      ∫⁻ x : UnitAddTorus (Fin d),
        (squareFunctionSquared r
          (gaussianSynthesis (nativeFinAtoms d n) z) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      ENNReal.ofReal (nativeSmoothSobolevRateConstant d K C p r *
        (nativeClassNormScale d n r (1 / 2)) ^ p) := by
  let L := nativeClassNormScale d n r (1 / 2)
  let A := (4 * gaussianAbsoluteMoment 2 * scalarLayerBudget C r K ^ d) ^ (p / 2)
  let B := (4 * gaussianAbsoluteMoment p ^ (2 / p) * scalarLayerBudget C r K ^ d) ^ (p / 2)
  have hL : 0 < L := by dsimp [L]; exact nativeClassNormScale_pos hd r (1 / 2)
  have hLp : 0 ≤ L ^ p := Real.rpow_nonneg (le_of_lt hL) _
  by_cases hp2 : p < 2
  · have hlow := nativeSmoothSobolev_lowerP_expected_energy_rate d n K hd hK C hC
      p r (by linarith) hp2 hr hgap
    have hA : A ≤ nativeSmoothSobolevRateConstant d K C p r := by
      dsimp [A, nativeSmoothSobolevRateConstant]
      linarith [le_max_left
        ((4 * gaussianAbsoluteMoment 2 * scalarLayerBudget C r K ^ d) ^ (p / 2))
        ((4 * gaussianAbsoluteMoment p ^ (2 / p) * scalarLayerBudget C r K ^ d) ^ (p / 2))]
    calc
      _ ≤ ENNReal.ofReal (A * L ^ p) := by exact hlow
      _ ≤ ENNReal.ofReal (nativeSmoothSobolevRateConstant d K C p r * L ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hA hLp
  · have hp2' : 2 ≤ p := le_of_not_gt hp2
    have hhigh := nativeSmoothSobolev_higherP_expected_energy_rate d n K hd hK C hC
      p r hp2' hr hgap
    have hB : B ≤ nativeSmoothSobolevRateConstant d K C p r := by
      dsimp [B, nativeSmoothSobolevRateConstant]
      linarith [le_max_right
        ((4 * gaussianAbsoluteMoment 2 * scalarLayerBudget C r K ^ d) ^ (p / 2))
        ((4 * gaussianAbsoluteMoment p ^ (2 / p) * scalarLayerBudget C r K ^ d) ^ (p / 2))]
    calc
      _ ≤ ENNReal.ofReal (B * L ^ p) := by exact hhigh
      _ ≤ ENNReal.ofReal (nativeSmoothSobolevRateConstant d K C p r * L ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right hB hLp

/-- The actual native Gaussian layer yields the Sobolev entropy lower rate
for every `p>1` and `r>0`, with the smooth-atom derivative order chosen
internally from `r`. -/
theorem periodicSobolev_entropy_of_actual_native_expected_rate
    {d : ℕ} (hd : 2 ≤ d) (p r : ℝ) (hp : 1 < p) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * (k : ℝ) ^ (-r) * (Real.log (k : ℝ)) ^
        (r * ((d - 1 : ℕ) : ℝ) + 1 / 2)) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | SobolevUnitBall p r f} := by
  let K : ℕ := Nat.ceil (r + 2)
  have hceil : r + 2 ≤ (K : ℝ) := by
    exact_mod_cast Nat.le_ceil (r + 2)
  have hK : 1 ≤ K := by
    have hreal : (1 : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast hreal
  have hgap : 2 * r < 2 * (K : ℝ) - 1 := by linarith
  obtain ⟨D, hDpos, hD⟩ := exists_smoothAtom_iteratedDeriv_bound K
  let RateC := nativeSmoothSobolevRateConstant d K D p r
  have hRateC : 0 < RateC := by
    dsimp [RateC]
    exact nativeSmoothSobolevRateConstant_pos d K D p r hgap
  have hmean : ∀ n : ℕ,
      (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
        (∫⁻ x : UnitAddTorus (Fin d),
          (squareFunctionSquared r (gaussianSynthesis (nativeFinAtoms d n) z) x) ^ (p / 2))
        ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      ENNReal.ofReal (RateC * (nativeClassNormScale d n r (1 / 2)) ^ p) := by
    intro n
    exact nativeSmoothSobolev_expected_energy_rate_all_p d n K (by omega) hK D hD
      p r (by linarith) (le_of_lt hr) hgap
  exact periodicSobolev_entropy_of_native_expected_energy_rate hd p r RateC
    (show 0 < p by linarith) hr hRateC hmean

end BrownianSharp
