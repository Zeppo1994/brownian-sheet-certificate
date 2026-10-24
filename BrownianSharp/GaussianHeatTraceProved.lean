import BrownianSharp.GaussianHeatTracePDE
import BrownianSharp.GaussianHeatSupport

/-!
# Proof of the trace premise used by the regularized Borell argument

The coordinate Gaussian integration-by-parts argument proves the required
trace identity for constant plus compactly supported smooth perturbations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology

namespace BrownianSharp

private theorem gaussianHeat_const_add_of_compactSupport {κ : Type*} [Fintype κ]
    (p : (κ → ℝ) → ℝ) (c t : ℝ) (x : κ → ℝ)
    (hp : Continuous p) (hpc : HasCompactSupport p) :
    gaussianHeat (fun y => c + p y) t x = c + gaussianHeat p t x := by
  have hpBound0 := hp.bounded_above_of_compact_support hpc
  let Cp := max hpBound0.choose 0
  have hpBound (y : κ → ℝ) : ‖p y‖ ≤ Cp :=
    (hpBound0.choose_spec y).trans (le_max_left _ _)
  have hpi : Integrable (fun z : κ → ℝ => p (x + Real.sqrt t • z))
      (productStandardGaussian κ) :=
    gaussianHeat_integrable_of_bounded p hp t x hpBound
  rw [gaussianHeat]
  calc
    (∫ z, c + p (x + Real.sqrt t • z) ∂productStandardGaussian κ) =
        (∫ _z, c ∂productStandardGaussian κ) +
          ∫ z, p (x + Real.sqrt t • z) ∂productStandardGaussian κ :=
      integral_add (integrable_const c) hpi
    _ = c + gaussianHeat p t x := by simp [gaussianHeat]

theorem gaussianHeatTracePDE_proved (κ : Type*) [Fintype κ] [DecidableEq κ] :
    ∀ (c : ℝ) (p : (κ → ℝ) → ℝ), ContDiff ℝ 2 p → HasCompactSupport p →
    ∀ (x : κ → ℝ) (t : ℝ), 0 < t →
      HasDerivAt (fun s : ℝ => gaussianHeat (fun y => c + p y) s x)
        ((∑ i, ∫ z, fderiv ℝ
          (fun y => fderiv ℝ (fun w => c + p w) y (Pi.single i (1 : ℝ)))
          (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
          ∂productStandardGaussian κ) / 2) t := by
  intro c p hp hpc x t ht
  have hbase := hasDerivAt_gaussianHeat_trace_of_contDiff_compactSupport
    p hp hpc x t ht
  have hconst (s : ℝ) :
      gaussianHeat (fun y => c + p y) s x = c + gaussianHeat p s x :=
    gaussianHeat_const_add_of_compactSupport p c s x hp.continuous hpc
  have hderiv := hbase.const_add c
  have hsum : (∑ i, ∫ z, fderiv ℝ
          (fun y => fderiv ℝ (fun w => c + p w) y (Pi.single i (1 : ℝ)))
          (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
          ∂productStandardGaussian κ) =
        ∑ i, ∫ z, fderiv ℝ
          (fun y => fderiv ℝ p y (Pi.single i (1 : ℝ)))
          (x + Real.sqrt t • z) (Pi.single i (1 : ℝ))
          ∂productStandardGaussian κ := by
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    filter_upwards [] with z
    simp [fderiv_const_add]
  convert hderiv using 1
  · funext s
    exact hconst s
  · rw [hsum]
    ring

end BrownianSharp
