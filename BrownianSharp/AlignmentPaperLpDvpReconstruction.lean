import BrownianSharp.AlignmentPaperLpGridOrthogonality
import Mathlib.Analysis.Normed.Operator.Basic

/-! Bounded continuous reconstruction from an anisotropic four-times
oversampled midpoint grid using the actual tensor DVP kernel. -/

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperLpDvpReconstruction

open BrownianSharp.AlignmentPaperLpGridOrthogonality
open BrownianSharp.AlignmentPaperLpDvpReproduction
open BrownianSharp.Torus

abbrev OversampledGrid (d : ℕ) (N : Fin d → ℕ) :=
  ∀ i, Fin (N i * 4)

def oversampledGridSize {d : ℕ} (N : Fin d → ℕ) : ℝ :=
  ∏ i, (4 * N i : ℝ)

def translatedTensorDvpKernel {d : ℕ} (N : Fin d → ℕ)
    (j : OversampledGrid d N) : C(UnitAddTorus (Fin d), ℂ) :=
  ⟨fun x => tensorDvpKernel N (oversampledTorusGridPoint N j - x), by fun_prop⟩

def oversampledDvpReconstruction {d : ℕ} (N : Fin d → ℕ)
    (a : OversampledGrid d N → ℂ) : C(UnitAddTorus (Fin d), ℂ) :=
  (↑((oversampledGridSize N)⁻¹) : ℂ) •
    ∑ j, (a j) • translatedTensorDvpKernel N j

def oversampledDvpReconstructionLinearMap {d : ℕ} (N : Fin d → ℕ) :
    (OversampledGrid d N → ℂ) →ₗ[ℂ] C(UnitAddTorus (Fin d), ℂ) where
  toFun := oversampledDvpReconstruction N
  map_add' a b := by
    ext x
    simp [oversampledDvpReconstruction, Finset.sum_add_distrib, add_smul,
      smul_add, mul_add]
  map_smul' c a := by
    ext x
    simp [oversampledDvpReconstruction, Finset.smul_sum, smul_smul]
    ring_nf

theorem oversampledGridSize_pos {d : ℕ} (N : Fin d → ℕ)
    (hN : ∀ i, 0 < N i) : 0 < oversampledGridSize N := by
  unfold oversampledGridSize
  apply Finset.prod_pos
  intro i hi
  exact mul_pos (by norm_num) (by exact_mod_cast hN i)

theorem oversampledDvpReconstruction_norm_le {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (a : OversampledGrid d N → ℂ) :
    ‖oversampledDvpReconstruction N a‖ ≤ (5 : ℝ)^d * ‖a‖ := by
  let M := oversampledGridSize N
  have hM : 0 < M := oversampledGridSize_pos N hN
  have hmassFactor :
      (∏ i, (5 * (N i * 4 : ℝ))) = (5 : ℝ)^d * M := by
    simp [M, oversampledGridSize, Finset.prod_mul_distrib, mul_comm]
  apply (ContinuousMap.norm_le _ (mul_nonneg (by positivity) (norm_nonneg a))).2
  intro x
  rw [oversampledDvpReconstruction]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
  have hsum :
      ‖∑ j : OversampledGrid d N,
        (a j) • translatedTensorDvpKernel N j x‖ ≤
      ‖a‖ * ∑ j : OversampledGrid d N,
        ‖tensorDvpKernel N (oversampledTorusGridPoint N j-x)‖ := by
    calc
      _ ≤ ∑ j : OversampledGrid d N,
          ‖(a j) • translatedTensorDvpKernel N j x‖ := norm_sum_le _ _
      _ = ∑ j : OversampledGrid d N,
          ‖a j‖ * ‖tensorDvpKernel N (oversampledTorusGridPoint N j-x)‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [translatedTensorDvpKernel, norm_smul]
      _ ≤ ∑ j : OversampledGrid d N,
          ‖a‖ * ‖tensorDvpKernel N (oversampledTorusGridPoint N j-x)‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm a j)
          (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hkernel := tensorDvp_oversampled_grid_abs_mass_le N hN x
  have hpoint :
      ‖oversampledDvpReconstruction N a x‖ ≤
        (5 : ℝ)^d * ‖a‖ := by
    change ‖((↑(M⁻¹) : ℂ) •
      ∑ j : OversampledGrid d N,
        (a j) • translatedTensorDvpKernel N j) x‖ ≤ _
    simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
    have hcoeff : ‖(↑(M⁻¹) : ℂ)‖ = M⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
    rw [norm_mul, hcoeff]
    have hInv : 0 ≤ M⁻¹ := (inv_pos.mpr hM).le
    calc
      _ ≤ M⁻¹ * (‖a‖ * ∑ j : OversampledGrid d N,
          ‖tensorDvpKernel N (oversampledTorusGridPoint N j-x)‖) := by
        exact mul_le_mul_of_nonneg_left hsum hInv
      _ ≤ M⁻¹ * (‖a‖ * ((5 : ℝ)^d * M)) := by
        rw [← hmassFactor]
        apply mul_le_mul_of_nonneg_left _ hInv
        apply mul_le_mul_of_nonneg_left hkernel (norm_nonneg a)
      _ = (5 : ℝ)^d * ‖a‖ := by field_simp [ne_of_gt hM]
  simpa [oversampledDvpReconstruction, M, ContinuousMap.smul_apply,
    ContinuousMap.sum_apply, smul_eq_mul] using hpoint

def oversampledDvpReconstructionCLM {d : ℕ} (N : Fin d → ℕ)
    (hN : ∀ i, 0 < N i) :
    (OversampledGrid d N → ℂ) →L[ℂ] C(UnitAddTorus (Fin d), ℂ) :=
  (oversampledDvpReconstructionLinearMap N).mkContinuous
    ((5 : ℝ)^d) (oversampledDvpReconstruction_norm_le N hN)

end BrownianSharp.AlignmentPaperLpDvpReconstruction
