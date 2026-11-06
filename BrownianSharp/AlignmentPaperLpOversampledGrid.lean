import BrownianSharp.AlignmentPaperLpDvpGrid
import Mathlib.Logic.Equiv.Fin.Basic

/-! DVP absolute mass on a four-times oversampled midpoint grid, by splitting
the grid into four translates of the bandwidth-sized midpoint grid. -/

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperLpOversampledGrid

open BrownianSharp.AlignmentPaperLpDvpGrid
open HaarQuarter.TheoremD.FejerFourier

def oversampledGridCoordinate (M : ℕ) (j : Fin M) : ℝ :=
  ((j.val : ℝ) + 1/2) / (M : ℝ)

private theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) =
      ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

theorem real_dvp_oversampled_grid_abs_mass_le {N : ℕ} (hN : 0 < N)
    (t : ℝ) :
    (∑ j : Fin (N*4),
      abs (realDeLaValleePoussinKernel N (oversampledGridCoordinate (N*4) j - t)))
        ≤ 5 * (N*4 : ℝ) := by
  classical
  let E : Fin N × Fin 4 ≃ Fin (N*4) := finProdFinEquiv
  have hcoord (b : Fin 4) :
      (∑ k : Fin N,
        abs (realDeLaValleePoussinKernel N
          (oversampledGridCoordinate (N*4) (E (k,b)) - t))) ≤ 5 * (N : ℝ) := by
    have hshift := realDeLaValleePoussin_grid_average_abs_le_five N
      (t + (3/2 - (b.val : ℝ)) / (N*4 : ℝ)) hN
    have hrange :
        (∑ k : Fin N,
          abs (realDeLaValleePoussinKernel N
            ((((k.val : ℝ) + 1/2) / N) -
              (t + (3/2 - (b.val : ℝ)) / (N*4 : ℝ))))) =
        ∑ k ∈ Finset.range N,
          abs (realDeLaValleePoussinKernel N
            ((((k : ℝ) + 1/2) / N) -
              (t + (3/2 - (b.val : ℝ)) / (N*4 : ℝ)))) := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => abs (realDeLaValleePoussinKernel N
          ((((k : ℝ) + 1/2) / N) -
            (t + (3/2 - (b.val : ℝ)) / (N*4 : ℝ)))) ) N
    have hterm :
        (∑ k : Fin N,
          abs (realDeLaValleePoussinKernel N
            (oversampledGridCoordinate (N*4) (E (k,b)) - t))) =
        ∑ k : Fin N,
          abs (realDeLaValleePoussinKernel N
            ((((k.val : ℝ) + 1/2) / N) -
              (t + (3/2 - (b.val : ℝ)) / (N*4 : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have harg :
          oversampledGridCoordinate (N*4) (E (k,b)) - t =
          (((k.val : ℝ) + 1/2) / N) -
            (t + (3/2 - (b.val : ℝ)) / (N*4 : ℝ)) := by
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        dsimp [oversampledGridCoordinate, E, finProdFinEquiv]
        push_cast
        field_simp
        ring
      simpa [oversampledGridCoordinate, E] using congrArg
        (fun z : ℝ => abs (realDeLaValleePoussinKernel N z)) harg
    rw [hterm, hrange]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hsum := (div_le_iff₀ hNreal).mp hshift
    simpa using hsum
  have hsumReindex :
      (∑ j : Fin (N*4),
        abs (realDeLaValleePoussinKernel N (oversampledGridCoordinate (N*4) j - t))) =
      ∑ b : Fin 4, ∑ k : Fin N,
        abs (realDeLaValleePoussinKernel N
          (oversampledGridCoordinate (N*4) (E (k,b)) - t)) := by
    have heq := Fintype.sum_equiv E
      (fun z : Fin N × Fin 4 =>
        abs (realDeLaValleePoussinKernel N
          (oversampledGridCoordinate (N*4) (E z) - t)))
      (fun j : Fin (N*4) =>
        abs (realDeLaValleePoussinKernel N
          (oversampledGridCoordinate (N*4) j - t)))
      (fun z => rfl)
    calc
      _ = ∑ z : Fin N × Fin 4,
          abs (realDeLaValleePoussinKernel N
            (oversampledGridCoordinate (N*4) (E z) - t)) := heq.symm
      _ = ∑ k : Fin N, ∑ b : Fin 4,
          abs (realDeLaValleePoussinKernel N
            (oversampledGridCoordinate (N*4) (E (k,b)) - t)) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ b : Fin 4, ∑ k : Fin N,
          abs (realDeLaValleePoussinKernel N
            (oversampledGridCoordinate (N*4) (E (k,b)) - t)) := by
        rw [Finset.sum_comm]
  rw [hsumReindex]
  calc
    (∑ b : Fin 4, ∑ k : Fin N,
        abs (realDeLaValleePoussinKernel N
          (oversampledGridCoordinate (N*4) (E (k,b)) - t)))
        ≤ ∑ b : Fin 4, 5 * (N : ℝ) := Finset.sum_le_sum fun b hb => hcoord b
    _ = 5 * (N*4 : ℝ) := by norm_num [Finset.sum_const]; ring_nf

theorem tensor_real_dvp_oversampled_grid_abs_mass_le {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) (t : Fin d → ℝ) :
    (∑ j : (∀ i, Fin (N i * 4)),
      ∏ i, abs (realDeLaValleePoussinKernel (N i)
        (oversampledGridCoordinate (N i * 4) (j i) - t i))) ≤
      ∏ i, (5 * (N i * 4 : ℝ)) := by
  rw [sum_pi_prod (fun i j =>
    abs (realDeLaValleePoussinKernel (N i)
      (oversampledGridCoordinate (N i * 4) j - t i)))]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    exact real_dvp_oversampled_grid_abs_mass_le (hN i) (t i)

end BrownianSharp.AlignmentPaperLpOversampledGrid
