import BrownianSharp.TheoremDFejerFourier

/-! Tensorized translated-grid mass bounds for the actual de la Vallée-Poussin
reproducing kernel. The factorization is on the full product grid, not a
replacement coefficient-space sampling model. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperLpDvpGrid

open HaarQuarter.TheoremD.FejerFourier

private theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) =
      ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

/-- The tensor product of one-dimensional de la Vallée-Poussin kernels with
coordinate-dependent bandwidths has absolute mass bounded by the product of
the corresponding one-dimensional grid masses. -/
theorem tensor_shifted_dvp_grid_abs_mass_le_five_pi {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) (t : Fin d → ℝ) :
    (∑ j : (∀ i, Fin (N i)),
      ∏ i, |realDeLaValleePoussinKernel (N i)
        ((((j i).val : ℝ) + 1 / 2) / (N i) - t i)|) ≤
      ∏ i, (5 * (N i : ℝ)) := by
  classical
  let f : ∀ i : Fin d, Fin (N i) → ℝ := fun i j =>
    |realDeLaValleePoussinKernel (N i)
      ((((j.val : ℝ) + 1 / 2) / (N i) : ℝ) - t i)|
  have hfactor :
      (∑ j : (∀ i, Fin (N i)), ∏ i, f i (j i)) =
        ∏ i, ∑ j : Fin (N i), f i j := sum_pi_prod f
  have hcoord (i : Fin d) : (∑ j : Fin (N i), f i j) ≤ 5 * (N i : ℝ) := by
    have hgrid := realDeLaValleePoussin_grid_average_abs_le_five (N i) (t i) (hN i)
    have hNreal : (0 : ℝ) < N i := by exact_mod_cast hN i
    have hsum :
        (∑ j : Fin (N i),
          |realDeLaValleePoussinKernel (N i)
            ((((j.val : ℝ) + 1 / 2) / (N i)) - t i)|) =
          ∑ j ∈ Finset.range (N i),
            |realDeLaValleePoussinKernel (N i)
              ((((j : ℝ) + 1 / 2) / (N i)) - t i)| := by
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ => |realDeLaValleePoussinKernel (N i)
          ((((j : ℝ) + 1 / 2) / (N i)) - t i)|) (N i)
    rw [show (∑ j : Fin (N i), f i j) = _ by
      simpa [f] using hsum]
    have hsumle := (div_le_iff₀ hNreal).mp hgrid
    convert hsumle using 1 <;> norm_num [one_div]
  rw [hfactor]
  calc
    ∏ i, (∑ j : Fin (N i), f i j) ≤ ∏ i, (5 * (N i : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        apply Finset.sum_nonneg
        intro j hj
        exact abs_nonneg _
      · intro i hi
        exact hcoord i
    _ = ∏ i, (5 * (N i : ℝ)) := rfl

end BrownianSharp.AlignmentPaperLpDvpGrid
