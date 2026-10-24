import BrownianSharp.AlignmentHilbertOrthogonalImages
import Mathlib.Tactic

/-! Lower norm bounds for operators with orthogonal images of an ON basis. -/

noncomputable section
open scoped InnerProductSpace

namespace BrownianSharp.AlignmentHilbertOrthogonalEnergy

private theorem norm_sq_sum_smul_of_pairwise_orthogonal
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} [Fintype ι] (y : ι → F) (c : ι → ℝ)
    (horth : ∀ i j, i ≠ j → ⟪y i, y j⟫_ℝ = 0) :
    ‖∑ i, c i • y i‖^2 = ∑ i, (c i)^2 * ‖y i‖^2 := by
  classical
  let s : Finset ι := Finset.univ
  have hsum (t : Finset ι) :
      ‖∑ i ∈ t, c i • y i‖^2 = ∑ i ∈ t, (c i)^2 * ‖y i‖^2 := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hzero : ⟪c a • y a, ∑ i ∈ t, c i • y i⟫_ℝ = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hai : a ≠ i := fun h => ha (h ▸ hi)
        simp only [inner_smul_left, inner_smul_right, horth a i hai, mul_zero]
      calc
        ‖c a • y a + ∑ i ∈ t, c i • y i‖^2 =
            ‖c a • y a + ∑ i ∈ t, c i • y i‖ *
              ‖c a • y a + ∑ i ∈ t, c i • y i‖ := by ring
        _ = ‖c a • y a‖ * ‖c a • y a‖ +
              ‖∑ i ∈ t, c i • y i‖ * ‖∑ i ∈ t, c i • y i‖ :=
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hzero
        _ = c a ^ 2 * ‖y a‖ ^ 2 + ∑ i ∈ t, (c i)^2 * ‖y i‖^2 := by
          have ih' : ‖∑ i ∈ t, c i • y i‖ * ‖∑ i ∈ t, c i • y i‖ =
              ∑ i ∈ t, c i ^ 2 * ‖y i‖ ^ 2 := by simpa only [pow_two] using ih
          rw [ih', norm_smul]
          rw [Real.norm_eq_abs]
          have hnorm : |c a| * ‖y a‖ * (|c a| * ‖y a‖) =
              c a ^ 2 * ‖y a‖ ^ 2 := by
            calc
              |c a| * ‖y a‖ * (|c a| * ‖y a‖) =
                  (|c a| * |c a|) * (‖y a‖ * ‖y a‖) := by ring
              _ = c a ^ 2 * ‖y a‖ ^ 2 := by rw [abs_mul_abs_self]; ring
          rw [hnorm]
  simpa [s] using hsum Finset.univ

/-- If the images of an orthonormal basis are orthogonal and all have norm at
least `σ`, then the operator is bounded below by `σ`. -/
theorem norm_lower_of_orthogonal_basis_images
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (σ : ℝ)
    (horth : ∀ i j, i ≠ j → ⟪T (b i), T (b j)⟫_ℝ = 0)
    (hlower : ∀ i, σ ≤ ‖T (b i)‖) (hσ : 0 ≤ σ) :
    ∀ x : E, σ * ‖x‖ ≤ ‖T x‖ := by
  intro x
  have hxrepr : x = ∑ i, ⟪b i, x⟫_ℝ • b i := (b.sum_repr' x).symm
  have hTxrepr : T x = ∑ i, ⟪b i, x⟫_ℝ • T (b i) := by
    calc
      T x = T (∑ i, ⟪b i, x⟫_ℝ • b i) := congrArg T hxrepr
      _ = ∑ i, ⟪b i, x⟫_ℝ • T (b i) := by simp
  have hnormsq : ‖T x‖^2 = ∑ i,
      (⟪b i, x⟫_ℝ)^2 * ‖T (b i)‖^2 := by
    rw [hTxrepr]
    exact norm_sq_sum_smul_of_pairwise_orthogonal (fun i => T (b i))
      (fun i => ⟪b i, x⟫_ℝ) horth
  have hcoord : ∑ i, (⟪b i, x⟫_ℝ)^2 = ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right x
  have hsq : (σ * ‖x‖)^2 ≤ ‖T x‖^2 := by
    rw [hnormsq, mul_pow]
    calc
      σ^2 * ‖x‖^2 = ∑ i, (⟪b i, x⟫_ℝ)^2 * σ^2 := by
        rw [← hcoord]
        simp_rw [mul_comm]
        rw [← Finset.mul_sum]
      _ ≤ ∑ i, (⟪b i, x⟫_ℝ)^2 * ‖T (b i)‖^2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left
        · exact (sq_le_sq₀ hσ (norm_nonneg _)).2 (hlower i)
        · exact sq_nonneg _
  exact (sq_le_sq₀ (mul_nonneg hσ (norm_nonneg _)) (norm_nonneg _)).1 hsq

end BrownianSharp.AlignmentHilbertOrthogonalEnergy
