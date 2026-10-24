import BrownianSharp.FejerCoefficients
import BrownianSharp.FejerSecondDifference

/-! Finite even Fourier multipliers as signed positive Fejer mixtures. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.ScalarKernelL1
open AddCircle HaarQuarter.TheoremD.FejerFourier

/-- Second-difference weights for the Fejer kernels of orders 1,...,J. -/
def secondWeight (c : ℕ → ℂ) (j : ℕ) : ℂ :=
  (j+1:ℕ) * (c j-2*c (j+1)+c (j+2))

def fejerMixture (J : ℕ) (c : ℕ → ℂ) : C(UnitAddCircle, ℂ) :=
  ∑ j ∈ Finset.range J, secondWeight c j • fejerKernel (j+1)

/-- The mixture reconstructs the exact even coefficient sequence. -/
theorem fejerMixture_coefficient (J : ℕ) (c : ℕ → ℂ)
    (htail : ∀ k, J ≤ k → c k=0) (k : ℤ) :
    fourierCoeff (fejerMixture J c) k = c k.natAbs := by
  classical
  have hInt (j : ℕ) : Integrable (fun x : UnitAddCircle =>
      secondWeight c j * fejerFourierPolynomial (j+1) x) AddCircle.haarAddCircle :=
    ((fejer_continuous (j+1)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  have heq : (fejerMixture J c : UnitAddCircle → ℂ) =
      ∑ j ∈ Finset.range J, (fun x => secondWeight c j * fejerFourierPolynomial (j+1) x) := by
    funext x
    simp [fejerMixture, fejerKernel, smul_eq_mul]
  rw [heq, fourierCoeff.sum _ _ (fun j hj => hInt j)]
  simp only [Finset.sum_apply]
  have hterm : ∀ j, fourierCoeff (fun x : UnitAddCircle =>
      secondWeight c j * fejerFourierPolynomial (j+1) x) k =
      ((j+1-k.natAbs:ℕ):ℂ)*(c j-2*c (j+1)+c (j+2)) := by
    intro j
    rw [fourierCoeff.const_mul, fejer_coefficient (j+1) (by omega)]
    unfold secondWeight
    have hj : (j+1:ℂ) ≠ 0 := by exact_mod_cast (by omega : j+1≠0)
    push_cast
    field_simp
    <;> ring
  simp_rw [hterm]
  by_cases hk : k.natAbs ≤ J
  · exact fejer_secondDifference_telescope_of_tail_zero c J k.natAbs hk
      (htail J le_rfl) (htail (J+1) (by omega))
  · rw [htail k.natAbs (by omega)]
    apply Finset.sum_eq_zero
    intro j hj
    have hjJ := Finset.mem_range.mp hj
    simp [Nat.sub_eq_zero_of_le (by omega : j+1≤k.natAbs)]

/-- An actual continuous even polynomial is the finite Fejer mixture of its
second differences. -/
theorem continuous_eq_fejerMixture (F : C(UnitAddCircle, ℂ)) (J : ℕ) (c : ℕ → ℂ)
    (hF : ∀ k : ℤ, fourierCoeff F k=c k.natAbs)
    (htail : ∀ k, J ≤ k → c k=0) : F=fejerMixture J c := by
  apply continuous_eq_of_fourierCoeff_eq
  intro k
  rw [hF, fejerMixture_coefficient J c htail]

theorem fejerMixture_norm_integral_le (J : ℕ) (c : ℕ → ℂ) :
    (∫ x : UnitAddCircle, ‖fejerMixture J c x‖ ∂AddCircle.haarAddCircle) ≤
      ∑ j ∈ Finset.range J, ‖secondWeight c j‖ := by
  have h := fejer_mixture_norm_integral_le
    ((Finset.range J).image Nat.succ) (fun j => secondWeight c (j-1))
    (by intro N hN; rcases Finset.mem_image.mp hN with ⟨j,hj,rfl⟩; omega)
  simpa [Finset.sum_image, Nat.succ_injective.injOn, fejerMixture, fejerKernel,
    Nat.succ_eq_add_one, smul_eq_mul] using h

end BrownianSharp.ScalarKernelL1
