import BrownianSharp.ScalarKernelL1

/-! A public all-integer coefficient formula for the reused Fejer kernels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.ScalarKernelL1
open AddCircle HaarQuarter.TheoremD.FejerFourier

private theorem mode_integrable (k : ℤ) :
    Integrable (fourier (T := (1:ℝ)) k) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (by fun_prop : Continuous (fourier (T := (1:ℝ)) k)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Finite Gaussian/Fourier machinery is unnecessary here: this is exact
counting of character differences in the positive Fejer polynomial. -/
theorem fejer_coefficient_count (N : ℕ) (k : ℤ) :
    fourierCoeff (T := (1:ℝ)) (fejerFourierPolynomial N) k =
      (N:ℂ)⁻¹ * ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        if k=(s:ℤ)-(r:ℤ) then (1:ℂ) else 0 := by
  classical
  let f : ℕ → UnitAddCircle → ℂ := fun r x => ∑ s ∈ Finset.range N, fourier ((s:ℤ)-(r:ℤ)) x
  have hf (r : ℕ) : Integrable (f r) AddCircle.haarAddCircle := by
    dsimp [f]
    exact integrable_finset_sum _ fun s hs => mode_integrable _
  have hinner (r : ℕ) : fourierCoeff (f r) k =
      ∑ s ∈ Finset.range N, if k=(s:ℤ)-(r:ℤ) then (1:ℂ) else 0 := by
    have heq : f r = ∑ s ∈ Finset.range N, (fun x : UnitAddCircle => fourier ((s:ℤ)-(r:ℤ)) x) := by
      funext x; simp [f]
    rw [heq, fourierCoeff.sum _ _ (fun s hs => mode_integrable _)]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro s hs
    simpa only [Pi.single_apply] using congrFun (fourierCoeff_fourier ((s:ℤ)-(r:ℤ))) k
  rw [show fejerFourierPolynomial N = (N:ℂ)⁻¹ • ∑ r ∈ Finset.range N, f r by
    funext x; simp [fejerFourierPolynomial, f, smul_eq_mul]]
  rw [fourierCoeff.const_smul, fourierCoeff.sum _ _ (fun r hr => hf r)]
  simp only [Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact hinner r

theorem fejer_coefficient_outside (N : ℕ) (k : ℤ) (hk : N ≤ k.natAbs) :
    fourierCoeff (T := (1:ℝ)) (fejerFourierPolynomial N) k = 0 := by
  rw [fejer_coefficient_count]
  have hz : (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
      if k=(s:ℤ)-(r:ℤ) then (1:ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro s hs
    have hrN := Finset.mem_range.mp hr
    have hsN := Finset.mem_range.mp hs
    rw [if_neg (by omega)]
  rw [hz, mul_zero]

/-- The triangular coefficient formula includes every integer and the zero
kernel, with natural subtraction handling frequencies outside the support. -/
theorem fejer_coefficient (N : ℕ) (hN : 0<N) (k : ℤ) :
    fourierCoeff (T := (1:ℝ)) (fejerFourierPolynomial N) k =
      ((N-k.natAbs:ℕ):ℂ)/(N:ℂ) := by
  by_cases hk : k.natAbs ≤ N
  · cases k with
    | ofNat q => simpa using fejerFourierPolynomial_fourierCoeff_nat N q hN hk
    | negSucc q =>
      have he : Int.negSucc q = -((q+1:ℕ):ℤ) := by omega
      simpa only [he, Int.natAbs_negSucc, Int.natAbs_neg, Int.natAbs_natCast] using
        fejerFourierPolynomial_fourierCoeff_neg_nat N (q+1) hN hk
  · rw [fejer_coefficient_outside N k (by omega)]
    simp [Nat.sub_eq_zero_of_le (by omega : N≤k.natAbs)]

end BrownianSharp.ScalarKernelL1
