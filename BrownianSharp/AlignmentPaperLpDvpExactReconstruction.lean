import BrownianSharp.AlignmentPaperLpDvpReconstruction
import BrownianSharp.AlignmentPaperLpTensorDvpExpansion

/-! Exact reconstruction from the anisotropic oversampled grid. -/

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperLpDvpExactReconstruction

open BrownianSharp
open BrownianSharp.Torus
open BrownianSharp.AlignmentPaperLpDvpReconstruction
open BrownianSharp.AlignmentPaperLpTensorDvpExpansion
open BrownianSharp.AlignmentPaperLpGridOrthogonality
open BrownianSharp.AlignmentPaperLpDvpReproduction
open BrownianSharp.AlignmentPaperLpDvpKernelExpansion
open BrownianSharp.AlignmentPaperLpOversampledGrid
open HaarQuarter.TheoremD.FejerFourier
open UnitAddTorus

private theorem mFourier_sub_mul {d : ℕ} (k : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x-y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  have hcoord (i : Fin d) :
      fourier (T := (1 : ℝ)) (k i) ((x-y) i) =
        fourier (T := (1 : ℝ)) (k i) (x i) *
          fourier (T := (1 : ℝ)) (-k i) (y i) := by
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

theorem oversampledDvpReconstruction_eq_of_bandlimited_polynomial {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (hband : ∀ k ∈ S, ∀ i, (k i).natAbs ≤ N i) :
    oversampledDvpReconstruction N
      (fun j => torusFourierPolynomial S a (oversampledTorusGridPoint N j)) =
      torusFourierPolynomial S a := by
  classical
  ext x
  let T := tensorDvpFrequencyBox N
  let c := tensorDvpFourierCoefficient N
  let M : ℂ := ∏ i, (N i * 4 : ℂ)
  have hM : M ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos (hN i) (by norm_num : 0 < 4)))
  have hnorm : (↑((oversampledGridSize N)⁻¹) : ℂ) = M⁻¹ := by
    have hcast : (↑(oversampledGridSize N) : ℂ) = M := by
      simp [M, oversampledGridSize, ← map_prod, mul_comm]
    rw [← hcast]
    push_cast
    rfl
  have hK (y : UnitAddTorus (Fin d)) :
      tensorDvpKernel N y = ∑ m ∈ T, c m * UnitAddTorus.mFourier m y := by
    simpa [T, c] using congrArg (fun f : C(UnitAddTorus (Fin d), ℂ) => f y)
      (tensorDvpKernel_eq_finiteFourierPolynomial N hN)
  have hKshift (j : OversampledGrid d N) :
      translatedTensorDvpKernel N j x =
        ∑ m ∈ T, c m * UnitAddTorus.mFourier m
          (oversampledTorusGridPoint N j - x) := by
    change tensorDvpKernel N (oversampledTorusGridPoint N j - x) = _
    exact hK _
  have hgrid (q : Fin d → ℤ) (hq : ∀ i, (q i).natAbs < N i * 4) :
      (∑ j : OversampledGrid d N,
        UnitAddTorus.mFourier q (oversampledTorusGridPoint N j)) =
        if q = 0 then M else 0 := by
    simpa [M, oversampledTorusGridPoint, UnitAddTorus.mFourier,
      oversampledGridCoordinate, fourier_apply, ContinuousMap.coe_mk] using
      (tensor_midpoint_fourier_sum_eq_zero
        (fun i => N i * 4) (by intro i; exact Nat.mul_pos (hN i) (by norm_num)) q
        (by intro i; simpa using hq i))
  have hcoeff (l : Fin d → ℤ) (hl : ∀ i, (l i).natAbs ≤ N i) :
      c (-l) = 1 := by
    simp [c, tensorDvpFourierCoefficient, dvpFourierCoefficient,
      deLaValleePoussinCircleKernel_fourierCoeff_of_natAbs_le, hN, hl]
  rw [oversampledDvpReconstruction]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
  change (↑((oversampledGridSize N)⁻¹) : ℂ) *
      ∑ j : OversampledGrid d N,
        torusFourierPolynomial S a (oversampledTorusGridPoint N j) *
          translatedTensorDvpKernel N j x =
    torusFourierPolynomial S a x
  rw [hnorm]
  simp_rw [BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply,
    hKshift]
  have hmode (k l : Fin d → ℤ) (y : UnitAddTorus (Fin d)) :
      UnitAddTorus.mFourier k y * UnitAddTorus.mFourier l y =
        UnitAddTorus.mFourier (k + l) y := by
    simp [UnitAddTorus.mFourier, Pi.add_apply, Finset.prod_mul_distrib,
      fourier_add]
  have hpair (l m : Fin d → ℤ) (hlmem : l ∈ S) (hmmem : m ∈ T) :
      (∑ j : OversampledGrid d N,
        (a l * UnitAddTorus.mFourier l (oversampledTorusGridPoint N j)) *
          (c m * UnitAddTorus.mFourier m
            (oversampledTorusGridPoint N j - x))) =
        (a l * c m * UnitAddTorus.mFourier (-m) x) *
          (if l + m = 0 then M else 0) := by
    have hchar (j : OversampledGrid d N) :
        UnitAddTorus.mFourier l (oversampledTorusGridPoint N j) *
          UnitAddTorus.mFourier m (oversampledTorusGridPoint N j - x) =
        UnitAddTorus.mFourier (l + m) (oversampledTorusGridPoint N j) *
          UnitAddTorus.mFourier (-m) x := by
      calc
        _ = (UnitAddTorus.mFourier l (oversampledTorusGridPoint N j) *
            UnitAddTorus.mFourier m (oversampledTorusGridPoint N j)) *
              UnitAddTorus.mFourier (-m) x := by
          rw [mFourier_sub_mul]
          ring
        _ = _ := by rw [hmode]
    calc
      _ = (a l * c m * UnitAddTorus.mFourier (-m) x) *
          ∑ j : OversampledGrid d N,
            UnitAddTorus.mFourier (l + m) (oversampledTorusGridPoint N j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = a l * c m * (UnitAddTorus.mFourier l (oversampledTorusGridPoint N j) *
                UnitAddTorus.mFourier m (oversampledTorusGridPoint N j - x)) := by ring
        _ = a l * c m * (UnitAddTorus.mFourier (l + m)
                (oversampledTorusGridPoint N j) * UnitAddTorus.mFourier (-m) x) := by
            exact congrArg (fun z : ℂ => a l * c m * z) (hchar j)
          _ = _ := by ring
      _ = _ := by
        rw [hgrid (l + m) (by
          intro i
          have hl' := hband l hlmem i
          have hm' : (m i).natAbs ≤ 2 * N i := by
            have hmcoord := (Fintype.mem_piFinset.mp
              (by simpa [T, tensorDvpFrequencyBox] using hmmem)) i
            have hmIcc := Finset.mem_Icc.mp (by simpa [dvpFrequencyBox] using hmcoord)
            have habs : |m i| ≤ 2 * (N i : ℤ) := abs_le.mpr ⟨hmIcc.1, hmIcc.2⟩
            have hmcast : ((m i).natAbs : ℤ) ≤ 2 * (N i : ℤ) := by
              rw [Int.natCast_natAbs]
              exact habs
            exact_mod_cast hmcast
          have hsum : (l i + m i).natAbs ≤ 3 * N i := by
            calc
              (l i + m i).natAbs ≤ (l i).natAbs + (m i).natAbs := Int.natAbs_add_le _ _
              _ ≤ N i + 2 * N i := Nat.add_le_add hl' hm'
              _ = 3 * N i := by ring
          have hstrict : 3 * N i < N i * 4 := by nlinarith [hN i]
          exact lt_of_le_of_lt hsum hstrict)]
  have hcollapse (l : Fin d → ℤ) (hl : ∀ i, (l i).natAbs ≤ N i) :
      (∑ m ∈ T,
        (a l * c m * UnitAddTorus.mFourier (-m) x) *
          (if l + m = 0 then M else 0)) =
        M * (a l * UnitAddTorus.mFourier l x) := by
    have hmem : -l ∈ T := by
      apply Fintype.mem_piFinset.mpr
      intro i
      rw [dvpFrequencyBox, Finset.mem_Icc]
      have habs : |l i| ≤ (N i : ℤ) := by
        have hcast : ((l i).natAbs : ℤ) ≤ N i := by exact_mod_cast hl i
        simpa [Int.natCast_natAbs] using hcast
      change -(2 * (N i : ℤ)) ≤ -l i ∧ -l i ≤ 2 * (N i : ℤ)
      rcases abs_le.mp habs with ⟨hlo, hhi⟩
      constructor <;> omega
    rw [Finset.sum_eq_single (-l)]
    · rw [hcoeff l hl]
      simp [Pi.add_apply, Pi.neg_apply]
      ring
    · intro m hm hne
      have hneq : l + m ≠ 0 := by
        intro hz
        apply hne
        ext i
        have hi := congrFun hz i
        change l i + m i = 0 at hi
        change m i = -l i
        omega
      simp [hneq]
    · intro hnot
      exact (hnot hmem).elim
  calc
    _ = M⁻¹ * ∑ l ∈ S, ∑ m ∈ T,
          (a l * c m * UnitAddTorus.mFourier (-m) x) *
            (if l + m = 0 then M else 0) := by
      congr 1
      calc
        _ = ∑ j : OversampledGrid d N, ∑ l ∈ S, ∑ m ∈ T,
              (a l * UnitAddTorus.mFourier l (oversampledTorusGridPoint N j)) *
                (c m * UnitAddTorus.mFourier m (oversampledTorusGridPoint N j-x)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul_sum]
        _ = ∑ l ∈ S, ∑ m ∈ T, ∑ j : OversampledGrid d N,
              (a l * UnitAddTorus.mFourier l (oversampledTorusGridPoint N j)) *
                (c m * UnitAddTorus.mFourier m (oversampledTorusGridPoint N j-x)) := by
          calc
            _ = ∑ l ∈ S, ∑ j : OversampledGrid d N, ∑ m ∈ T,
                  (a l * UnitAddTorus.mFourier l (oversampledTorusGridPoint N j)) *
                    (c m * UnitAddTorus.mFourier m (oversampledTorusGridPoint N j-x)) := by
              rw [Finset.sum_comm (s := Finset.univ) (t := S)]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [Finset.sum_comm (s := Finset.univ) (t := T)]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro m hm
          exact hpair l m hl (by simpa [T] using hm)
    _ = M⁻¹ * ∑ l ∈ S, M * (a l * UnitAddTorus.mFourier l x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      exact hcollapse l (hband l hl)
    _ = ∑ l ∈ S, a l * UnitAddTorus.mFourier l x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      field_simp

end BrownianSharp.AlignmentPaperLpDvpExactReconstruction
