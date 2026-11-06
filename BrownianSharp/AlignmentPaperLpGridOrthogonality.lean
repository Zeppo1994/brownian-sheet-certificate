import BrownianSharp.AlignmentPaperLpOversampledGrid
import BrownianSharp.TheoremDFejerSampling
import Mathlib.Analysis.Fourier.AddCircle
import BrownianSharp.AlignmentMaternComplexWindow
import BrownianSharp.AlignmentPaperLpDvpReproduction

/-! Discrete character orthogonality on an oversampled midpoint grid. -/

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperLpGridOrthogonality

open BrownianSharp.AlignmentPaperLpOversampledGrid
open HaarQuarter.TheoremD.Fejer
open HaarQuarter.TheoremD.FejerFourier
open BrownianSharp.Torus
open BrownianSharp.AlignmentMaternComplexWindow
open BrownianSharp.AlignmentPaperLpDvpReproduction

private theorem sum_pi_prod_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℂ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) =
      ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

def oversampledTorusGridPoint {d : ℕ} (N : Fin d → ℕ)
    (j : ∀ i, Fin (N i * 4)) : UnitAddTorus (Fin d) :=
  fun i => ((oversampledGridCoordinate (N i * 4) (j i) : ℝ) : UnitAddCircle)

def midpointTorusGridPoint {d : ℕ} (M : Fin d → ℕ)
    (j : ∀ i, Fin (M i)) : UnitAddTorus (Fin d) :=
  fun i => ((oversampledGridCoordinate (M i) (j i) : ℝ) : UnitAddCircle)

theorem midpoint_fourier_sum_eq_zero {M : ℕ} (hM : 0 < M)
    (q : ℤ) (hq : q ≠ 0) (hbound : q.natAbs < M) :
    (∑ j : Fin M,
      fourier (T := (1 : ℝ)) q
        ((oversampledGridCoordinate M j : ℝ) : UnitAddCircle)) = 0 := by
  classical
  cases q with
  | ofNat n =>
      have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        exact hq rfl
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hzero :
          (∑ j : Fin M, fourier (T := (1 : ℝ)) (Int.ofNat n)
            ((oversampledGridCoordinate M j : ℝ) : UnitAddCircle)) =
          ∑ j ∈ Finset.range M, midpointCharacter M n j := by
        calc
          _ = ∑ j : Fin M, midpointCharacter M n j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [fourier_coe_apply]
            simp [midpointCharacter, midpointPhase, oversampledGridCoordinate]
            ring_nf
          _ = _ := Fin.sum_univ_eq_sum_range
            (fun j : ℕ => midpointCharacter M n j) M
      rw [hzero]
      apply HaarQuarter.TheoremD.Fejer.midpoint_root_sum_eq_zero M n hM hn
      simpa using hbound
  | negSucc n =>
      have hn : 0 < n + 1 := by omega
      have hzero :
          (∑ j : Fin M, fourier (T := (1 : ℝ)) (Int.negSucc n)
            ((oversampledGridCoordinate M j : ℝ) : UnitAddCircle)) =
          ∑ j ∈ Finset.range M,
            Complex.exp (-(↑(midpointPhase M (n+1) j) * Complex.I)) := by
        calc
          _ = ∑ j : Fin M,
              Complex.exp (-(↑(midpointPhase M (n+1) j) * Complex.I)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [fourier_coe_apply]
            simp [midpointPhase, oversampledGridCoordinate]
            ring_nf
          _ = _ := Fin.sum_univ_eq_sum_range
            (fun j : ℕ => Complex.exp (-(↑(midpointPhase M (n+1) j) * Complex.I))) M
      rw [hzero]
      apply HaarQuarter.TheoremD.Fejer.midpoint_root_sum_neg_eq_zero M (n+1) hM hn
      simpa using hbound

theorem tensor_midpoint_fourier_sum_eq_zero {d : ℕ}
    (M : Fin d → ℕ) (hM : ∀ i, 0 < M i)
    (q : Fin d → ℤ) (hq : ∀ i, (q i).natAbs < M i) :
    (∑ j : (∀ i, Fin (M i)),
      ∏ i, fourier (T := (1 : ℝ)) (q i)
        ((oversampledGridCoordinate (M i) (j i) : ℝ) : UnitAddCircle)) =
      if q = 0 then ∏ i, (M i : ℂ) else 0 := by
  rw [sum_pi_prod_complex (fun i j =>
    fourier (T := (1 : ℝ)) (q i)
      ((oversampledGridCoordinate (M i) j : ℝ) : UnitAddCircle))]
  by_cases hq0 : q = 0
  · subst q
    simp only [if_pos rfl]
    apply Finset.prod_congr rfl
    intro i hi
    simp [midpoint_fourier_sum_eq_zero, hM]
  · rw [if_neg hq0]
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hq0 (funext h)
    have hzero := midpoint_fourier_sum_eq_zero (hM i) (q i) hi (hq i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

theorem tensorDvp_oversampled_grid_abs_mass_le {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (x : UnitAddTorus (Fin d)) :
    (∑ j : (∀ i, Fin (N i * 4)),
      ‖tensorDvpKernel N (oversampledTorusGridPoint N j - x)‖) ≤
      ∏ i, (5 * (N i * 4 : ℝ)) := by
  classical
  let surr : Function.Surjective (fun t : ℝ => (t : UnitAddCircle)) := by
    intro z
    exact Quotient.mk_surjective z
  let t : Fin d → ℝ := fun i => Classical.choose (surr (x i))
  have ht (i : Fin d) : (t i : UnitAddCircle) = x i :=
    Classical.choose_spec (surr (x i))
  have hterm (j : ∀ i, Fin (N i * 4)) :
      ‖tensorDvpKernel N (oversampledTorusGridPoint N j - x)‖ =
        ∏ i, abs (realDeLaValleePoussinKernel (N i)
          (oversampledGridCoordinate (N i * 4) (j i) - t i)) := by
    change ‖∏ i, deLaValleePoussinCircleKernel (N i)
        (oversampledTorusGridPoint N j i - x i)‖ = _
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have harg : oversampledTorusGridPoint N j i - x i =
        ((oversampledGridCoordinate (N i * 4) (j i) - t i : ℝ) : UnitAddCircle) := by
      rw [← ht i]
      simp [oversampledTorusGridPoint]
    rw [harg, deLaValleePoussinCircleKernel_eval_eq_real]
    simp [Complex.norm_real]
  calc
    _ = ∑ j : (∀ i, Fin (N i * 4)),
        ∏ i, abs (realDeLaValleePoussinKernel (N i)
          (oversampledGridCoordinate (N i * 4) (j i) - t i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j
    _ ≤ ∏ i, (5 * (N i * 4 : ℝ)) :=
      tensor_real_dvp_oversampled_grid_abs_mass_le N hN t

end BrownianSharp.AlignmentPaperLpGridOrthogonality
