import BrownianSharp.AtomicBlockBessel
import BrownianSharp.PeriodicAtomDerivatives
import Mathlib.Analysis.Fourier.AddCircle

/-! Scalar AddCircle Fourier-kernel identities used to prove dyadic block
variance bounds. This file does not yet identify the truncated kernels with
the tensor-product operator; that identification is handled separately. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.ScalarBlockBessel

open AddCircle

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

def continuousLp1 (f : C(UnitAddCircle, ℂ)) :
    Lp ℂ (2 : ℝ≥0∞) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  f.toLp (2 : ℝ≥0∞) AddCircle.haarAddCircle ℂ

/-- Finite scalar Fourier multiplier kernel, represented in AddCircle L². -/
def kernelLp (S : Finset ℤ) (c : ℤ → ℂ) (x : UnitAddCircle) :
    Lp ℂ (2 : ℝ≥0∞) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  ∑ n ∈ S, star (c n * fourier n x) • fourierLp (T := 1) 2 n

/-- Exact L² energy of the finite scalar multiplier kernel. -/
theorem kernelLp_norm_sq (S : Finset ℤ) (c : ℤ → ℂ) (x : UnitAddCircle) :
    ‖kernelLp S c x‖ ^ 2 = ∑ n ∈ S, ‖c n‖ ^ 2 := by
  unfold kernelLp
  rw [BrownianSharp.AtomicBlockKernelL2.norm_sq_orthonormal_finset_sum
    (fourierLp (T := 1) 2) (orthonormal_fourier (T := 1)) S
    (fun n => star (c n * fourier n x))]
  apply Finset.sum_congr rfl
  intro n hn
  simp [norm_mul, fourier_apply]

/-- Evaluation of a finite Fourier multiplier polynomial is the L² inner
product against its conjugate evaluation kernel. -/
theorem polynomial_eq_inner_kernelLp (S : Finset ℤ) (c : ℤ → ℂ)
    (f : C(UnitAddCircle, ℂ)) (x : UnitAddCircle) :
    (∑ n ∈ S, c n * fourierCoeff f n * fourier n x) =
      inner ℂ (kernelLp S c x)
        (f.toLp (2 : ℝ≥0∞) AddCircle.haarAddCircle ℂ) := by
  classical
  unfold kernelLp
  simp only [sum_inner, inner_smul_left]
  apply Finset.sum_congr rfl
  intro n hn
  have hrepr := fourierBasis_repr
    (T := 1) (f.toLp (2 : ℝ≥0∞) AddCircle.haarAddCircle ℂ) n
  rw [fourierBasis.repr_apply_apply] at hrepr
  rw [fourierCoeff_toLp] at hrepr
  rw [coe_fourierBasis] at hrepr
  change c n * fourierCoeff f n * fourier n x =
      star (star (c n * fourier n x)) *
        inner ℂ (fourierLp (T := 1) 2 n)
          (f.toLp (2 : ℝ≥0∞) AddCircle.haarAddCircle ℂ)
  rw [hrepr]
  simp only [star_star]
  ring

/-- Bessel controls the pointwise squared output of any finite scalar Fourier
multiplier on a pairwise orthogonal family of atoms. -/
theorem polynomial_atoms_sum_sq_le {ι : ℕ} (S : Finset ℤ) (c : ℤ → ℂ)
    (atoms : Fin ι → C(UnitAddCircle, ℂ)) (x : UnitAddCircle)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (horth : ∀ i j, i ≠ j → inner ℂ (continuousLp1 (atoms i))
      (continuousLp1 (atoms j)) = 0)
    (hnorm : ∀ i, ‖continuousLp1 (atoms i)‖ ^ 2 ≤ ρ) :
    (∑ i : Fin ι,
      ‖∑ n ∈ S, c n * fourierCoeff (atoms i) n * fourier n x‖ ^ 2) ≤
        ρ * ‖kernelLp S c x‖ ^ 2 := by
  let u : Fin ι → Lp ℂ (2 : ℝ≥0∞)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := fun i => continuousLp1 (atoms i)
  have hb := BrownianSharp.AtomicBlockBessel.sum_inner_sq_le_of_orthogonal
    u horth hρ hnorm (kernelLp S c x)
  calc
    _ = ∑ i : Fin ι, ‖inner ℂ (u i) (kernelLp S c x)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          have h := polynomial_eq_inner_kernelLp S c (atoms i) x
          dsimp [u, continuousLp1]
          have h' : (∑ n ∈ S, c n * fourierCoeff (atoms i) n *
              (↑(n • x).toCircle : ℂ)) =
              inner ℂ (kernelLp S c x) (continuousLp1 (atoms i)) := by
            simpa [continuousLp1, fourier_apply] using h
          rw [h']
          have hc := inner_conj_symm (𝕜 := ℂ) (continuousLp1 (atoms i))
            (kernelLp S c x)
          have hnorm' :
              ‖inner ℂ (kernelLp S c x) (continuousLp1 (atoms i))‖ =
                ‖inner ℂ (continuousLp1 (atoms i)) (kernelLp S c x)‖ := by
            calc
              _ = ‖(starRingEnd ℂ) (inner ℂ (kernelLp S c x)
                  (continuousLp1 (atoms i)))‖ := by
                    rw [starRingEnd_apply, norm_star]
              _ = _ := congrArg (fun z : ℂ => ‖z‖) hc
          rw [hnorm']
          rfl
    _ ≤ ρ * ‖kernelLp S c x‖ ^ 2 := by
          exact hb

end BrownianSharp.ScalarBlockBessel
