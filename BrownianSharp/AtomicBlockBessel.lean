import BrownianSharp.AtomicBlockKernelL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! A normalized Bessel estimate for finite orthogonal families.  This is the
abstract Hilbert-space step used after dyadic atoms have been shown to have
disjoint supports and a uniform squared-norm bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
open scoped ENNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace BrownianSharp.AtomicBlockBessel

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockKernelL2
open UnitAddTorus

def continuousLp {d : ℕ} (f : RealPeriodic d) :
    Lp ℂ (2 : ℝ≥0∞) (volume : Measure (UnitAddTorus (Fin d))) :=
  (complexifyContinuous f).toLp (2 : ℝ≥0∞)
    (volume : Measure (UnitAddTorus (Fin d))) ℂ

/-- Bessel's inequality for a finite orthogonal family with nonzero vectors,
rescaled by a common upper bound for their squared norms. -/
theorem sum_inner_sq_le_of_orthogonal_nonzero {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : ι → E) (hu : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0)
    (hnonzero : ∀ i, ‖u i‖ ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnorm : ∀ i, ‖u i‖ ^ 2 ≤ ρ) (x : E) :
    (∑ i : ι, ‖inner ℂ (u i) x‖ ^ 2) ≤ ρ * ‖x‖ ^ 2 := by
  classical
  let v : ι → E := fun i => ((‖u i‖⁻¹ : ℝ) : ℂ) • u i
  have hnormv : ∀ i, ‖v i‖ = 1 := by
    intro i
    dsimp [v]
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg,
      inv_mul_cancel₀ (hnonzero i)]
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst j
      rw [inner_self_eq_norm_sq_to_K, hnormv i]
      simp
    · simp only [hij, ite_false]
      dsimp [v]
      change inner ℂ (((‖u i‖⁻¹ : ℝ) : ℂ) • u i)
        (((‖u j‖⁻¹ : ℝ) : ℂ) • u j) = 0
      rw [inner_smul_left, inner_smul_right, hu i j hij]
      simp
  have hb := hv.sum_inner_products_le x (s := Finset.univ)
  have hrel : ∀ i, inner ℂ (u i) x = (‖u i‖ : ℂ) * inner ℂ (v i) x := by
    intro i
    have hvec : u i = (‖u i‖ : ℂ) • v i := by
      dsimp [v]
      have hs : (‖u i‖ : ℂ) * ((‖u i‖⁻¹ : ℝ) : ℂ) = 1 := by
        push_cast
        exact_mod_cast (mul_inv_cancel₀ (hnonzero i))
      calc
        u i = (1 : ℂ) • u i := by simp
        _ = (((‖u i‖ : ℝ) : ℂ) * ((‖u i‖⁻¹ : ℝ) : ℂ)) • u i := by rw [hs]
        _ = (‖u i‖ : ℂ) • (((‖u i‖⁻¹ : ℝ) : ℂ) • u i) := by rw [smul_smul]
    have hinner := congrArg (fun y : E => inner ℂ y x) hvec
    rw [hinner, inner_smul_left]
    change star (‖u i‖ : ℂ) * inner ℂ (v i) x = _
    simp
  calc
    ∑ i : ι, ‖inner ℂ (u i) x‖ ^ 2
        = ∑ i : ι, ‖(‖u i‖ : ℂ) * inner ℂ (v i) x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hrel i]
    _ = ∑ i : ι, ‖u i‖ ^ 2 * ‖inner ℂ (v i) x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hcast : ‖(‖u i‖ : ℂ)‖ = ‖u i‖ := by
            exact (RCLike.norm_ofReal (‖u i‖)).trans
              (abs_of_nonneg (norm_nonneg (u i)))
          calc
            ‖(‖u i‖ : ℂ) * inner ℂ (v i) x‖ ^ 2 =
                (‖(‖u i‖ : ℂ)‖ * ‖inner ℂ (v i) x‖) ^ 2 := by rw [norm_mul]
            _ = (‖u i‖ * ‖inner ℂ (v i) x‖) ^ 2 := by rw [hcast]
            _ = ‖u i‖ ^ 2 * ‖inner ℂ (v i) x‖ ^ 2 := by ring
    _ ≤ ∑ i : ι, ρ * ‖inner ℂ (v i) x‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hnorm i)
            (sq_nonneg ‖inner ℂ (v i) x‖)
    _ = ρ * ∑ i : ι, ‖inner ℂ (v i) x‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ρ * ‖x‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_left hb hρ

/-- Bessel's inequality also holds when some members of the orthogonal family
are zero: those indices contribute zero and are removed before normalization. -/
theorem sum_inner_sq_le_of_orthogonal {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : ι → E) (hu : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hnorm : ∀ i, ‖u i‖ ^ 2 ≤ ρ) (x : E) :
    (∑ i : ι, ‖inner ℂ (u i) x‖ ^ 2) ≤ ρ * ‖x‖ ^ 2 := by
  classical
  let p : ι → Prop := fun i => ‖u i‖ ≠ 0
  let J := {i : ι // p i}
  let w : J → E := fun i => u i.1
  let f : ι → ℝ := fun i => ‖inner ℂ (u i) x‖ ^ 2
  have hsplit := Fintype.sum_subtype_add_sum_subtype p f
  have hzero : (∑ i : {i : ι // ¬p i}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi0 : ‖u i.1‖ = 0 := by simpa [p] using i.2
    have hu0 : u i.1 = 0 := norm_eq_zero.mp hi0
    simp [f, hu0]
  have horth : ∀ i j : J, i ≠ j → inner ℂ (w i) (w j) = 0 := by
    intro i j hij
    exact hu i.1 j.1 (by intro heq; exact hij (Subtype.ext heq))
  have hnonzero : ∀ i : J, ‖w i‖ ≠ 0 := by
    intro i
    exact i.2
  have hbound : ∀ i : J, ‖w i‖ ^ 2 ≤ ρ := fun i => hnorm i.1
  have hB := sum_inner_sq_le_of_orthogonal_nonzero w horth hnonzero hρ hbound x
  dsimp [f] at hsplit ⊢
  rw [← hsplit, hzero, add_zero]
  exact hB

/-- Pointwise squared block evaluations of a finite orthogonal periodic atom
family are controlled by the squared L² norm of the actual smooth-block
evaluation kernel. The atom support and norm hypotheses are explicit inputs. -/
theorem smoothBlock_atom_sum_sq_le {ι d : ℕ} (s : Fin d → ℕ)
    (atoms : Fin ι → RealPeriodic d) (x : UnitAddTorus (Fin d))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (horth : ∀ i j, i ≠ j → inner ℂ (continuousLp (atoms i))
      (continuousLp (atoms j)) = 0)
    (hnorm : ∀ i,
      ‖continuousLp (atoms i)‖ ^ 2 ≤ ρ) :
    (∑ i : Fin ι, ‖block s (atoms i) x‖ ^ 2) ≤
      ρ * ‖evaluationKernelLp s x‖ ^ 2 := by
  let u : Fin ι → Lp ℂ (2 : ℝ≥0∞)
      (volume : Measure (UnitAddTorus (Fin d))) := fun i => continuousLp (atoms i)
  have hb := sum_inner_sq_le_of_orthogonal u horth hρ hnorm
    (evaluationKernelLp s x)
  calc
    ∑ i : Fin ι, ‖block s (atoms i) x‖ ^ 2 =
        ∑ i : Fin ι, ‖inner ℂ (u i) (evaluationKernelLp s x)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          have h := block_eq_inner_evaluationKernelLp s (atoms i) x
          have h' : inner ℂ (evaluationKernelLp s x) (continuousLp (atoms i)) =
              block s (atoms i) x := by simpa [continuousLp] using h
          dsimp [u]
          calc
            ‖block s (atoms i) x‖ ^ 2 =
                ‖inner ℂ (evaluationKernelLp s x) (continuousLp (atoms i))‖ ^ 2 := by
                  rw [← h']
            _ = ‖inner ℂ (continuousLp (atoms i)) (evaluationKernelLp s x)‖ ^ 2 := by
                  have hc := inner_conj_symm (𝕜 := ℂ) (continuousLp (atoms i))
                    (evaluationKernelLp s x)
                  have hnorm :
                      ‖inner ℂ (evaluationKernelLp s x) (continuousLp (atoms i))‖ =
                        ‖inner ℂ (continuousLp (atoms i)) (evaluationKernelLp s x)‖ := by
                    calc
                      _ = ‖(starRingEnd ℂ) (inner ℂ (evaluationKernelLp s x)
                          (continuousLp (atoms i)))‖ := by
                            rw [starRingEnd_apply, norm_star]
                      _ = _ := congrArg (fun z : ℂ => ‖z‖) hc
                  rw [hnorm]
    _ ≤ ρ * ‖evaluationKernelLp s x‖ ^ 2 := hb

end BrownianSharp.AtomicBlockBessel
