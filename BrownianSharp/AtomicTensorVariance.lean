import BrownianSharp.AtomicBlockBessel
import BrownianSharp.AtomicTensorSynthesisLp
import BrownianSharp.ScalarAtomSpecialization

/-! Fixed-rectangular-shape specialization of the generic Fourier-block Bessel
bound to the actual tensor-product periodic dyadic atoms. -/

noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AtomicTensorVariance

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockBessel
open BrownianSharp.PeriodicCover
open UnitAddTorus

abbrev ShapeCell (d : ℕ) (s : Fin d → ℕ) := DyadicShapeCell d s

def shapePeriodicAtom {d : ℕ} (s : Fin d → ℕ) (j : ShapeCell d s) :
    RealPeriodic d where
  toFun := dyadicShapeAtom s j
  continuous_toFun := by
    unfold dyadicShapeAtom
    exact continuous_finsetProd Finset.univ fun i hi =>
      (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0).continuous.comp
        (continuous_apply i)

private theorem shapePeriodicAtom_eq_periodized {d : ℕ} (s : Fin d → ℕ)
    (j : ShapeCell d s) :
    shapePeriodicAtom s j = periodizedDyadicAtom
      ⟨s, (fun i => (j i).val), fun i => (j i).isLt⟩ := by
  ext x
  rfl

private theorem continuousLp_norm_sq_eq_integral {d : ℕ} (f : RealPeriodic d) :
    ‖AtomicBlockBessel.continuousLp f‖ ^ 2 =
      ∫ x : UnitAddTorus (Fin d), |f x| ^ 2
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ _ _ _]
  rw [AtomicBlockBessel.continuousLp, ContinuousMap.inner_toLp]
  have hintOn : IntegrableOn
      (fun x : UnitAddTorus (Fin d) => (f x : ℂ) * star (f x : ℂ))
      Set.univ (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    have hc : Continuous (fun x : UnitAddTorus (Fin d) =>
        (f x : ℂ) * star (f x : ℂ)) := by fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_univ
  have hint : Integrable
      (fun x : UnitAddTorus (Fin d) => (f x : ℂ) * star (f x : ℂ))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    simpa [integrableOn_univ] using hintOn
  change Complex.re (∫ x : UnitAddTorus (Fin d),
    (f x : ℂ) * star (f x : ℂ)
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) = _
  calc
    _ = ∫ x : UnitAddTorus (Fin d),
        Complex.re ((f x : ℂ) * star (f x : ℂ))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
          (integral_re hint).symm
    _ = ∫ x : UnitAddTorus (Fin d), |f x| ^ 2
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [RCLike.star_def, RCLike.mul_conj]
      have hnorm : ‖(f x : ℂ)‖ = |f x| := RCLike.norm_ofReal _
      rw [hnorm]
      have hp : (Complex.ofReal |f x|) ^ 2 = Complex.ofReal (|f x| ^ 2) :=
        (Complex.ofReal_pow _ _).symm
      change Complex.re ((Complex.ofReal |f x|) ^ 2) = |f x| ^ 2
      calc
        _ = Complex.re (Complex.ofReal (|f x| ^ 2)) := congrArg Complex.re hp
        _ = _ := Complex.ofReal_re _

private theorem shapePeriodicAtom_orthogonal {d : ℕ} (s : Fin d → ℕ) :
    ∀ i j : ShapeCell d s, i ≠ j →
      inner ℂ (AtomicBlockBessel.continuousLp (shapePeriodicAtom s i))
        (AtomicBlockBessel.continuousLp (shapePeriodicAtom s j)) = 0 := by
  intro i j hij
  rw [AtomicBlockBessel.continuousLp, AtomicBlockBessel.continuousLp,
    ContinuousMap.inner_toLp]
  have hji : j ≠ i := by
    intro heq
    exact hij heq.symm
  have hzero := dyadicShapeAtom_mul_eq_zero_of_ne s j i hji
  calc
    _ = ∫ x : UnitAddTorus (Fin d), (0 : ℂ)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (dyadicShapeAtom s j x : ℂ) *
        (starRingEnd ℂ) (dyadicShapeAtom s i x : ℂ) = 0
      have hstar : (starRingEnd ℂ) (dyadicShapeAtom s i x : ℂ) =
          (dyadicShapeAtom s i x : ℂ) := by
        simp [RCLike.star_def, RCLike.conj_ofReal]
      rw [hstar]
      rw [← Complex.ofReal_mul]
      exact_mod_cast hzero x
    _ = 0 := by simp

private theorem shapePeriodicAtom_norm_sq_le {d : ℕ} (s : Fin d → ℕ)
    (j : ShapeCell d s) :
    ‖AtomicBlockBessel.continuousLp (shapePeriodicAtom s j)‖ ^ 2 ≤
      ∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹ := by
  rw [continuousLp_norm_sq_eq_integral]
  simpa [shapePeriodicAtom, dyadicShapeAtom] using
    dyadicShapeAtom_rpow_integral_le s j 2 (by norm_num)

/-- Pointwise tensor variance bound for one rectangular depth shape. The
frequency count remains explicit and all tensor cell orthogonality is proved
from the actual disjoint supports. -/
theorem actual_shape_block_variance_le {d : ℕ} (s t : Fin d → ℕ)
    (x : UnitAddTorus (Fin d)) :
    (∑ j : ShapeCell d s,
      ‖block t (shapePeriodicAtom s j) x‖ ^ 2) ≤
      (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) * (frequencyBox t).card := by
  classical
  let e : ShapeCell d s ≃ Fin (Fintype.card (ShapeCell d s)) := Fintype.equivFin _
  let ρ : ℝ := ∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact Finset.prod_nonneg fun _ _ => inv_nonneg.mpr (by positivity)
  have hfin := AtomicBlockBessel.smoothBlock_atom_sum_sq_le t
    (fun k : Fin (Fintype.card (ShapeCell d s)) => shapePeriodicAtom s (e.symm k)) x
    hρ
    (by
      intro k l hkl
      exact shapePeriodicAtom_orthogonal s (e.symm k) (e.symm l)
        (by intro heq; exact hkl (by simpa using congrArg e heq)))
    (fun k => shapePeriodicAtom_norm_sq_le s (e.symm k))
  have hsum :
      (∑ j : ShapeCell d s, ‖block t (shapePeriodicAtom s j) x‖ ^ 2) =
      ∑ k : Fin (Fintype.card (ShapeCell d s)),
        ‖block t (shapePeriodicAtom s (e.symm k)) x‖ ^ 2 := by
    exact Fintype.sum_equiv e _ _ (by intro j; simp)
  rw [hsum]
  calc
    _ ≤ ρ * ‖AtomicBlockKernelL2.evaluationKernelLp t x‖ ^ 2 := hfin
    _ ≤ ρ * (frequencyBox t).card := by
      apply mul_le_mul_of_nonneg_left _ hρ
      exact AtomicBlockKernelL2.evaluationKernelLp_norm_sq_le_card t x

end BrownianSharp.AtomicTensorVariance
