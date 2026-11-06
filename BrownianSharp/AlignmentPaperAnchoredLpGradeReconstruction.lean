import BrownianSharp.AlignmentPaperLpJointDvp
import BrownianSharp.AlignmentPeriodicFourierReconstruction
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Reconstruct the actual continuous periodic path from its smooth grades.
The sole analytic premise is summability of those grades; the sum is identified
by their actual Fourier coefficients and the dyadic partition of unity. -/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpGradeReconstruction
open BrownianSharp.Torus BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPeriodicFourierReconstruction
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The grade fibre is the existing finite shape type, with no missing zero
coordinate profiles. -/
def shapeGradeFiberEquiv (d n : ℕ) :
    Shape d n ≃ {s : Fin d → ℕ // (∑ i, s i) = n} where
  toFun r := ⟨fun i => r.1 i, by
    have h := (Finset.mem_finsuppAntidiag'.mp r.2).1
    simpa [Finsupp.sum_fintype] using h⟩
  invFun s := ⟨Finsupp.equivFunOnFinite.symm s.1, by
    apply Finset.mem_finsuppAntidiag'.2
    constructor
    · simpa [Finsupp.sum_fintype] using s.2
    · simp⟩
  left_inv r := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

/-- Regrouping the actual tensor partition of unity by total grade. -/
theorem gradeMultiplier_hasSum {d : ℕ} (k : Fin d → ℤ) :
    HasSum (fun n : ℕ => ∑ s : Shape d n, tensorMultiplier s.1 k) 1 := by
  classical
  have h := (tensorMultiplier_hasSum k).tsum_fiberwise
    (fun s : Fin d → ℕ => ∑ i, s i)
  have hinner : ∀ n : ℕ,
      (∑' s : {s : Fin d → ℕ | (∑ i, s i) = n}, tensorMultiplier s.1 k) =
        ∑ s : Shape d n, tensorMultiplier s.1 k := by
    intro n
    let e := shapeGradeFiberEquiv d n
    let a : {s : Fin d → ℕ // (∑ i, s i) = n} → ℝ :=
      fun s => tensorMultiplier s.1 k
    have he : HasSum (a ∘ e) (∑ s : Shape d n, a (e s)) :=
      hasSum_fintype (a ∘ e)
    have hh := (e.hasSum_iff.mp he).tsum_eq
    change (∑' s : {s : Fin d → ℕ // (∑ i, s i) = n},
      tensorMultiplier s.1 k) =
      ∑ s : Shape d n, tensorMultiplier s.1 k at hh
    exact hh
  change HasSum (fun n : ℕ =>
    ∑' s : {s : Fin d → ℕ // (∑ i, s i) = n}, tensorMultiplier s.1 k) 1 at h
  exact h.congr_fun (fun n => (hinner n).symm)

/-- Each finite smooth grade has the exact sum of its block coefficients. -/
theorem smoothGradePolynomial_coefficient {d n : ℕ} (f : RealPeriodic d)
    (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (smoothGradePolynomial (d := d) (n := n) f) k =
      (∑ s : Shape d n, (tensorMultiplier s.1 k : ℂ)) *
        realPeriodicFourierCoeff f k := by
  classical
  rw [← fourierCoefficientCLM_apply]
  simp only [smoothGradePolynomial, map_sum, fourierCoefficientCLM_apply,
    block_coefficient, Finset.sum_mul]

/-- Summable smooth grades reconstruct the actual path in the uniform norm,
not only an abstract coefficient sequence or an Lp equivalence class. -/
theorem smoothGradePolynomial_hasSum {d : ℕ} (f : RealPeriodic d)
    (hs : Summable (fun n : ℕ => smoothGradePolynomial (d := d) (n := n) f)) :
    HasSum (fun n : ℕ => smoothGradePolynomial (d := d) (n := n) f)
      (complexifyContinuous f) := by
  have hcoeff : ∀ k,
      UnitAddTorus.mFourierCoeff
        ((∑' n : ℕ, smoothGradePolynomial (d := d) (n := n) f) :
          C(UnitAddTorus (Fin d), ℂ)) k =
      UnitAddTorus.mFourierCoeff (complexifyContinuous f) k := by
    intro k
    have h1 := (fourierCoefficientCLM k).hasSum hs.hasSum
    have h2 := (Complex.ofRealCLM.hasSum (gradeMultiplier_hasSum k)).mul_right
      (realPeriodicFourierCoeff f k)
    simp only [fourierCoefficientCLM_apply, smoothGradePolynomial_coefficient] at h1
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul,
      Complex.ofReal_sum] at h2
    exact h1.unique h2
  have hLp :
      (∑' n : ℕ, smoothGradePolynomial (d := d) (n := n) f).toLp 2 volume ℂ =
        (complexifyContinuous f).toLp 2 volume ℂ := by
    apply (UnitAddTorus.mFourierBasis (d := Fin d)).repr.injective
    ext k
    simp only [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierCoeff_toLp]
    exact hcoeff k
  have heq :
      (∑' n : ℕ, smoothGradePolynomial (d := d) (n := n) f) =
        complexifyContinuous f := ContinuousMap.toLp_injective volume hLp
  simpa only [heq] using hs.hasSum

end BrownianSharp.AlignmentPaperAnchoredLpGradeReconstruction
