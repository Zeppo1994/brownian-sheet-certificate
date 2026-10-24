import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
Minimal v10 torus definitions extracted from
HaarQuarter/TheoremDMixedSmoothness.lean (RealPeriodic,
realPeriodicFourierCoeff, torusFourierPolynomial). Their defining formulas are
unchanged. The independent namespace avoids importing the v10 sine-gain proof
merely to obtain these elementary definitions.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.Torus
abbrev RealPeriodic (d : ℕ) := C(UnitAddTorus (Fin d), ℝ)
def complexifyRealPeriodic {d : ℕ} (f : RealPeriodic d) : UnitAddTorus (Fin d) → ℂ :=
  fun x => (f x : ℂ)
def realPeriodicFourierCoeff {d : ℕ} (f : RealPeriodic d) (k : Fin d → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (complexifyRealPeriodic f) k
def torusFourierPolynomial {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) : C(UnitAddTorus (Fin d), ℂ) :=
  ∑ k ∈ S, (a k) • UnitAddTorus.mFourier k
end BrownianSharp.Torus
