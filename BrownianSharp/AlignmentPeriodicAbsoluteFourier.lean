import BrownianSharp.AlignmentPeriodicAbsoluteFourierCore
import BrownianSharp.AlignmentPeriodicSpectralEnergy
import BrownianSharp.AtomicBlockKernelL2

noncomputable section
namespace BrownianSharp.AlignmentPeriodicAbsoluteFourier
open BrownianSharp.Torus
open BrownianSharp.AtomicBlockKernelL2
open BrownianSharp.AlignmentPeriodicSpectralEnergy
open BrownianSharp.SmoothResolution
open UnitAddTorus

theorem realPeriodicFourier_hasSum_uniform {d : ℕ} (r : ℝ) (hr : 1/2 < r)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    HasSum (fun k : Fin d → ℤ => realPeriodicFourierCoeff f k • mFourier k)
      (complexifyContinuous f) := by
  have hc := realPeriodicFourierCoeff_summable r hr f hf
  have hcoeff : ∀ k : Fin d → ℤ,
      realPeriodicFourierCoeff f k =
        UnitAddTorus.mFourierCoeff (complexifyContinuous f) k := by
    intro k
    unfold realPeriodicFourierCoeff
    change UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k =
      UnitAddTorus.mFourierCoeff (fun x => (f x : ℂ)) k
    rfl
  have hc_norm : Summable (fun k =>
      ‖UnitAddTorus.mFourierCoeff (complexifyContinuous f) k‖) := by
    refine hc.congr ?_
    intro k
    rw [← hcoeff k]
  have hc' : Summable (UnitAddTorus.mFourierCoeff (complexifyContinuous f)) :=
    hc_norm.of_norm
  change HasSum
    (fun k : Fin d → ℤ =>
      UnitAddTorus.mFourierCoeff (complexifyContinuous f) k • mFourier k)
    (complexifyContinuous f)
  exact UnitAddTorus.hasSum_mFourier_series_of_summable hc'

end BrownianSharp.AlignmentPeriodicAbsoluteFourier
