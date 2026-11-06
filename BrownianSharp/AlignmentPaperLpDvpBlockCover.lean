import BrownianSharp.AlignmentPaperLpDvpExactReconstruction
import BrownianSharp.AlignmentPaperLpDvpSampling
import Mathlib.Data.Sym.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Operator.Basic
import BrownianSharp.Carl

/-! A real-coordinate encoding of complex oversampled DVP samples and its
finite-dimensional entropy lift. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperLpDvpBlockCover

open BrownianSharp.Torus
open BrownianSharp.AlignmentPaperLpDvpReconstruction
open BrownianSharp.AlignmentPaperLpDvpExactReconstruction
open BrownianSharp.AlignmentPaperLpDvpSampling
open BrownianSharp.AlignmentPaperLpOversampledGrid
open BrownianSharp.AlignmentPaperLpDvpReproduction
open BrownianSharp.AlignmentPaperLpGridOrthogonality
open BrownianSharp.AlignmentPaperTorusTranslation

abbrev Grid (d : ℕ) (N : Fin d → ℕ) := OversampledGrid d N

def gridRealIndexEquiv {d : ℕ} (N : Fin d → ℕ) :
    Grid d N × Bool ≃ Fin (Fintype.card (Grid d N) * 2) :=
  (Fintype.equivFin (Grid d N)).prodCongr finTwoEquiv.symm |>.trans finProdFinEquiv

def encodeComplexSamples {d : ℕ} (N : Fin d → ℕ)
    (f : C(UnitAddTorus (Fin d), ℂ)) :
    Fin (Fintype.card (Grid d N) * 2) → ℝ := fun i =>
  let j := (gridRealIndexEquiv N).symm i
  if j.2 then (f (oversampledTorusGridPoint N j.1)).im
  else (f (oversampledTorusGridPoint N j.1)).re

def decodeRealSamplesLinearMap {d : ℕ} (N : Fin d → ℕ) :
    (Fin (Fintype.card (Grid d N) * 2) → ℝ) →ₗ[ℝ] (Grid d N → ℂ) where
  toFun v j :=
    (v ((gridRealIndexEquiv N) (j, false) : Fin _ ) : ℂ) +
      Complex.I * (v ((gridRealIndexEquiv N) (j, true) : Fin _) : ℂ)
  map_add' v w := by
    funext j
    simp
    ring
  map_smul' r v := by
    funext j
    simp
    ring

def decodeRealSamplesCLM {d : ℕ} (N : Fin d → ℕ) :
    (Fin (Fintype.card (Grid d N) * 2) → ℝ) →L[ℝ] (Grid d N → ℂ) :=
  (decodeRealSamplesLinearMap N).mkContinuous 2 (by
    intro v
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg v))).2
    intro j
    change ‖(v _ : ℂ) + Complex.I * (v _ : ℂ)‖ ≤ 2 * ‖v‖
    calc
      _ ≤ |v ((gridRealIndexEquiv N) (j, false))| +
            |v ((gridRealIndexEquiv N) (j, true))| := by
        calc
          _ ≤ ‖(v ((gridRealIndexEquiv N) (j, false)) : ℂ)‖ +
                ‖Complex.I * (v ((gridRealIndexEquiv N) (j, true)) : ℂ)‖ := norm_add_le _ _
          _ = _ := by simp
      _ ≤ ‖v‖ + ‖v‖ := by
        have h1 := norm_le_pi_norm v ((gridRealIndexEquiv N) (j, false))
        have h2 := norm_le_pi_norm v ((gridRealIndexEquiv N) (j, true))
        simpa [Real.norm_eq_abs] using add_le_add h1 h2
      _ = 2 * ‖v‖ := by ring)

@[simp] theorem decodeRealSamplesCLM_apply {d : ℕ} (N : Fin d → ℕ)
    (v : Fin (Fintype.card (Grid d N) * 2) → ℝ) :
    decodeRealSamplesCLM N v = decodeRealSamplesLinearMap N v := rfl

def oversampledDvpRealCoordinateReconstruction {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) :
    (Fin (Fintype.card (Grid d N) * 2) → ℝ) →L[ℝ]
      C(UnitAddTorus (Fin d), ℂ) :=
  (oversampledDvpReconstructionCLM N hN).restrictScalars ℝ |>.comp
    (decodeRealSamplesCLM N)

theorem decode_encode_complex_samples {d : ℕ} (N : Fin d → ℕ)
    (f : C(UnitAddTorus (Fin d), ℂ)) :
    decodeRealSamplesLinearMap N (encodeComplexSamples N f) =
      fun j => f (oversampledTorusGridPoint N j) := by
  funext j
  simp [decodeRealSamplesLinearMap, encodeComplexSamples, gridRealIndexEquiv]
  apply Complex.ext <;> simp

theorem oversampledDvpRealCoordinateReconstruction_exact {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (hband : ∀ k ∈ S, ∀ i, (k i).natAbs ≤ N i) :
    oversampledDvpRealCoordinateReconstruction N hN
      (encodeComplexSamples N (torusFourierPolynomial S a)) =
      torusFourierPolynomial S a := by
  change (oversampledDvpReconstructionCLM N hN)
      (decodeRealSamplesLinearMap N (encodeComplexSamples N (torusFourierPolynomial S a))) = _
  rw [decode_encode_complex_samples]
  exact oversampledDvpReconstruction_eq_of_bandlimited_polynomial N hN S a hband

end BrownianSharp.AlignmentPaperLpDvpBlockCover
