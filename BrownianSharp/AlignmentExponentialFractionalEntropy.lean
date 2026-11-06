import BrownianSharp.AlignmentExponentialNativeEntropy
import BrownianSharp.AlignmentFractionalNativeLayer
import BrownianSharp.AlignmentCompactFeatureBall
import BrownianSharp.AlignmentLatestStatements
import Mathlib.Tactic

/-! An unconditional isotropic tensor Riemann--Liouville entropy lower bound
obtained from the generic compact-domain native cover and actual atom
preimages in the fractional integration ball. -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentExponentialFractionalEntropy
open AlignmentFractionalNativeLayer AlignmentFractionalCompactness

theorem cubeNativeSynthesis_cube_eq {d n : ℕ} (x : LayerIndex d n → ℝ)
    (t : HaarQuarter.BrownianCubeAnchor d) :
    cubeNativeSynthesisLinear x t = AlignmentPaperGenericBumpCertified.bumpSynthesis
      AlignmentPaperContinuumGenericBump.AdmissibleBump.smoothAtomAdmissible x t.val := by
  simp [cubeNativeSynthesisLinear, cubeNativeAtom, AlignmentFractionalTensorAtoms.cubeTensorAtom,
    AlignmentPaperGenericBumpCertified.bumpSynthesis,
    AlignmentPaperContinuumGenericBump.cubeBumpAtom,
    AlignmentPaperContinuumGenericBump.AdmissibleBump.smoothAtomAdmissible,
    layerIndexCell, layerIndexDepth, mul_comm]

theorem isotropic_fractional_entropy_lower {d : ℕ} (hd : 2 ≤ d)
    {r : ℝ} (hr : 1/2 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+1/2)) ≤
          HaarQuarter.TheoremD.entropyNumber k
            (Latest.fractionalIntegrationBall (fun _ : Fin d => r)) := by
  obtain ⟨a,ha,hmass⟩ := isotropic_fractional_scaled_class_mass (d:=d) (by omega) hr
  let K := Latest.fractionalIntegrationBall (fun _ : Fin d => r)
  have hclass : ∀ n : ℕ, 0 ≤ n →
      (1/2:ENNReal)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r 0) •
            cubeNativeSynthesisLinear x ∈ K} := by
    intro n hn
    have hmass' := hmass n
    let S := Nat.choose (n+d-1) (d-1)
    have hSpos : 1 ≤ S := by
      dsimp [S]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have hpow : (1/2:ENNReal)^S ≤ (1/2:ENNReal) := by
      have hrepr : S = (S-1)+1 := by omega
      rw [hrepr, pow_succ]
      calc
        (1/2:ENNReal)^(S-1) * (1/2:ENNReal) ≤ 1 * (1/2:ENNReal) :=
          mul_le_mul_of_nonneg_right
            (pow_le_one₀ (a := (1/2:ENNReal)) (by norm_num) (by norm_num)) (by norm_num)
        _ = 1/2 := by simp
    change (1/2:ENNReal)^S ≤ _
    exact hpow.trans hmass'
  let F : ∀ n : ℕ, (LayerIndex d n → ℝ) →ₗ[ℝ]
      C(HaarQuarter.BrownianCubeAnchor d,ℝ) :=
    fun n => cubeNativeSynthesisLinear (d:=d) (n:=n)
  simpa only [zero_mul, add_zero, K] using
    (AlignmentExponentialNativeEntropy.entropy_rate_of_scaled_native_class_mass
    (α:=HaarQuarter.BrownianCubeAnchor d) (d:=d) hd K r 0 a
    (lt_trans (by norm_num : (0:ℝ)<1/2) hr) ha 0 F
    (fun n x s hs => ⟨⟨s, fun i => hs i (Set.mem_univ i)⟩, cubeNativeSynthesis_cube_eq x _⟩)
    hclass)

end BrownianSharp.AlignmentExponentialFractionalEntropy
