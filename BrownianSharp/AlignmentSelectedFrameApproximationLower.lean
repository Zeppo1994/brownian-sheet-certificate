import BrownianSharp.AlignmentFractionalCubeTraceLower
import BrownianSharp.AlignmentGenericSelectedLayerFrame
import BrownianSharp.AlignmentIntegerTensorLowerRate

noncomputable section
open scoped ENNReal
open HaarQuarter
namespace BrownianSharp.AlignmentSelectedFrameApproximationLower
open AlignmentFractionalCubeTraceLower AlignmentGenericSelectedLayerFrame
  AlignmentIntegerTwoUniversalSelectedFrame AlignmentFractionalL2
  AlignmentFractionalTensorL2Semigroup AlignmentSigmaFiniteL2Tensor AlignmentFractionalTensorOperator
  AlignmentFractionalApproximationNumbers AlignmentIntegerTensorLowerRate

theorem tensor_approximation_lower_rate_of_scalar_frame
    {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (hr : 1/2 < r)
    (F : SelectedIndex → UnitL2) (hF : Orthonormal ℝ F)
    (A : UnitL2 →L[ℝ] UnitL2)
    (T : CameronMartin.UnitCubeL2 d →L[ℝ] C(BrownianCubeAnchor d,ℝ))
    (hfactor : ∀ v : Fin d → UnitL2,
      cubeProfileToL2 (T (productToCube d (productVector v))) =
        productToCube d (productVector (fun i => A (v i))))
    (himage : ∀ x y : SelectedIndex, x ≠ y →
      inner ℝ (A (F x)) (A (F y)) = 0)
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ s : ℕ, ∀ j : Fin (2^s),
      c * ((2:ℝ)^(-r))^s ≤ ‖A (F ⟨s,j⟩)‖) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c₁ * (k:ℝ)^(-r+1/2) *
          (Real.log (k:ℝ))^(r*((d-1:ℕ):ℝ))) ≤ approximationNumber T k := by
  let TL2 := (cubeProfileToL2 (d:=d)).comp T
  have hf : ∀ v : Fin d → UnitL2,
      TL2 (productToCube d (productVector v)) =
        productToCube d (productVector (fun i => A (v i))) := hfactor
  have hρ : 0 ≤ (2:ℝ)^(-r) := by positivity
  have hlayer : ∀ N k : ℕ, 0 ≤ N → 1 ≤ k →
      k ≤ Fintype.card (LayerIndex d N) →
      ENNReal.ofReal (c^d * (2:ℝ)^(-r*(N:ℝ)) *
        Real.sqrt ((Fintype.card (LayerIndex d N)-(k-1):ℕ):ℝ)) ≤
        approximationNumber T k := by
    intro N k _ hk hkD
    let e := selectedLayerSource (d:=d) (N:=N) F
    have he : Orthonormal ℝ e := selectedLayerSource_orthonormal F hF
    have horth : ∀ i j, i ≠ j →
        inner ℝ (cubeProfileToL2 (T (e i))) (cubeProfileToL2 (T (e j))) = 0 :=
      selectedLayerImage_pairwise_orthogonal F A TL2 hf himage
    have hn : ∀ i, c^d * ((2:ℝ)^(-r))^N ≤ ‖cubeProfileToL2 (T (e i))‖ :=
      selectedLayerImage_norm_lower F A TL2 hf c ((2:ℝ)^(-r)) hc.le hρ hlower
    have hσ : 0 ≤ c^d * ((2:ℝ)^(-r))^N := by positivity
    have hmain := approximationNumber_lower_of_orthonormal_cube_frame
      T e he (c^d * ((2:ℝ)^(-r))^N) hσ horth hn hk hkD
    have hp : ((2:ℝ)^(-r))^N = (2:ℝ)^(-r*(N:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    simpa [hp] using hmain
  exact all_index_lower_of_layer_bound hd r (c^d) hr (pow_pos hc d) 0
    (fun k => approximationNumber T k) hlayer

end BrownianSharp.AlignmentSelectedFrameApproximationLower
