import BrownianSharp.AlignmentFractionalSheetMvNGram
import BrownianSharp.AlignmentSigmaFiniteL2Tensor

/-! Actual continuous whole-line tensor features for fractional Brownian sheets. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalSheetTensorFeature
open AlignmentFractionalSheetMvNGram AlignmentFractionalSheetRKHS
open AlignmentFractionalL2 AlignmentGaussianRates

def normalizedAxis (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : UnitInterval) : FullLineL2 :=
  mvNNormalizedFeature H hH0 hH1 t.val t.property.1 t.property.2

theorem normalizedAxis_inner (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (s t : UnitInterval) :
    ⟪normalizedAxis H hH0 hH1 s, normalizedAxis H hH0 hH1 t⟫ =
      fractionalCoordinateCovariance H s.val t.val :=
  mvNNormalizedFeature_gram_eq_covariance H hH0 hH1 _ _
    s.property.1 s.property.2 t.property.1 t.property.2

theorem normalizedAxis_norm_sub_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (s t : UnitInterval) :
    ‖normalizedAxis H hH0 hH1 s-normalizedAxis H hH0 hH1 t‖^2 =
      |s.val-t.val|^(2*H) := by
  have hss := normalizedAxis_inner H hH0 hH1 s s
  have htt := normalizedAxis_inner H hH0 hH1 t t
  have hst := normalizedAxis_inner H hH0 hH1 s t
  rw [real_inner_self_eq_norm_sq] at hss htt
  have hnorm := norm_sub_sq_real (normalizedAxis H hH0 hH1 s)
    (normalizedAxis H hH0 hH1 t)
  dsimp [fractionalCoordinateCovariance] at hss htt hst
  simp only [sub_self, abs_zero, Real.zero_rpow (by linarith : 2*H ≠ 0)] at hss htt
  nlinarith

theorem normalizedAxis_continuous (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    Continuous (normalizedAxis H hH0 hH1) := by
  rw [continuous_iff_continuous_dist]
  have heq : (fun p : UnitInterval × UnitInterval =>
      dist (normalizedAxis H hH0 hH1 p.1) (normalizedAxis H hH0 hH1 p.2)) =
      fun p => Real.sqrt (|p.1.val-p.2.val|^(2*H)) := by
    funext p
    rw [dist_eq_norm, ← normalizedAxis_norm_sub_sq H hH0 hH1 p.1 p.2,
      Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  exact (((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).abs.rpow_const
      (fun _ => Or.inr (by linarith))).sqrt

def normalizedAxisFamily (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    C(UnitInterval, FullLineL2) :=
  ⟨normalizedAxis H hH0 hH1, normalizedAxis_continuous H hH0 hH1⟩

abbrev FullProductL2 (d : ℕ) :=
  Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))

def fractionalSheetFeature {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) :
    C(BrownianCubeAnchor d, FullProductL2 d) where
  toFun t := AlignmentSigmaFiniteL2Tensor.tensorContinuous
    (fun i => normalizedAxis (H i) (hH i).1 (hH i).2
      (AlignmentFractionalTensorOperator.cubeCoordinate i t))
  continuous_toFun := AlignmentSigmaFiniteL2Tensor.tensorContinuous.cont.comp
    (continuous_pi fun i => (normalizedAxis_continuous (H i) (hH i).1 (hH i).2).comp
      (AlignmentFractionalTensorOperator.cubeCoordinate i).continuous)

theorem fractionalSheetFeature_gram {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) (s t : BrownianCubeAnchor d) :
    ⟪fractionalSheetFeature H hH s, fractionalSheetFeature H hH t⟫ =
      fractionalSheetCovariance H s t := by
  change ⟪AlignmentSigmaFiniteL2Tensor.productVector _,
    AlignmentSigmaFiniteL2Tensor.productVector _⟫ = _
  rw [AlignmentSigmaFiniteL2Tensor.productVector_inner]
  apply Finset.prod_congr rfl
  intro i hi
  exact normalizedAxis_inner (H i) (hH i).1 (hH i).2 _ _


theorem normalizedAxis_norm_sq (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : UnitInterval) :
    ‖normalizedAxis H hH0 hH1 t‖^2 = t.val^(2*H) := by
  have h := normalizedAxis_inner H hH0 hH1 t t
  rw [real_inner_self_eq_norm_sq] at h
  simpa [fractionalCoordinateCovariance, Real.zero_rpow (by linarith : 2*H ≠ 0)] using h

theorem normalizedAxis_norm_le_one (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (t : UnitInterval) : ‖normalizedAxis H hH0 hH1 t‖ ≤ 1 := by
  have hp : t.val^(2*H) ≤ 1 := by
    calc
      _ ≤ (1:ℝ)^(2*H) :=
        Real.rpow_le_rpow t.property.1 t.property.2 (by linarith)
      _ = 1 := Real.one_rpow _
  rw [← normalizedAxis_norm_sq H hH0 hH1 t] at hp
  nlinarith [norm_nonneg (normalizedAxis H hH0 hH1 t)]

theorem normalizedAxis_holder (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (h : ℝ) (hh : 0 < h) (hhH : h ≤ H) (s t : UnitInterval) :
    ‖normalizedAxis H hH0 hH1 s-normalizedAxis H hH0 hH1 t‖ ≤
      |s.val-t.val|^h := by
  have ha : |s.val-t.val| ≤ 1 := (abs_sub_le_iff).2
    ⟨by linarith [s.property.2,t.property.1],
      by linarith [t.property.2,s.property.1]⟩
  have hpow := Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (s.val-t.val))
    ha (show 0≤2*h by linarith) (show 2*h≤2*H by linarith)
  have hsquare : (|s.val-t.val|^h)^2 = |s.val-t.val|^(2*h) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rw [← normalizedAxis_norm_sub_sq H hH0 hH1 s t, ← hsquare] at hpow
  have hn := Real.rpow_nonneg (abs_nonneg (s.val-t.val)) h
  nlinarith [norm_nonneg (normalizedAxis H hH0 hH1 s-normalizedAxis H hH0 hH1 t)]

theorem fractionalSheetFeature_norm_le_one {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) (t : BrownianCubeAnchor d) :
    ‖fractionalSheetFeature H hH t‖ ≤ 1 := by
  change ‖AlignmentSigmaFiniteL2Tensor.productVector _‖ ≤ _
  rw [AlignmentSigmaFiniteL2Tensor.productVector_norm]
  exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _) (fun i hi =>
    normalizedAxis_norm_le_one (H i) (hH i).1 (hH i).2 _)

theorem fractionalSheetFeature_holder {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) (h : ℝ) (hh : 0<h)
    (hhH : ∀ i, h≤H i) (x y : BrownianCubeAnchor d) :
    ‖fractionalSheetFeature H hH x-fractionalSheetFeature H hH y‖ ≤
      (d:ℝ)*(dist x y)^h := by
  classical
  let T := AlignmentSigmaFiniteL2Tensor.tensorContinuous
    (μ := fun _ : Fin d => (volume : Measure ℝ))
  let v : BrownianCubeAnchor d → Fin d → FullLineL2 := fun z i =>
    normalizedAxis (H i) (hH i).1 (hH i).2
      (AlignmentFractionalTensorOperator.cubeCoordinate i z)
  have hnorm (z : BrownianCubeAnchor d) : ‖v z‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2
    intro i
    exact normalizedAxis_norm_le_one (H i) (hH i).1 (hH i).2 _
  have hdiff : ‖v x-v y‖ ≤ (dist x y)^h := by
    apply (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg dist_nonneg _)).2
    intro i
    have he := normalizedAxis_holder (H i) (hH i).1 (hH i).2 h hh (hhH i)
      (AlignmentFractionalTensorOperator.cubeCoordinate i x)
      (AlignmentFractionalTensorOperator.cubeCoordinate i y)
    have hc : |x.val i-y.val i|≤dist x y := by
      change |x.val i-y.val i|≤‖x.val-y.val‖
      simpa using norm_le_pi_norm (x.val-y.val) i
    exact he.trans (Real.rpow_le_rpow (abs_nonneg _) hc hh.le)
  have hT : ‖T‖≤1 := by
    dsimp [T,AlignmentSigmaFiniteL2Tensor.tensorContinuous]
    exact MultilinearMap.mkContinuous_norm_le _ (by norm_num)
      (fun _ => by simp [AlignmentSigmaFiniteL2Tensor.tensorMultilinear,
        AlignmentSigmaFiniteL2Tensor.productVector_norm])
  have hb := T.norm_image_sub_le (v x) (v y)
  change ‖T (v x)-T (v y)‖≤_
  calc
    _≤‖T‖*(d:ℝ)*max ‖v x‖ ‖v y‖^(d-1)*‖v x-v y‖ := by
      simpa using hb
    _≤1*(d:ℝ)*(1:ℝ)^(d-1)*(dist x y)^h := by
      have hm : max ‖v x‖ ‖v y‖≤1 := max_le (hnorm x) (hnorm y)
      gcongr
    _=(d:ℝ)*(dist x y)^h := by simp

theorem fractionalSheetFeature_squared_holder {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0<H i ∧ H i<1) (h : ℝ) (hh : 0<h)
    (hhH : ∀ i, h≤H i) (x y : BrownianCubeAnchor d) :
    ‖fractionalSheetFeature H hH x-fractionalSheetFeature H hH y‖^2 ≤
      (d:ℝ)^2*(dist x y)^(2*h) := by
  have he := fractionalSheetFeature_holder H hH h hh hhH x y
  have hp : ((dist x y)^h)^2=(dist x y)^(2*h) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul dist_nonneg]
    congr 1
    ring
  calc
    _≤((d:ℝ)*(dist x y)^h)^2 := by gcongr
    _=_ := by rw [mul_pow,hp]

end BrownianSharp.AlignmentFractionalSheetTensorFeature
