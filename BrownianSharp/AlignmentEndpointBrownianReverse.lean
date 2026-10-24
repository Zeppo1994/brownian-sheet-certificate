import BrownianSharp.AlignmentEndpointGaussianHaarLaw
import BrownianSharp.AlignmentEndpointCubeGridLimit
import BrownianSharp.AlignmentGaussianFiniteFeature
import BrownianSharp.AlignmentGaussianHaarProjection
import BrownianSharp.AlignmentGaussianHaarVariance
import BrownianSharp.AlignmentGaussianResidualMetric
import BrownianSharp.CameronMartinFeatureModulus
import BrownianSharp.AlignmentExponentialDiagonalDilation
import BrownianSharp.SmoothCoefficientEvents
import BrownianSharp.AlignmentExponentialReverseInversion

/-! Actual finite-Haar Gaussian construction for the dyadic Brownian-sheet
small-ball lower bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace BrownianSharp.AlignmentEndpointBrownianReverse

open BrownianSharp.CameronMartin
open BrownianSharp.AlignmentGaussianHaarProjection
open BrownianSharp.AlignmentGaussianFiniteFeature
open BrownianSharp.AlignmentEndpointGaussianHaarLaw
open BrownianSharp.AlignmentEndpointCubeGridLimit
open BrownianSharp.AlignmentExponentialDiagonalDilation
open BrownianSharp.AlignmentGaussianChainingRate
open HaarQuarter

def scaledHaarFeaturePath {d N M : ℕ} (a : FiniteHaarIndex d M) :
    C(BrownianCubeAnchor d, ℝ) := by
  refine ⟨fun x => gradeScale N (finiteHaarGrade a) *
    ⟪featureVector x, finiteHaarVector a⟫, ?_⟩
  exact continuous_const.mul
    ((CameronMartin.featureVector_continuous d).inner continuous_const)

theorem scaledHaarFeaturePath_apply {d N M : ℕ}
    (a : FiniteHaarIndex d M) (x : BrownianCubeAnchor d) :
    scaledHaarFeaturePath (N := N) (M := M) a x =
      gradeScale N (finiteHaarGrade a) *
        ⟪featureVector x, finiteHaarVector a⟫ := rfl

theorem scaledHaarFeaturePath_square_sum {d N M : ℕ}
    (x : BrownianCubeAnchor d) :
    (∑ a : FiniteHaarIndex d M,
      (scaledHaarFeaturePath (N := N) (M := M) a x)^2) =
      ‖gradeScaledFeature (N := N) (M := M) (featureVector x)‖^2 := by
  rw [gradeScaledFeature_norm_sq]
  apply Finset.sum_congr rfl
  intro a ha
  rw [scaledHaarFeaturePath_apply]

theorem scaledHaarFeaturePath_square_sum_le {d N M : ℕ} (hd : 0 < d)
    (x : BrownianCubeAnchor d) :
    (∑ a : FiniteHaarIndex d M,
      (scaledHaarFeaturePath (N := N) (M := M) a x)^2) ≤
      ((N+1:ℝ)^(d-1))/(2:ℝ)^N *
        (2 + BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1/2) (d-1)) := by
  rw [scaledHaarFeaturePath_square_sum]
  have hpoint := grade_scaled_feature_variance_le (d:=d) (N:=N) (M:=M)
    hd x.val x.property
  have hunif := grade_scaled_variance_sum_uniform d N M hd
  exact hpoint.trans hunif

theorem scaledHaarFeaturePath_increment_square_sum_le {d N M : ℕ}
    (x y : BrownianCubeAnchor d) :
    (∑ a : FiniteHaarIndex d M,
      (scaledHaarFeaturePath (N := N) (M := M) a x -
        scaledHaarFeaturePath (N := N) (M := M) a y)^2) ≤
      ‖featureVector x - featureVector y‖^2 := by
  let u : brownianCubeBoxSpan d := featureVector x-featureVector y
  have hsum : (∑ a : FiniteHaarIndex d M,
      (scaledHaarFeaturePath (N := N) (M := M) a x -
        scaledHaarFeaturePath (N := N) (M := M) a y)^2) =
      ‖gradeScaledFeature (N:=N) (M:=M) u‖^2 := by
    rw [gradeScaledFeature_norm_sq]
    apply Finset.sum_congr rfl
    intro a ha
    rw [scaledHaarFeaturePath_apply, scaledHaarFeaturePath_apply]
    congr 1
    simp only [u, inner_sub_left]
    ring_nf
  rw [hsum]
  have hcontract := gradeScaledFeature_sub_norm_le (N:=N) (M:=M)
    (featureVector x) (featureVector y)
  have hlinear : gradeScaledFeature (N:=N) (M:=M) (featureVector x) -
      gradeScaledFeature (N:=N) (M:=M) (featureVector y) =
      gradeScaledFeature (N:=N) (M:=M) u := by
    simp only [gradeScaledFeature]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    calc
      (gradeScale N (finiteHaarGrade a) *
          ⟪featureVector x, finiteHaarVector a⟫) • finiteHaarVector a -
        (gradeScale N (finiteHaarGrade a) *
          ⟪featureVector y, finiteHaarVector a⟫) • finiteHaarVector a =
        (gradeScale N (finiteHaarGrade a) *
          ⟪featureVector x, finiteHaarVector a⟫ -
         gradeScale N (finiteHaarGrade a) *
          ⟪featureVector y, finiteHaarVector a⟫) • finiteHaarVector a := by
            module
      _ = (gradeScale N (finiteHaarGrade a) *
          ⟪featureVector x - featureVector y, finiteHaarVector a⟫) •
            finiteHaarVector a := by
              rw [inner_sub_left]
              congr 1
              ring_nf
      _ = (gradeScale N (finiteHaarGrade a) *
          ⟪u, finiteHaarVector a⟫) • finiteHaarVector a := by rfl
  have hsq : ‖gradeScaledFeature (N:=N) (M:=M) u‖^2 ≤
      ‖featureVector x-featureVector y‖^2 := by
    dsimp [u]
    rw [← hlinear]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hcontract
  exact hsq

private theorem boxFeature_metric_sq_le_dist_mul {d : ℕ}
    (x y : BrownianCubeAnchor d) :
    ‖featureVector x-featureVector y‖^2 ≤ (d:ℝ)*dist x y := by
  have hmetric := CameronMartin.featureVector_sub_norm_sq_le x y
  have hcoord : ∀ i : Fin d, |x.val i-y.val i| ≤ dist x y := by
    intro i
    have hnorm : ‖(x.val-y.val) i‖ ≤ ‖x.val-y.val‖ := norm_le_pi_norm _ i
    calc
      |x.val i-y.val i| = ‖(x.val-y.val) i‖ := by rw [Real.norm_eq_abs]; simp
      _ ≤ ‖x.val-y.val‖ := hnorm
      _ = dist x y := by
        change ‖x.val-y.val‖ = dist x.val y.val
        rw [dist_eq_norm]
  have hsum : (∑ i : Fin d, |x.val i-y.val i|) ≤ (d:ℝ)*dist x y := by
    calc
      _ ≤ ∑ _i : Fin d, dist x y := Finset.sum_le_sum (fun i hi=>hcoord i)
      _ = (d:ℝ)*dist x y := by simp
  have hmetric' : ‖featureVector x-featureVector y‖^2 ≤
      ∑ i : Fin d, |x.val i-y.val i| := by
    simpa [CameronMartin.featureVector, CameronMartin.AmbientL2] using hmetric
  exact hmetric'.trans hsum

theorem scaledHaarFeaturePath_increment_bound {d N M : ℕ}
    (x y : BrownianCubeAnchor d) :
    (∑ a : FiniteHaarIndex d M,
      (scaledHaarFeaturePath (N := N) (M := M) a x -
        scaledHaarFeaturePath (N := N) (M := M) a y)^2) ≤
      (d:ℝ)*dist x y := by
  exact (scaledHaarFeaturePath_increment_square_sum_le x y).trans
    (boxFeature_metric_sq_le_dist_mul x y)

def scaledFiniteGaussianPath {d N M : ℕ}
    (z : FiniteHaarIndex d M → ℝ) : C(BrownianCubeAnchor d,ℝ) :=
  finiteGaussianFeaturePath (scaledHaarFeaturePath (N:=N) (M:=M)) z

private def varianceBudgetConstant (d : ℕ) : ℝ :=
  2 + BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1/2) (d-1)

private theorem varianceBudgetConstant_pos (d : ℕ) : 0 < varianceBudgetConstant d := by
  unfold varianceBudgetConstant
  have h := BrownianSharp.AlignmentGeometricRanks.polynomialBudget_nonneg
    (q := (1/2:ℝ)) (by norm_num) (d-1)
  linarith

private def expectedRadiusConstant (d : ℕ) : ℝ :=
  chainingConstant d * (Real.sqrt (varianceBudgetConstant d) + Real.sqrt (2*(d:ℝ)))

theorem scaledFiniteGaussianPath_expected_norm_le {d N M : ℕ} (hd : 2≤d) :
    Integrable (fun z : FiniteHaarIndex d M → ℝ => ‖scaledFiniteGaussianPath (N:=N) (M:=M) z‖)
      (productStandardGaussian (FiniteHaarIndex d M)) ∧
    (∫ z : (FiniteHaarIndex d M → ℝ),
      ‖scaledFiniteGaussianPath (N:=N) (M:=M) z‖
        ∂productStandardGaussian (FiniteHaarIndex d M)) ≤
      BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile d
        (expectedRadiusConstant d) N := by
  let C := varianceBudgetConstant d
  let σ := Real.sqrt (C * ((2:ℝ)^N)⁻¹ * ((N+1:ℝ)^(d-1)))
  let v : FiniteHaarIndex d M → C(BrownianCubeAnchor d,ℝ) :=
    scaledHaarFeaturePath (N:=N) (M:=M)
  have hC : 0<C := by dsimp [C]; exact varianceBudgetConstant_pos d
  have hσ : 0≤σ := Real.sqrt_nonneg _
  have hd0 : 0<d := by omega
  have hd1 : 1≤d := by omega
  have hvar : ∀x : BrownianCubeAnchor d, (∑ a, (v a x)^2)≤σ^2 := by
    intro x
    calc
      _ ≤ ((N+1:ℝ)^(d-1))/(2:ℝ)^N * C := by
        simpa [v,C,varianceBudgetConstant,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
          scaledHaarFeaturePath_square_sum_le (d:=d) (N:=N) (M:=M) hd0 x
      _ = σ^2 := by
        dsimp [σ]
        rw [Real.sq_sqrt (by positivity)]
        ring_nf
  have hinc : ∀x y : BrownianCubeAnchor d,
      (∑ a, (v a x-v a y)^2)≤(d:ℝ)*dist x y := by
    intro x y
    exact scaledHaarFeaturePath_increment_bound x y
  have hR : 0≤(d:ℝ) := by positivity
  have hExpected := finiteGaussianFeaturePath_expected_norm
    (v:=v) σ (d:ℝ) hσ hR hvar hinc N
  refine ⟨?_, ?_⟩
  · simpa [scaledFiniteGaussianPath,v] using hExpected.1
  · have hbudget := dyadic_chaining_budget_le (d:=d) (by omega) N C
      (Real.sqrt (2*(d:ℝ))) hC.le (Real.sqrt_nonneg _)
    have hsigma : σ = Real.sqrt (C*((2:ℝ)^N)⁻¹*((N+1:ℝ)^(d-1))) := by
      dsimp [σ]
    have hmean := hExpected.2
    rw [hsigma] at hmean
    change (∫ z : (FiniteHaarIndex d M → ℝ),
      ‖finiteGaussianFeaturePath v z‖ ∂productStandardGaussian (FiniteHaarIndex d M)) ≤ _
    calc
      _ ≤ chainingConstant d*Real.sqrt ((N:ℝ)+1)*
          (Real.sqrt (C*((2:ℝ)^N)⁻¹*((N+1:ℝ)^(d-1)))+
            Real.sqrt (2*(d:ℝ))*(2:ℝ)^(-((N:ℝ)/2))) := hmean
      _ ≤ BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile d
          (expectedRadiusConstant d) N := by
        have hexp : (2:ℝ)^(-((N:ℝ)/2)) = (2:ℝ)^(-(N:ℝ)/2) := by
          congr 1
          ring_nf
        simpa [expectedRadiusConstant, varianceBudgetConstant, C,
          BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile,
          Nat.cast_add, hexp] using hbudget

theorem scaledFiniteGaussianPath_half_mass {d N M : ℕ} (hd : 2≤d) :
    (1/2:ℝ≥0∞) ≤ productStandardGaussian (FiniteHaarIndex d M)
      {z | ‖scaledFiniteGaussianPath (N:=N) (M:=M) z‖ ≤
        BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile d
          (4*expectedRadiusConstant d) N} := by
  have hExpected := scaledFiniteGaussianPath_expected_norm_le (d:=d) (N:=N) (M:=M) hd
  let base : ℝ := (2:ℝ)^(-(N:ℝ)/2)*((N+1:ℝ)^((d:ℝ)/2))
  let cutoff : ℝ := 2*expectedRadiusConstant d*base
  have hcutoff : 0<cutoff := by
    dsimp [cutoff,base,expectedRadiusConstant]
    have hc := chainingConstant_pos d
    have hb := varianceBudgetConstant_pos d
    positivity
  have hmeas : Measurable (fun z : FiniteHaarIndex d M → ℝ =>
      ‖scaledFiniteGaussianPath (N:=N) (M:=M) z‖) := by
    exact (continuous_norm.comp
      (finiteGaussianFeaturePath_continuous (scaledHaarFeaturePath (N:=N) (M:=M)))).measurable
  have hmass := BrownianSharp.gaussian_nonneg_energy_cutoff_mass
    (productStandardGaussian (FiniteHaarIndex d M))
    (fun z=>‖scaledFiniteGaussianPath (N:=N) (M:=M) z‖)
    hmeas hExpected.1 (fun _=>norm_nonneg _) (M:=cutoff) hcutoff ?_
  · have hRadius : 2*cutoff =
      BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile d
        (4*expectedRadiusConstant d) N := by
      dsimp [cutoff,base,
        BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile]
      rw [Nat.cast_add]
      ring_nf
    simpa only [hRadius] using hmass
  · have hmean : (∫ z : (FiniteHaarIndex d M → ℝ),
        ‖scaledFiniteGaussianPath (N:=N) (M:=M) z‖
          ∂productStandardGaussian (FiniteHaarIndex d M)) ≤ cutoff := by
      have hcp : 0≤expectedRadiusConstant d := by
        unfold expectedRadiusConstant
        exact mul_nonneg (chainingConstant_pos d).le
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have hbase : 0≤base := by dsimp [base]; positivity
      calc
        _ ≤ expectedRadiusConstant d * base := by
          simpa [base,mul_assoc,
            BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile,
            Nat.cast_add] using hExpected.2
        _ ≤ 2*expectedRadiusConstant d*base := by nlinarith
      
    exact hmean

/-- One radius constant works for every Haar cutoff and every dyadic level. -/
theorem exists_scaledFiniteGaussianPath_half_mass {d : ℕ} (hd : 2≤d) :
    ∃ A : ℝ, 0<A ∧ ∀ N M : ℕ,
      (1/2:ℝ≥0∞) ≤ productStandardGaussian (FiniteHaarIndex d M)
        {z | ‖scaledFiniteGaussianPath (N:=N) (M:=M) z‖ ≤
          BrownianSharp.AlignmentExponentialReverseInversion.radiusProfile d A N} := by
  refine ⟨4*expectedRadiusConstant d, ?_, ?_⟩
  · unfold expectedRadiusConstant
    have hc := chainingConstant_pos d
    have hb := varianceBudgetConstant_pos d
    have hroot : 0< Real.sqrt (varianceBudgetConstant d) :=
      Real.sqrt_pos.2 hb
    positivity
  · intro N M
    exact scaledFiniteGaussianPath_half_mass hd

end BrownianSharp.AlignmentEndpointBrownianReverse
