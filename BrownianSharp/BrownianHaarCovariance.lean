import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import BrownianSharp.IntegratedHaarTent

/-! Finite-dimensional Gaussian consequences of an honest isonormal family.

The Brownian-sheet application supplies stochastic integrals `W f` and proves
the covariance identity from the sheet covariance.  This interface keeps the
joint Gaussian and covariance inputs explicit; it does not assume independent
Haar coefficients. -/

open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace HaarQuarter

/-- A centered jointly Gaussian isonormal family on a real Hilbert space.
The finite-family Gaussian field is the definition of joint Gaussianity; the
separate covariance field is the isometry needed for the Brownian-sheet
application. -/
structure IsonormalGaussianFamily (H Ω ι : Type*) [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] (P : Measure Ω) where
  eval : H → Ω → ℝ
  jointlyGaussian : (v : ι → H) →
    HasGaussianLaw (fun ω i => eval (v i) ω) P
  measurable_eval : ∀ f : H, Measurable (fun ω => eval f ω)
  mean_zero : ∀ f : H, ∫ ω, eval f ω ∂P = 0
  covariance_eq_inner : ∀ f g : H,
    cov[fun ω ↦ eval f ω, fun ω ↦ eval g ω; P] = ⟪f, g⟫

namespace IsonormalGaussianFamily

variable {H Ω ι : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace Ω]
  {P : Measure Ω} (W : IsonormalGaussianFamily H Ω ι P)

/-- Every stochastic integral has the centered Gaussian law with variance
equal to the squared Hilbert norm of its integrand. -/
theorem coordinate_law (v : ι → H) (i : ι) :
    P.map (fun ω => W.eval (v i) ω) =
      gaussianReal 0 (⟪v i, v i⟫).toNNReal := by
  have hjoint := W.jointlyGaussian v
  have hX := hjoint.eval i
  have hmean : (∫ ω, W.eval (v i) ω ∂P) = 0 := W.mean_zero (v i)
  have hvar : Var[fun ω => W.eval (v i) ω; P] = ⟪v i, v i⟫ := by
    rw [← covariance_self hX.aemeasurable, W.covariance_eq_inner]
  rw [hX.map_eq_gaussianReal, hmean, hvar]

/-- A deterministic scaling of an isonormal coordinate has the expected
centered Gaussian variance. -/
theorem scaled_coordinate_law (v : ι → H) (c : ℝ) (i : ι) :
    P.map (fun ω => c * W.eval (v i) ω) =
      gaussianReal 0
        (.mk (c ^ 2) (sq_nonneg _) * (⟪v i, v i⟫).toNNReal) := by
  have hcomp : (fun ω => c * W.eval (v i) ω) =
      (fun y => c * y) ∘ (fun ω => W.eval (v i) ω) := by
    rfl
  rw [hcomp]
  rw [← Measure.map_map (by fun_prop) (W.measurable_eval (v i))]
  rw [W.coordinate_law]
  rw [gaussianReal_map_const_mul]
  simp

/-- The covariance of scaled stochastic integrals is the Hilbert inner
product with both deterministic factors displayed. -/
theorem scaled_covariance (v : ι → H) (c : ι → ℝ)
    (i j : ι) :
    cov[fun ω ↦ c i * W.eval (v i) ω,
        fun ω ↦ c j * W.eval (v j) ω; P] =
      c i * c j * ⟪v i, v j⟫ := by
  have hleft : (fun ω => c i * W.eval (v i) ω) =
      fun ω => W.eval (v i) ω * c i := by
    funext ω
    ring
  have hright : (fun ω => c j * W.eval (v j) ω) =
      fun ω => W.eval (v j) ω * c j := by
    funext ω
    ring
  rw [hleft, hright, covariance_mul_const_left, covariance_mul_const_right,
    W.covariance_eq_inner]
  ring

/-- Orthogonal isonormal vectors give independent scaled Gaussian
coordinates.  We derive independence from the joint Gaussian law and the
covariance identity rather than assuming it. -/
theorem iIndepFun_of_orthogonal
    (v : ι → H) (c : ι → ℝ)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) :
    iIndepFun (fun i ω => c i * W.eval (v i) ω) P := by
  classical
  have hindep : iIndepFun (fun i ω => W.eval (v i) ω) P := by
    apply HasGaussianLaw.iIndepFun_of_covariance_eq_zero
      (W.jointlyGaussian v)
    intro i j hij
    rw [W.covariance_eq_inner, horth i j hij]
  have hscaled := hindep.comp (fun i x => c i * x)
    (fun _ => measurable_const.mul measurable_id)
  simpa [Function.comp_def] using hscaled

end IsonormalGaussianFamily

/-- Euclidean volume of a dyadic product rectangle. -/
noncomputable def integratedTentDyadicVolume {d : ℕ}
    (profile : Fin d → ℕ) : ℝ :=
  ∏ i, (integratedTentDyadicRight (profile i) 0 -
    integratedTentDyadicLeft (profile i) 0)

/-- A finite family of integrated Brownian-sheet Haar tents at one common
rectangle shape is orthogonal in the actual integrand Hilbert space whenever
its cell vectors are distinct. -/
theorem dyadicTentVectorFamily_orthogonal {d : ℕ} {ι : Type*} [Fintype ι]
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k) :
    ∀ i j, i ≠ j →
      ⟪tensorIntegratedTentDyadicLp profile (cells i),
        tensorIntegratedTentDyadicLp profile (cells j)⟫ = 0 := by
  intro i j hij
  obtain ⟨k, hk⟩ := hseparate i j hij
  exact tensorIntegratedTentDyadicLp_inner_eq_zero_of_coordinate_ne
    profile (cells i) (cells j) k hk

/-- For any isonormal realization on the Brownian-sheet integrand space,
integrated Haar coefficients from a common shape and distinct cells are
independent.  Independence follows from joint Gaussianity and the proved
orthogonality of the deterministic tent vectors. -/
theorem dyadicTentGaussianFamily_independent {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k) :
    iIndepFun (fun i ω => W.eval
      (tensorIntegratedTentDyadicLp profile (cells i)) ω) P := by
  have horth := dyadicTentVectorFamily_orthogonal profile cells hseparate
  have hindep := W.iIndepFun_of_orthogonal
    (fun i => tensorIntegratedTentDyadicLp profile (cells i))
    (fun _ => 1) horth
  simpa using hindep

/-- Each unscaled integrated Haar coefficient has the centered Gaussian law
whose variance is exactly the tent's squared L² norm. -/
theorem dyadicTentGaussianFamily_coordinate_law {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ) (i : ι) :
    P.map (fun ω => W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω) =
      gaussianReal 0
        (((∏ k, (integratedTentDyadicRight (profile k) ((cells i) k) -
          integratedTentDyadicLeft (profile k) ((cells i) k))) ^ 3 /
          (12 : ℝ) ^ d).toNNReal) := by
  have hnorm : ‖tensorIntegratedTentDyadicLp profile (cells i)‖ ^ 2 =
      (∏ k, (integratedTentDyadicRight (profile k) ((cells i) k) -
        integratedTentDyadicLeft (profile k) ((cells i) k))) ^ 3 /
        (12 : ℝ) ^ d := by
    rw [← real_inner_self_eq_norm_sq]
    exact tensorIntegratedTentDyadicLp_inner_self profile (cells i)
  simpa [hnorm] using
    W.coordinate_law
      (fun j => tensorIntegratedTentDyadicLp profile (cells j)) i

/-- The same independent coefficient family after its natural `|R|⁻¹`
normalization.  The variance is displayed in factorized form; the norm theorem
above identifies it with `|R| / 12^d` by real algebra. -/
theorem normalizedDyadicTentGaussianFamily_independent {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k)
    (c : ι → ℝ) :
    iIndepFun (fun i ω => c i * W.eval
      (tensorIntegratedTentDyadicLp profile (cells i)) ω) P := by
  have horth := dyadicTentVectorFamily_orthogonal profile cells hseparate
  exact W.iIndepFun_of_orthogonal
    (fun i => tensorIntegratedTentDyadicLp profile (cells i)) c horth

/-- A dyadic rectangle's volume is strictly positive. -/
theorem integratedTentDyadicVolume_pos {d : ℕ} (profile : Fin d → ℕ) :
    0 < integratedTentDyadicVolume profile := by
  unfold integratedTentDyadicVolume
  apply Finset.prod_pos
  intro i hi
  simp [integratedTentDyadicLeft, integratedTentDyadicRight]

/-- The manuscript's signed coefficient normalization for the positive tent
representative. -/
noncomputable def dyadicBrownianHaarCoefficientScale {d : ℕ}
    (profile : Fin d → ℕ) : ℝ :=
  (-1 : ℝ) ^ d * (integratedTentDyadicVolume profile)⁻¹

/-- The signed Haar coefficient scale has exact variance `|R|/12^d`. -/
theorem dyadicBrownianHaarCoefficient_variance {d : ℕ}
    (profile : Fin d → ℕ) :
    (dyadicBrownianHaarCoefficientScale profile) ^ 2 *
        ((integratedTentDyadicVolume profile) ^ 3 / (12 : ℝ) ^ d) =
      integratedTentDyadicVolume profile / (12 : ℝ) ^ d := by
  have hsign : ((-1 : ℝ) ^ d) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm d 2, pow_mul]
    norm_num
  have hV := integratedTentDyadicVolume_pos profile
  have hn : integratedTentDyadicVolume profile ≠ 0 := hV.ne'
  have h12 : (12 : ℝ) ^ d ≠ 0 := by positivity
  unfold dyadicBrownianHaarCoefficientScale
  rw [mul_pow, hsign]
  field_simp

/-- The signed coefficient family at one shape is independent, since the
sign and volume normalization are deterministic common factors. -/
theorem dyadicBrownianHaarCoefficient_independent {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k) :
    iIndepFun (fun i ω => dyadicBrownianHaarCoefficientScale profile *
      W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω) P := by
  exact normalizedDyadicTentGaussianFamily_independent
    P W profile cells hseparate (fun _ => dyadicBrownianHaarCoefficientScale profile)

/-- The product of side lengths is independent of the cell vector. -/
theorem integratedTentDyadicCellVolume_eq {d : ℕ}
    (profile cells : Fin d → ℕ) :
    (∏ i, (integratedTentDyadicRight (profile i) (cells i) -
      integratedTentDyadicLeft (profile i) (cells i))) =
      integratedTentDyadicVolume profile := by
  unfold integratedTentDyadicVolume
  apply Finset.prod_congr rfl
  intro i hi
  dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
  have hpow : (2 : ℝ) ^ profile i ≠ 0 := by positivity
  field_simp
  <;> ring

/-- The signed manuscript coefficient is Gaussian with the exact factorized
variance whose real value is `|R|/12^d`. -/
theorem dyadicBrownianHaarCoefficient_coordinate_law {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ) (i : ι) :
    P.map (fun ω => dyadicBrownianHaarCoefficientScale profile *
        W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω) =
      gaussianReal 0
        (.mk ((dyadicBrownianHaarCoefficientScale profile) ^ 2)
          (sq_nonneg _) *
          (((integratedTentDyadicVolume profile) ^ 3 /
            (12 : ℝ) ^ d).toNNReal)) := by
  have hnorm : ‖tensorIntegratedTentDyadicLp profile (cells i)‖ ^ 2 =
      (integratedTentDyadicVolume profile) ^ 3 /
        (12 : ℝ) ^ d := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← integratedTentDyadicCellVolume_eq profile (cells i)]
    exact tensorIntegratedTentDyadicLp_inner_self profile (cells i)
  simpa [hnorm] using
    W.scaled_coordinate_law
      (fun j => tensorIntegratedTentDyadicLp profile (cells j))
      (dyadicBrownianHaarCoefficientScale profile) i

/-- Real algebra for the Haar coefficient normalization: the tent variance
`|R|^3/12^d`, multiplied by `|R|^{-2}`, is `|R|/12^d`. -/
theorem integratedTentDyadic_normalized_variance {d : ℕ}
    (profile : Fin d → ℕ) :
    (integratedTentDyadicVolume profile)⁻¹ ^ 2 *
        ((integratedTentDyadicVolume profile) ^ 3 / (12 : ℝ) ^ d) =
      integratedTentDyadicVolume profile / (12 : ℝ) ^ d := by
  have hV := integratedTentDyadicVolume_pos profile
  have hn : integratedTentDyadicVolume profile ≠ 0 := hV.ne'
  have h12 : (12 : ℝ) ^ d ≠ 0 := by positivity
  field_simp

/-- The natural volume-normalized integrated Haar coefficient is Gaussian.
Its ENNReal variance factors as `|R|^{-2} · (|R|^3/12^d)`; the preceding
real identity reduces this exactly to the manuscript's `|R|/12^d`. -/
theorem normalizedDyadicTentGaussianFamily_coordinate_law {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ) (i : ι) :
    P.map (fun ω => (integratedTentDyadicVolume profile)⁻¹ *
        W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω) =
      gaussianReal 0
        (.mk ((integratedTentDyadicVolume profile)⁻¹ ^ 2)
          (sq_nonneg _) *
          (((integratedTentDyadicVolume profile) ^ 3 /
            (12 : ℝ) ^ d).toNNReal)) := by
  have hnorm : ‖tensorIntegratedTentDyadicLp profile (cells i)‖ ^ 2 =
      (integratedTentDyadicVolume profile) ^ 3 /
        (12 : ℝ) ^ d := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← integratedTentDyadicCellVolume_eq profile (cells i)]
    exact tensorIntegratedTentDyadicLp_inner_self profile (cells i)
  simpa [hnorm] using
    W.scaled_coordinate_law
      (fun j => tensorIntegratedTentDyadicLp profile (cells j))
      ((integratedTentDyadicVolume profile)⁻¹) i

/-- The scalar that turns an integrated tent into a unit vector in the
Brownian-sheet integrand Hilbert space. -/
noncomputable def dyadicTentUnitScale {d : ℕ} (profile : Fin d → ℕ) : ℝ :=
  Real.sqrt ((12 : ℝ) ^ d / (integratedTentDyadicVolume profile) ^ 3)

/-- Unit-norm integrated-tent vectors, whose isonormal images are the standard
Gaussian coordinates underlying the same-shape coefficient family. -/
noncomputable def standardizedDyadicTentVector {d : ℕ}
    (profile cells : Fin d → ℕ) :
    Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) :=
  dyadicTentUnitScale profile • tensorIntegratedTentDyadicLp profile cells

/-- The exact variance calculation normalizes each tent vector to norm one. -/
theorem standardizedDyadicTentVector_inner_self {d : ℕ}
    (profile cells : Fin d → ℕ) :
    ⟪standardizedDyadicTentVector profile cells,
      standardizedDyadicTentVector profile cells⟫ = 1 := by
  rw [standardizedDyadicTentVector, real_inner_smul_left, real_inner_smul_right,
    tensorIntegratedTentDyadicLp_inner_self]
  have hV := integratedTentDyadicVolume_pos profile
  have hratio : dyadicTentUnitScale profile ^ 2 =
      (12 : ℝ) ^ d / (integratedTentDyadicVolume profile) ^ 3 := by
    rw [dyadicTentUnitScale, Real.sq_sqrt]
    positivity
  rw [integratedTentDyadicCellVolume_eq profile cells]
  have h12 : (12 : ℝ) ^ d ≠ 0 := by positivity
  have hV3 : (integratedTentDyadicVolume profile) ^ 3 ≠ 0 := by positivity
  calc
    dyadicTentUnitScale profile *
        (dyadicTentUnitScale profile *
          ((integratedTentDyadicVolume profile) ^ 3 / (12 : ℝ) ^ d)) =
        dyadicTentUnitScale profile ^ 2 *
          ((integratedTentDyadicVolume profile) ^ 3 / (12 : ℝ) ^ d) := by ring
    _ = 1 := by rw [hratio]; field_simp

/-- Standardized integrated tents give standard normal coordinates. -/
theorem standardizedDyadicTentGaussianFamily_coordinate_law {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ) (i : ι) :
    P.map (fun ω => W.eval (standardizedDyadicTentVector profile (cells i)) ω) =
      gaussianReal 0 1 := by
  have hunit : ⟪standardizedDyadicTentVector profile (cells i),
      standardizedDyadicTentVector profile (cells i)⟫ = 1 :=
    standardizedDyadicTentVector_inner_self profile (cells i)
  have hnorm : ‖standardizedDyadicTentVector profile (cells i)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hunit
  simpa [hnorm] using
    W.coordinate_law
      (fun j => standardizedDyadicTentVector profile (cells j)) i

/-- At one fixed rectangle shape, the standardized tent coordinates are an
independent standard-normal family for every isonormal realization. -/
theorem standardizedDyadicTentGaussianFamily_independent {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k) :
    iIndepFun (fun i ω => W.eval
      (standardizedDyadicTentVector profile (cells i)) ω) P := by
  have horth := dyadicTentVectorFamily_orthogonal profile cells hseparate
  have horth' : ∀ i j, i ≠ j →
      ⟪standardizedDyadicTentVector profile (cells i),
        standardizedDyadicTentVector profile (cells j)⟫ = 0 := by
    intro i j hij
    rw [standardizedDyadicTentVector, standardizedDyadicTentVector,
      real_inner_smul_left, real_inner_smul_right, horth i j hij]
    ring
  have hindep := W.iIndepFun_of_orthogonal
    (fun i => standardizedDyadicTentVector profile (cells i))
    (fun _ => 1) horth'
  simpa using hindep

/-- The volume-normalized coefficients, standardized to variance one, are
standard Gaussian coordinates by the scaled isonormal law and the exact tent
variance calculation. -/
theorem standardizedDyadicTentCoefficient_coordinate_law {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ) (i : ι) :
    P.map (fun ω => dyadicTentUnitScale profile *
        W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω) =
      gaussianReal 0 1 := by
  have hnorm : ⟪tensorIntegratedTentDyadicLp profile (cells i),
      tensorIntegratedTentDyadicLp profile (cells i)⟫ =
      (integratedTentDyadicVolume profile) ^ 3 / (12 : ℝ) ^ d := by
    rw [tensorIntegratedTentDyadicLp_inner_self,
      integratedTentDyadicCellVolume_eq]
  have hV := integratedTentDyadicVolume_pos profile
  have hratio : dyadicTentUnitScale profile ^ 2 =
      (12 : ℝ) ^ d / (integratedTentDyadicVolume profile) ^ 3 := by
    rw [dyadicTentUnitScale, Real.sq_sqrt]
    positivity
  have hscale : dyadicTentUnitScale profile ^ 2 *
      ((integratedTentDyadicVolume profile) ^ 3 / (12 : ℝ) ^ d) = 1 := by
    rw [hratio]
    have hV := integratedTentDyadicVolume_pos profile
    have hV3 : (integratedTentDyadicVolume profile) ^ 3 ≠ 0 := by positivity
    have h12 : (12 : ℝ) ^ d ≠ 0 := by positivity
    field_simp
  have hvariance :
      .mk (dyadicTentUnitScale profile ^ 2) (sq_nonneg _) *
        ((integratedTentDyadicVolume profile) ^ 3 /
          (12 : ℝ) ^ d).toNNReal = 1 := by
    ext
    have hA : 0 ≤ (integratedTentDyadicVolume profile) ^ 3 /
        (12 : ℝ) ^ d := by positivity
    simp [Real.toNNReal_of_nonneg hA, hscale]
  rw [W.scaled_coordinate_law
    (fun j => tensorIntegratedTentDyadicLp profile (cells j))
    (dyadicTentUnitScale profile) i]
  rw [hnorm, hvariance]

/-- At one fixed shape, the variance-one normalizations of the actual
volume-normalized tent integrals remain independent. -/
theorem standardizedDyadicTentCoefficient_independent {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k) :
    iIndepFun (fun i ω => dyadicTentUnitScale profile *
      W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω) P := by
  exact normalizedDyadicTentGaussianFamily_independent
    P W profile cells hseparate (fun _ => dyadicTentUnitScale profile)

/-- The full finite vector of standardized same-shape tent coefficients has
the product standard-Gaussian law. This is the exact law hypothesis needed by
the existing fine-energy application, before reindexing a cell type by `Fin`. -/
theorem standardizedDyadicTentCoefficient_joint_law {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] [IsProbabilityMeasure P]
    {P : Measure Ω}
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k) :
    P.map (fun ω i => dyadicTentUnitScale profile *
        W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let G : ι → Ω → ℝ := fun i ω => dyadicTentUnitScale profile *
    W.eval (tensorIntegratedTentDyadicLp profile (cells i)) ω
  have hG : ∀ i, Measurable (G i) := by
    intro i
    dsimp [G]
    exact measurable_const.mul (W.measurable_eval _)
  have hLaw : ∀ i, HasLaw (G i) (gaussianReal 0 1) P := by
    intro i
    exact ⟨(hG i).aemeasurable, by
      simpa [G] using standardizedDyadicTentCoefficient_coordinate_law
        P W profile cells i⟩
  have hindep : iIndepFun G P := by
    simpa [G] using standardizedDyadicTentCoefficient_independent
      P W profile cells hseparate
  exact (hindep.hasLaw_pi hLaw).map_eq

/-- Reindex a finite rectangular-cell family by any `Fin K` equivalence. This
is the product-law interface expected by the fine-energy theorem. -/
theorem standardizedDyadicTentCoefficient_joint_law_fin {d K : ℕ}
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] [IsProbabilityMeasure P]
    {P : Measure Ω}
    (e : Fin K ≃ ι)
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ)))) Ω ι P)
    (profile : Fin d → ℕ) (cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k, cells i k ≠ cells j k) :
    P.map (fun ω i => dyadicTentUnitScale profile *
        W.eval (tensorIntegratedTentDyadicLp profile (cells (e i))) ω) =
      Measure.pi (fun _ : Fin K => gaussianReal 0 1) := by
  let G : Fin K → Ω → ℝ := fun i ω => dyadicTentUnitScale profile *
    W.eval (tensorIntegratedTentDyadicLp profile (cells (e i))) ω
  have hG : ∀ i, Measurable (G i) := by
    intro i
    dsimp [G]
    exact measurable_const.mul (W.measurable_eval _)
  have hLaw : ∀ i, HasLaw (G i) (gaussianReal 0 1) P := by
    intro i
    exact ⟨(hG i).aemeasurable, by
      simpa [G] using standardizedDyadicTentCoefficient_coordinate_law
        P W profile cells (e i)⟩
  have hindep : iIndepFun G P := by
    have hfull := standardizedDyadicTentCoefficient_independent
      P W profile cells hseparate
    simpa [G] using hfull.precomp e.injective
  exact (hindep.hasLaw_pi hLaw).map_eq

end HaarQuarter
