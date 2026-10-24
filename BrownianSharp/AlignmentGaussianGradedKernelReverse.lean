import BrownianSharp.AlignmentGaussianHolderGradedHalfMass
import BrownianSharp.AlignmentGaussianFiniteGridConfinement
import BrownianSharp.AlignmentGaussianGradedDilationAllGrades
import BrownianSharp.AlignmentGaussianDiagonalCoordinates
import BrownianSharp.AlignmentGeometricRanks
import Mathlib.Tactic

/-! A process-independent dyadic reverse assembly for finite Gaussian grids.
The analytic work is isolated in three explicit hypotheses: graded variance of
contracted frame coefficients, their holder increment metric, and a uniform
orthogonal projection residual. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianGradedKernelReverse

open BrownianSharp.AlignmentGaussianHolderGradedHalfMass
open BrownianSharp.AlignmentGaussianFiniteFeature
open BrownianSharp.AlignmentGaussianFiniteGridConfinement
open BrownianSharp.AlignmentGaussianGradedDilationAllGrades
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentGeometricRanks
open GaussianProjection
open HaarQuarter

/-- Finite-grid lower bound from a finite graded orthonormal source frame.
Constants are selected before the frame, grid, scale level, and Gaussian
process. Coefficient variance and holder bounds concern the diagonally scaled
frame field. -/
theorem gradedKernel_grid_lower_bound
    {d : ℕ} (β h Cvar Rvar Cdim η : ℝ) (k : ℕ)
    (hβ : 0 < β) (hh : 0 < h) (hCvar : 0 ≤ Cvar)
    (hRvar : 0 ≤ Rvar) (hCdim : 0 ≤ Cdim)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧
      ∀ {Ω I J H : Type*} [MeasurableSpace Ω]
        [Fintype I] [DecidableEq I] [Nonempty I]
        [Fintype J] [Nonempty J]
        {P : Measure Ω} [IsProbabilityMeasure P]
        [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        (X : Ω → J → ℝ) (K : C(BrownianCubeAnchor d, H))
        (e : I → H) (grade : I → ℕ) (N : ℕ)
        (x : J → BrownianCubeAnchor d) (τ : ℝ),
        HasGaussianLaw (fun ω j => X ω j) P →
        (∀ j, ∫ ω, X ω j ∂P = 0) →
        (∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P =
          ⟪K (x i), K (x j)⟫) →
        (∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) →
        (∀ z, ∑ i, (contractionScale η N (grade i) *
            ⟪K z, e i⟫)^2 ≤
          Cvar * (Real.rpow 2 (-β * (N : ℝ) / 2))^2 *
            (((N + 1 : ℕ) : ℝ)^k)) →
        (∀ z w, ∑ i, (contractionScale η N (grade i) *
            (⟪K z, e i⟫ - ⟪K w, e i⟫))^2 ≤
          Rvar * (dist z w)^(2*h)) →
        (∀ g : Fin (N + 1),
          (Fintype.card {i : I // grade i = g.val} : ℝ) ≤
            Cdim * (2 : ℝ)^g.val *
              (((g.val + 1 : ℕ) : ℝ)^k)) →
        (∀ j, ‖K (x j) - projection e (K (x j))‖ ≤ τ) →
        0 ≤ τ →
        2 * τ * Real.sqrt (Real.log (2 * (Fintype.card J : ℝ) + 2)) ≤
          (A * Real.rpow 2 (-β * (N : ℝ) / 2) *
            Real.sqrt (((N + 1 : ℕ) : ℝ)^(k + 1))) / 2 →
        ENNReal.ofReal (Real.exp (-D * (2 : ℝ)^N *
          (((N + 1 : ℕ) : ℝ)^k))) * ((1/2:ENNReal)*(1/2:ENNReal)) ≤
          P {ω | ∀ j, |X ω j| ≤
            2 * A * Real.rpow 2 (-β * (N : ℝ) / 2) *
              Real.sqrt (((N + 1 : ℕ) : ℝ)^(k + 1))} := by
  obtain ⟨A, hA, hhalf⟩ :=
    finiteGaussianFeaturePath_half_mass_of_graded_variance
      (d:=d) β h Cvar Rvar k hβ hh hCvar hRvar
  let D : ℝ := (-Real.log η) *
      (Cdim * polynomialBudget (1/2) 1)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hlog : 0 ≤ -Real.log η := by
      apply neg_nonneg.mpr
      exact Real.log_nonpos hη.le hη1
    have hbudget : 0 ≤ polynomialBudget (1/2) 1 :=
      polynomialBudget_nonneg (by norm_num) 1
    positivity
  refine ⟨A, D, hA, hD, ?_⟩
  intro Ω I J H _ _ _ _ _ _ P _ _ _ X K e grade N x τ hX hmean hcov he
    hvar hincrement hfiber hres hτ hbudget
  classical
  let scale : I → ℝ := fun i => contractionScale η N (grade i)
  let coeff : I → C(BrownianCubeAnchor d, ℝ) := fun i =>
    ⟨fun z => ⟪K z, e i⟫, K.continuous.inner continuous_const⟩
  let scaledCoeff : I → C(BrownianCubeAnchor d, ℝ) := fun i => scale i • coeff i
  let rate : ℝ := Real.rpow 2 (-β * (N : ℝ) / 2)
  let rad : ℝ := A * rate * Real.sqrt (((N + 1 : ℕ) : ℝ)^(k+1))
  have hscale_pos : ∀ i, 0 < scale i := by
    intro i
    exact contractionScale_pos hη N (grade i)
  have hscale_le : ∀ i, scale i ≤ 1 := by
    intro i
    exact contractionScale_le_one hη.le hη1 N (grade i)
  have hscaledVar : ∀ z,
      ∑ i, (scaledCoeff i z)^2 ≤
        Cvar * rate^2 * (((N + 1 : ℕ) : ℝ)^k) := by
    intro z
    simpa [scaledCoeff, coeff, scale, rate, smul_eq_mul] using hvar z
  have hscaledInc : ∀ z w,
      ∑ i, (scaledCoeff i z - scaledCoeff i w)^2 ≤
        Rvar * (dist z w)^(2*h) := by
    intro z w
    calc
      (∑ i, (scaledCoeff i z - scaledCoeff i w)^2) =
          ∑ i, (scale i * (⟪K z, e i⟫ - ⟪K w, e i⟫))^2 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [scaledCoeff, coeff, scale]
            ring
      _ ≤ Rvar * (dist z w)^(2*h) := hincrement z w
  have hmain := hhalf (ι:=I) N scaledCoeff hscaledVar hscaledInc
  have hradpos : 0 < rad := by
    dsimp [rad, rate]
    positivity
  have hmainSet : (1/2:ENNReal) ≤ productStandardGaussian I
      {z | ‖finiteGaussianFeaturePath scaledCoeff z‖ ≤ rad} := by
    simpa [rad, rate] using hmain
  have hscaled : (1/2:ENNReal) ≤ productStandardGaussian I
      {z | ∀ j, |∑ i, ⟪K (x j), e i⟫ * (scale i * z i)| ≤ rad} := by
    apply hmainSet.trans
    apply measure_mono
    intro z hz j
    have hev := (finiteGaussianFeaturePath scaledCoeff z).norm_coe_le_norm (x j)
    have hval := hev.trans hz
    have hval' : |finiteGaussianFeaturePath scaledCoeff z (x j)| ≤ rad := by
      simpa only [Real.norm_eq_abs] using hval
    rw [finiteGaussianFeaturePath_apply] at hval'
    have hsum : (∑ i, z i * scaledCoeff i (x j)) =
        ∑ i, ⟪K (x j), e i⟫ * (scale i * z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [scaledCoeff, coeff]
      ring
    rw [hsum] at hval'
    exact hval'
  have hfiber' : ∀ g : Fin (N+1),
      (Fintype.card {i : I // grade i = g.val}:ℝ) ≤
        Cdim*(2:ℝ)^g.val*(((g.val+1:ℕ):ℝ)^k) := hfiber
  have hdet := finite_graded_diagonal_dilation_product_ge_exp_all_grades
      grade Cdim η k N hCdim hη hη1 hfiber'
  have hconf := finiteGrid_confinement_of_main_half_mass
      X e (fun j => K (x j)) hX hmean hcov he scale rad τ hradpos
      hτ hscale_pos hscale_le hscaled hres hbudget
  have hdetENN : ENNReal.ofReal
      (Real.exp (-D*(2:ℝ)^N*(((N+1:ℕ):ℝ)^k))) ≤
      ENNReal.ofReal (∏ i : I, scale i) := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [D]
    have hcost : Real.exp (-(-Real.log η) *
        (Cdim*(2:ℝ)^N*(((N+1:ℕ):ℝ)^k)*polynomialBudget (1/2) 1)) ≤
        ∏ i : I, scale i := hdet
    rw [show -D*(2:ℝ)^N*(((N+1:ℕ):ℝ)^k) =
      -(-Real.log η)*(Cdim*(2:ℝ)^N*(((N+1:ℕ):ℝ)^k)*polynomialBudget (1/2) 1) by
        dsimp [D]
        ring]
    exact hcost
  have hmass' : ENNReal.ofReal (∏ i : I, scale i) *
      ((1/2:ENNReal)*(1/2:ENNReal)) ≤
      P {ω | ∀ j, |X ω j| ≤ 2*rad} := hconf
  have hfinal : ENNReal.ofReal
      (Real.exp (-D*(2:ℝ)^N*(((N+1:ℕ):ℝ)^k))) *
        ((1/2:ENNReal)*(1/2:ENNReal)) ≤
      P {ω | ∀ j, |X ω j| ≤ 2*rad} := by
    calc
      _ ≤ ENNReal.ofReal (∏ i : I, scale i) *
          ((1/2:ENNReal)*(1/2:ENNReal)) :=
        mul_le_mul_of_nonneg_right hdetENN (by positivity)
      _ ≤ _ := hmass'
  simpa [rad, rate, mul_assoc] using hfinal

/-- Sequence-of-frames version of `gradedKernel_grid_lower_bound`. Uniform
projection convergence selects a finite frame after the grid size and level
are fixed; every probabilistic and determinant constant remains independent
of that choice. -/
theorem gradedKernel_grid_lower_bound_of_uniform_frames
    {d : ℕ} (β h Cvar Rvar Cdim η : ℝ) (k : ℕ)
    (hβ : 0 < β) (hh : 0 < h) (hCvar : 0 ≤ Cvar)
    (hRvar : 0 ≤ Rvar) (hCdim : 0 ≤ Cdim)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧
      ∀ (F : ℕ → Type*)
        (hfinite : ∀ M, Fintype (F M))
        (hdecEq : ∀ M, DecidableEq (F M))
        (hnonempty : ∀ M, Nonempty (F M))
        {Ω J H : Type*} [MeasurableSpace Ω]
        [Fintype J] [Nonempty J]
        {P : Measure Ω} [IsProbabilityMeasure P]
        [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        (X : Ω → J → ℝ) (K : C(BrownianCubeAnchor d, H))
        (x : J → BrownianCubeAnchor d) (e : ∀ M, F M → H) (grade : ∀ M, F M → ℕ),
        (∀ M, letI : Fintype (F M) := hfinite M
          letI : DecidableEq (F M) := hdecEq M
          ∀ i j, ⟪e M i, e M j⟫ = if i = j then 1 else 0) →
        (∀ M N, letI : Fintype (F M) := hfinite M
          letI : DecidableEq (F M) := hdecEq M
          ∀ z, ∑ i : F M, (contractionScale η N (grade M i) *
              ⟪K z, e M i⟫)^2 ≤
            Cvar * (Real.rpow 2 (-β * (N : ℝ) / 2))^2 *
              (((N + 1 : ℕ) : ℝ)^k)) →
        (∀ M N, letI : Fintype (F M) := hfinite M
          ∀ z w, ∑ i : F M, (contractionScale η N (grade M i) *
              (⟪K z, e M i⟫ - ⟪K w, e M i⟫))^2 ≤
            Rvar * (dist z w)^(2*h)) →
        (∀ M N, letI : Fintype (F M) := hfinite M
          ∀ g : Fin (N+1),
            (Fintype.card {i : F M // grade M i = g.val} : ℝ) ≤
              Cdim * (2:ℝ)^g.val * (((g.val+1:ℕ):ℝ)^k)) →
        (∀ ε, 0 < ε → ∃ M,
          letI : Fintype (F M) := hfinite M
          letI : DecidableEq (F M) := hdecEq M
          ∀ z, ‖K z - projection (e M) (K z)‖ ≤ ε) →
        HasGaussianLaw (fun ω j => X ω j) P →
        (∀ j, ∫ ω, X ω j ∂P = 0) →
        (∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P =
          ⟪K (x i), K (x j)⟫) →
        ∀ N, ENNReal.ofReal (Real.exp (-D*(2:ℝ)^N*
          (((N+1:ℕ):ℝ)^k))) * ((1/2:ENNReal)*(1/2:ENNReal)) ≤
          P {ω | ∀ j, |X ω j| ≤
            2*A*Real.rpow 2 (-β*(N:ℝ)/2)*
              Real.sqrt (((N+1:ℕ):ℝ)^(k+1))} := by
  obtain ⟨A, D, hA, hD, hcore⟩ := gradedKernel_grid_lower_bound
    (d:=d) β h Cvar Rvar Cdim η k hβ hh hCvar hRvar hCdim hη hη1
  refine ⟨A,D,hA,hD,?_⟩
  intro F hfinite hdecEq hnonempty Ω J H _ _ _ μ _ _ _ X K x e grade
    horth hvar hincrement hfiber happrox hX hmean hcov N
  classical
  let rate : ℝ := Real.rpow 2 (-β*(N:ℝ)/2)
  let rad : ℝ := A*rate*Real.sqrt (((N+1:ℕ):ℝ)^(k+1))
  let loggrid : ℝ := Real.log (2*(Fintype.card J:ℝ)+2)
  let τ : ℝ := rad/(4*Real.sqrt loggrid)
  have hcardJ : 1 ≤ (Fintype.card J:ℝ) := by
    have hj : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ‹Nonempty J›
    have hj' : 1 ≤ Fintype.card J := by omega
    exact_mod_cast hj'
  have hlogarg : 1 < 2*(Fintype.card J:ℝ)+2 := by nlinarith
  have hlog : 0 < loggrid := by
    dsimp [loggrid]
    exact Real.log_pos hlogarg
  have hsqrtlog : 0 < Real.sqrt loggrid := Real.sqrt_pos.2 hlog
  have hrate : 0 < rate := by
    dsimp [rate]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hrad : 0 < rad := by dsimp [rad]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hbudget : 2*τ*Real.sqrt loggrid ≤ rad/2 := by
    dsimp [τ]
    have hnz : Real.sqrt loggrid ≠ 0 := ne_of_gt hsqrtlog
    field_simp
    norm_num
  obtain ⟨M,hM⟩ := happrox τ hτ
  letI : Fintype (F M) := hfinite M
  letI : DecidableEq (F M) := hdecEq M
  letI : Nonempty (F M) := hnonempty M
  have happly := hcore (X:=X) (K:=K) (e:=e M) (grade:=grade M)
    (N:=N) (x:=x) (τ:=τ) hX hmean hcov (horth M)
    (hvar M N) (hincrement M N) (hfiber M N) (fun j => hM (x j)) (le_of_lt hτ) hbudget
  simpa [rad,rate,mul_assoc] using happly

end BrownianSharp.AlignmentGaussianGradedKernelReverse
