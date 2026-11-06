import BrownianSharp.AlignmentPaperMaternFinal
import BrownianSharp.AlignmentGaussianGradedReverseClosure
import BrownianSharp.AlignmentEndpointCubeGridLimit
import Mathlib.Tactic

/-! Passage from genuine finite Gaussian grid probabilities to uniform-norm
small-ball upper logarithms. All constants precede the realization. The
analytic Matérn residual is supplied separately, not assumed in a final
Matérn statement. -/
universe u

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperMaternPathUpper

open BrownianSharp.AlignmentEndpointCubeGridLimit
open BrownianSharp.AlignmentGaussianGradedReverseClosure
open BrownianSharp.AlignmentExponentialGradedReverseInversion
open BrownianSharp.AlignmentGaussianChaining

private def finiteGridEquiv {J : Type*} [Fintype J] :
    (↥(Finset.univ : Finset J)) ≃ J :=
  { toFun := fun i => i.1
    invFun := fun j => ⟨j, Finset.mem_univ j⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro j; rfl }

private theorem gaussian_grid_law
    {α Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : α → Ω → ℝ) (hX : IsGaussianProcess X P)
    (x : J → α) : HasGaussianLaw (fun ω j => X (x j) ω) P := by
  let hp := hX.comp_right x
  have hr := hp.hasGaussianLaw Finset.univ
  let R : ((↥(Finset.univ : Finset J)) → ℝ) ≃L[ℝ] (J → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : J => ℝ) finiteGridEquiv
  have heq : (fun ω j => X (x j) ω) =
      (fun ω => R (fun i => X (x i.1) ω)) := by
    funext ω j
    rfl
  rw [heq]
  exact hr.map_equiv R

/-- The actual finite-dimensional Gaussian probability input. -/
def KernelGridLower {d : ℕ}
    (K : BrownianCubeAnchor d → BrownianCubeAnchor d → ℝ)
    (β A D : ℝ) : Prop :=
  ∀ {Ω : Type u} {J : Type} [MeasurableSpace Ω] [Fintype J] [Nonempty J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → J → ℝ) (x : J → BrownianCubeAnchor d),
    HasGaussianLaw (fun ω j => X ω j) P →
    (∀ j, ∫ ω, X ω j ∂P = 0) →
    (∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P = K (x i) (x j)) →
    ∀ N, ENNReal.ofReal (Real.exp (-D*(2:ℝ)^N *
      (((N+1:ℕ):ℝ)^(d-1)))) * ((1/2:ENNReal)*(1/2:ENNReal)) ≤
      P {ω | ∀ j, |X ω j| ≤
        2*A*Real.rpow 2 (-β*(N:ℝ)/2) * Real.sqrt (((N+1:ℕ):ℝ)^d)}

/-- Continuity and nested dyadic grids pass the finite-vector probability to
actual continuous paths; the fixed quarter is absorbed in the exponent. -/
theorem path_dyadic_reverse_of_grid {d : ℕ}
    (K : BrownianCubeAnchor d → BrownianCubeAnchor d → ℝ)
    (β A D : ℝ) (hβ : 0 < β) (hA : 0 < A) (hD : 0 ≤ D)
    (hgrid : KernelGridLower.{u} K β A D) :
    ∃ B : ℝ, 0 < B ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (F : Ω → C(BrownianCubeAnchor d,ℝ)) (hF : Measurable F)
        (hX : IsGaussianProcess (fun x ω => F ω x) P)
        (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
        (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] = K x y)
        (N : ℕ),
        Real.exp (-B * ((2:ℝ)^N * (((N+1:ℕ):ℝ)^(d-1)))) ≤
          P.real {ω | ‖F ω‖ ≤ radiusProfile β d (2*A) N} := by
  classical
  let B : ℝ := D + Real.log 4
  have hB : 0 < B := by
    dsimp [B]
    have : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
    linarith
  refine ⟨B,hB,?_⟩
  intro Ω _ P _ F hF hX hmean hcov N
  let rad : ℝ := radiusProfile β d (2*A) N
  let cost : ℝ := (2:ℝ)^N * (((N+1:ℕ):ℝ)^(d-1))
  have hcost : 1 ≤ cost := by
    dsimp [cost]
    have hp : (1:ℝ) ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hn : (1:ℝ) ≤ (((N+1:ℕ):ℝ)^(d-1)) := by
      apply one_le_pow₀
      exact_mod_cast (show 1 ≤ N+1 by omega)
    nlinarith [mul_le_mul_of_nonneg_left hn (show 0≤(2:ℝ)^N by positivity)]
  have hradpos : 0 < rad := by
    dsimp [rad, radiusProfile]
    positivity
  have hradEq : 2*A*Real.rpow 2 (-β*(N:ℝ)/2)*
      Real.sqrt (((N+1:ℕ):ℝ)^d) = rad := by
    have hsqrt : Real.sqrt (((N+1:ℕ):ℝ)^d) =
        (((N+1:ℕ):ℝ)^((d:ℝ)/2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((N+1:ℕ):ℝ))]
      congr 1
      ring
    rw [hsqrt]
    rfl
  have hgrid' : ∀ M : ℕ,
      ENNReal.ofReal (Real.exp (-D*cost))*((1/2:ENNReal)*(1/2:ENNReal)) ≤
        P {ω | cubeGridMaximum M (F ω) ≤ rad} := by
    intro M
    have hh := hgrid (Ω := Ω) (J := CubeDyadicGrid d M) (P := P)
      (fun ω j => F ω (cubeDyadicAnchor j))
      (cubeDyadicAnchor (d := d) (N := M))
      (gaussian_grid_law _ hX _) (fun j => hmean _) (fun i j => hcov _ _) N
    have hevent :
        {ω | ∀ j : CubeDyadicGrid d M, |F ω (cubeDyadicAnchor j)| ≤
          2*A*Real.rpow 2 (-β*(N:ℝ)/2)*Real.sqrt (((N+1:ℕ):ℝ)^d)} =
        {ω | cubeGridMaximum M (F ω) ≤ rad} := by
      rw [hradEq]
      ext ω
      constructor
      · intro h
        apply (pi_norm_le_iff_of_nonneg hradpos.le).2
        intro j
        simpa only [Real.norm_eq_abs] using h j
      · intro h j
        have hj := (pi_norm_le_iff_of_nonneg hradpos.le).1 h j
        simpa only [Real.norm_eq_abs] using hj
    rw [hevent] at hh
    simpa [cost, mul_assoc] using hh
  have huniform := cube_grid_mass_lower_to_uniform_mass_lower
    P F hF rad hradpos.le _ hgrid'
  have hreal := ENNReal.toReal_mono (measure_ne_top P _) huniform
  have hmass : Real.exp (-D*cost)/4 ≤ P.real {ω | ‖F ω‖ ≤ rad} := by
    have hmass' : (ENNReal.ofReal (Real.exp (-D*cost)) *
        (1/2:ENNReal) * (1/2:ENNReal)).toReal ≤ P.real {ω | ‖F ω‖ ≤ rad} := by
      simpa [Measure.real_def, mul_assoc] using hreal
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hmass'
    norm_num at hmass'
    convert hmass' using 1 <;> ring_nf
  have hexp : Real.exp (-B*cost) ≤ Real.exp (-D*cost)/4 := by
    have hlog4 : 0 ≤ Real.log (4:ℝ) := le_of_lt (Real.log_pos (by norm_num))
    have harg : -Real.log (4:ℝ)*cost ≤ -Real.log (4:ℝ) := by nlinarith
    have heq4 : Real.exp (-Real.log (4:ℝ)) = (1:ℝ)/4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
      norm_num
    have hfactor : Real.exp (-Real.log (4:ℝ)*cost) ≤ (1:ℝ)/4 := by
      calc
        _ ≤ Real.exp (-Real.log (4:ℝ)) := Real.exp_le_exp.mpr harg
        _ = _ := heq4
    have heq : -B*cost = -D*cost + (-Real.log (4:ℝ)*cost) := by
      dsimp [B]
      ring
    rw [heq, Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg _)).trans_eq (by ring)
  exact hexp.trans hmass

/-- Scale inversion produces the upper logarithm with constants uniform over
all centered continuous Gaussian realizations of the fixed covariance. -/
theorem path_upperLog_of_grid {d : ℕ} (hd : 2 ≤ d)
    (K : BrownianCubeAnchor d → BrownianCubeAnchor d → ℝ)
    (β A D : ℝ) (hβ : 0 < β) (hA : 0 < A) (hD : 0 ≤ D)
    (hgrid : KernelGridLower.{u} K β A D) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (F : Ω → C(BrownianCubeAnchor d,ℝ)) (hF : Measurable F)
        (hX : IsGaussianProcess (fun x ω => F ω x) P)
        (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
        (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] = K x y)
        (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) ≤
          C * BrownianSharp.Latest.smallBallRate
            (2/β) (d-1+(d:ℝ)/β) ε := by
  obtain ⟨B,hB,hdyadic⟩ := path_dyadic_reverse_of_grid K β A D hβ hA hD hgrid
  obtain ⟨C,ε₀,hC,hε₀,hε₀small,hprofiles⟩ :=
    uniform_upperLog_of_dyadic_probability_lower d 0 hd (2*A) B β
      (by positivity) hB hβ
  refine ⟨C,ε₀,hC,hε₀,hε₀small,?_⟩
  intro Ω _ P _ F hF hX hmean hcov ε hε hsmall
  let p : ℝ → ℝ := fun η => P.real {ω | ‖F ω‖ ≤ η}
  have hmono : ∀ x y, 0 < x → x ≤ y → p x ≤ p y := by
    intro x y hx hxy
    exact measureReal_mono (fun ω hω => hω.trans hxy) (measure_ne_top P _)
  have hdyad : ∀ N : ℕ, 0 ≤ N →
      Real.exp (-B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1))) ≤
        p (radiusProfile β d (2*A) N) := by
    intro N hN
    exact hdyadic F hF hX hmean hcov N
  have hmain := hprofiles p hmono hdyad ε hε hsmall
  have hcast : ((d:ℝ)-1) = ((d-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  simp only [gradedLogRate] at hmain
  rw [hcast] at hmain
  simpa [p, BrownianSharp.Latest.smallBallRate, div_eq_mul_inv, hcast] using hmain

end BrownianSharp.AlignmentPaperMaternPathUpper
