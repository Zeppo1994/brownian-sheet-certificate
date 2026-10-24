import BrownianSharp.AlignmentGaussianIntegratedHalfMass
import BrownianSharp.AlignmentGaussianIntegratedFiniteGridConfinement
import BrownianSharp.AlignmentGaussianGradedDilationAllGrades
import BrownianSharp.AlignmentFractionalGradedPolynomialFeature
import BrownianSharp.AlignmentFractionalGradedPolynomialWidth
import BrownianSharp.AlignmentFractionalPolynomialSpaces
import BrownianSharp.AlignmentFractionalPolynomialConvergence
import BrownianSharp.AlignmentFractionalDyadicProjection
import BrownianSharp.AlignmentFractionalWeightedHaarCounts
import BrownianSharp.FiniteHaarLowDimension
import BrownianSharp.LayerIndex
import Mathlib.Tactic

/-! Finite-grid lower probabilities for actual integer-integrated Brownian
sheets, using polynomial source frames and a uniform diagonal-dilation cost. -/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianIntegratedGridLower

open BrownianSharp.AlignmentGaussianIntegratedHalfMass
open BrownianSharp.AlignmentGaussianIntegratedFiniteGridConfinement
open BrownianSharp.AlignmentGaussianGradedDilationAllGrades
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentGaussianHilbertFeature
open BrownianSharp.AlignmentGaussianFiniteFeature
open BrownianSharp.AlignmentGaussianIntegratedSourceModel
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentFractionalGradedPolynomialWidth
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentFractionalPolynomialConvergence
open BrownianSharp.AlignmentGaussianFractionalHaar
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentGeometricRanks
open BrownianSharp.GaussianProjection
open BrownianSharp.CameronMartin
open BrownianSharp
open HaarQuarter

/-- A uniform finite-grid lower bound for actual integer-integrated sheets.
The constants are chosen before the finite grid and dyadic level. -/
theorem integerIntegrated_grid_lower_bound
    {ν e : ℕ} (hν : 2 ≤ ν) (m₀ : ℕ) (m : Fin (ν+e) → ℕ)
    (hm : Latest.minimumMultiplicity (fun i => (m i:ℝ)+1)
      ((m₀:ℝ)+1) ν) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (J : Type*) [Fintype J] [Nonempty J]
        (B : BrownianSheetOnCube (ν+e) Ω P)
        (x : J → BrownianCubeAnchor (ν+e)) (N : ℕ),
        ENNReal.ofReal (Real.exp (-D*(2:ℝ)^N*((N+1:ℕ):ℝ)^(ν-1))) *
            ((1/2:ENNReal)*(1/2:ENNReal)) ≤
          P {ω | ∀ j, |BrownianSharp.AlignmentGaussianRates.integrateSheetPath
            m (B.path ω) (x j)| ≤
              2*A*Real.rpow 2 (-(2*(m₀:ℝ)+1)*(N:ℝ)/2)*
                Real.sqrt (((N+1:ℕ):ℝ)^ν)} := by
  classical
  let d : ℕ := ν+e
  let α : Fin d → ℝ := fun i => (m i:ℝ)+1
  let r : ℝ := (m₀:ℝ)+1
  let β : ℝ := 2*r-1
  let q : ℝ := Real.rpow 2 (-β)
  have hd : 0 < d := by dsimp [d]; omega
  have hr : 1/2 < r := by
    dsimp [r]
    have hm0 : 0 ≤ (m₀:ℝ) := Nat.cast_nonneg _
    linarith
  have hβ : 0 < β := by
    dsimp [β,r]
    have hm0 : 0 ≤ (m₀:ℝ) := Nat.cast_nonneg _
    linarith
  have hq0 : 0 < q := by dsimp [q]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by
    dsimp [q]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    dsimp [β,r]
    have hm0 : 0 ≤ (m₀:ℝ) := Nat.cast_nonneg _
    linarith
  have hα : ∀ i, 1/2 < α i := by
    intro i
    dsimp [α]
    have hm0 : 0 ≤ (m i:ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨degree,Cvar,A,hdegree,hCvar,hA,hhalf⟩ :=
    integerIntegrated_polynomial_frame_half_mass (by omega : 0 < ν) m₀ m hm
  obtain ⟨Acount,hAcount,hcount⟩ :=
    polynomial_tensor_weightedLowFiber_layer_multiple hν (by linarith : 0 < r)
      α degree hdegree hm
  let eta : ℝ := Real.sqrt (q/2)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := by
    dsimp [eta]
    apply Real.sqrt_le_one.mpr
    linarith
  let Cdim : ℝ := Acount
  let D : ℝ := (-Real.log eta) *
      (Cdim * polynomialBudget (1/2) 1)
  have hCdim : 0 < Cdim := by
    dsimp [Cdim]
    exact_mod_cast hAcount
  have hD : 0 ≤ D := by
    dsimp [D]
    have hlog : 0 ≤ -Real.log eta := by
      apply neg_nonneg.mpr
      exact Real.log_nonpos heta.le heta1
    have hbudget : 0 ≤ polynomialBudget (1/2) 1 :=
      polynomialBudget_nonneg (by norm_num) 1
    positivity
  refine ⟨A,D,hA,hD,?_⟩
  intro Ω _ P _ J _ _ B x
  intro N
  let rate : ℝ := Real.rpow 2 (-β*(N:ℝ)/2)
  let poly : ℝ := (((N+1:ℕ):ℝ)^ν)
  let ρ : ℝ := A*rate*Real.sqrt poly
  let loggrid : ℝ := Real.log (2*(Fintype.card J:ℝ)+2)
  let τ : ℝ := ρ/(4*Real.sqrt loggrid)
  have hcardJ : 1 ≤ (Fintype.card J:ℝ) := by
    have hnat : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ‹Nonempty J›
    have hnat' : 1 ≤ Fintype.card J := by omega
    exact_mod_cast hnat'
  have hlogarg : 1 < 2*(Fintype.card J:ℝ)+2 := by nlinarith
  have hloggrid : 0 < loggrid := by
    dsimp [loggrid]
    exact Real.log_pos hlogarg
  have hsqrtlog : 0 < Real.sqrt loggrid := Real.sqrt_pos.2 hloggrid
  have hrate : 0 < rate := by dsimp [rate]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hpoly : 0 < poly := by dsimp [poly]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hbudgetτ : 2*τ*Real.sqrt loggrid ≤ ρ/2 := by
    dsimp [τ]
    have hs : Real.sqrt loggrid ≠ 0 := ne_of_gt hsqrtlog
    field_simp
    norm_num
  obtain ⟨M,hM,hresidual⟩ := exists_gradedPolynomialTensorProjectedKernel_depth
    hd degree hdegree α hα hτ
  let I : Type := ∀ i : Fin d,
      GradedFrameIndex (fun n => piecewisePolynomials (degree i) n) M
  let e : I → UnitCubeL2 d := polynomialTensorGradedFrame degree M
  let gradeI : I → ℕ := fun a => weightedProfileGrade α r
      (profileNat (fun i => (a i).1))
  let scaleI : I → ℝ := fun a => contractionScale eta N (gradeI a)
  let K : C(BrownianCubeAnchor d, UnitCubeL2 d) := tensorKernelFamily α hα
  have hmass : (1/2:ENNReal) ≤ productStandardGaussian I
      {z | ‖finiteGaussianFeaturePath (diagonalFeature K e scaleI) z‖ ≤ ρ} := by
    have h := hhalf M N
    convert h using 1 <;> rfl
  have hscaled : (1/2:ENNReal) ≤ productStandardGaussian I
      {z | ∀ j, |∑ i, ⟪integerIntegratedKernelFeature m (x j),e i⟫*
        (scaleI i*z i)| ≤ ρ} := by
    apply hmass.trans
    apply measure_mono
    intro z hz
    intro j
    let F := finiteGaussianFeaturePath (diagonalFeature K e scaleI) z
    have heval : F (x j) = ∑ i,
        ⟪integerIntegratedKernelFeature m (x j),e i⟫*(scaleI i*z i) := by
      dsimp [F]
      rw [finiteGaussianFeaturePath_apply]
      apply Finset.sum_congr rfl
      intro i hi
      simp [diagonalFeature,integerIntegratedKernelFeature,K]
      ring
    have hnorm : ‖F (x j)‖ ≤ ρ := (F.norm_coe_le_norm (x j)).trans hz
    rw [← heval]
    simpa only [Real.norm_eq_abs] using hnorm
  have hres : ∀ j, ‖integerIntegratedKernelFeature m (x j) -
      projection e (integerIntegratedKernelFeature m (x j))‖ ≤ τ := by
    intro j
    have hproj := polynomialGradedFrame_projection_eq_projectedKernel
      degree M α hα (x j)
    have hprojEq : projection e (tensorKernelFamily α hα (x j)) =
        finiteOrthonormalProjection e (tensorKernelFamily α hα (x j)) := by
      unfold projection finiteOrthonormalProjection
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      exact real_inner_comm _ _
    have hprojection : projection e (integerIntegratedKernelFeature m (x j)) =
        gradedPolynomialTensorProjectedKernel degree M α hα (x j) := by
      have hfeature : integerIntegratedKernelFeature m (x j) = tensorKernelFamily α hα (x j) := rfl
      rw [hfeature,hprojEq]
      change finiteOrthonormalProjection (polynomialTensorGradedFrame degree M)
        (tensorKernelFamily α hα (x j)) = _
      exact hproj
    rw [hprojection]
    simpa [integerIntegratedKernelFeature] using hresidual (x j)
  have horth : Orthonormal ℝ e := by
    change Orthonormal ℝ (polynomialTensorGradedFrame degree M)
    exact polynomialTensorGradedFrame_orthonormal degree M
  have hfiber : ∀ g : Fin (N+1),
      (Fintype.card {i : I // gradeI i = g.val}:ℝ) ≤
        Cdim*(2:ℝ)^g.val*(((g.val+1:ℕ):ℝ)^(ν-1)) := by
    intro g
    let low := {i : I // gradeI i ≤ g.val}
    have hnat : Fintype.card {i : I // gradeI i = g.val} ≤ Fintype.card low :=
      Fintype.card_le_of_injective (fun a => (⟨a.1,Nat.le_of_eq a.2⟩ : low))
      (by intro a b h; apply Subtype.ext; simpa using congrArg Subtype.val h)
    have hl := hcount M g.val
    have hl' : Fintype.card low ≤ Acount*Fintype.card (LayerIndex ν g.val) := by
      simpa [low,I,gradeI] using hl
    have hshape : hyperbolicCount ν g.val ≤
        ((g.val:ℝ)+1)^(ν-1) := hyperbolicCount_upper_shift (by omega : 1≤ν) g.val
    have hcardL : (Fintype.card (LayerIndex ν g.val):ℝ) =
        (2:ℝ)^g.val*(hyperbolicCount ν g.val:ℝ) := by
      rw [layerIndex_card ν g.val (by omega : 0<ν)]
      simp [hyperbolicCount]
    have hlReal : (Fintype.card low:ℝ) ≤
        Cdim*(2:ℝ)^g.val*(((g.val+1:ℕ):ℝ)^(ν-1)) := by
      have hc : (Fintype.card low:ℝ) ≤
          (Acount:ℝ)*(Fintype.card (LayerIndex ν g.val):ℝ) := by exact_mod_cast hl'
      rw [hcardL] at hc
      dsimp [Cdim]
      calc
        (Fintype.card low:ℝ) ≤ (Acount:ℝ) *
            ((2:ℝ)^g.val * (hyperbolicCount ν g.val:ℝ)) := by simpa [hcardL] using hc
        _ = Cdim*(2:ℝ)^g.val*(hyperbolicCount ν g.val:ℝ) := by simp [Cdim]; ring
        _ ≤ Cdim*(2:ℝ)^g.val*(((g.val+1:ℕ):ℝ)^(ν-1)) := by
              gcongr
              exact_mod_cast hshape
    have hnReal : (Fintype.card {i : I // gradeI i = g.val}:ℝ) ≤
        (Fintype.card low:ℝ) := by exact_mod_cast hnat
    exact hnReal.trans hlReal
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heta1 : eta ≤ 1 := by dsimp [eta]; apply Real.sqrt_le_one.mpr; linarith
  have hdet := finite_graded_diagonal_dilation_product_ge_exp_all_grades
    gradeI Cdim eta (ν-1) N (le_of_lt hCdim) heta heta1 hfiber
  have hnonemptyI : Nonempty I := by
    classical
    have haxis (i : Fin d) :
        0 < Module.finrank ℝ (piecewisePolynomials (degree i) 0) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      let v := sourceDyadicCellIndicator 0 ⟨0, by norm_num⟩
      have hmem : v ∈ piecewisePolynomials (degree i) 0 := by
        change sourceDyadicCellIndicator 0 ⟨0, by norm_num⟩ ∈
          piecewisePolynomials (degree i) 0
        rw [← cellMonomial_zero_eq_indicator]
        exact Submodule.subset_span ⟨(⟨0, by norm_num⟩, ⟨0, hdegree i⟩), rfl⟩
      have hnz : v ≠ 0 := by
        intro hz
        have hs := congrArg (fun z : AlignmentFractionalL2.UnitL2 => ⟪z,z⟫) hz
        rw [sourceDyadicCellIndicator_inner_self (n:=0) (j:=⟨0, by norm_num⟩)] at hs
        norm_num at hs
      refine ⟨⟨v,hmem⟩, ?_⟩
      intro hz
      exact hnz (congrArg Subtype.val hz)
    refine ⟨fun i => ⟨⟨0, by omega⟩, ⟨0, haxis i⟩⟩⟩
  have hconf := integratedGrid_confinement_of_main_half_mass B m e
    (fun i j => (orthonormal_iff_ite.mp horth i j)) x scaleI ρ τ hρ hτ.le
    (fun i => contractionScale_pos heta N (gradeI i))
    (fun i => contractionScale_le_one (le_of_lt heta) heta1 N (gradeI i))
    hscaled hres hbudgetτ
  let D' : ℝ := (-Real.log eta) * (Cdim*polynomialBudget (1/2) 1)
  have hD' : D = D' := by rfl
  have hdetENN : ENNReal.ofReal
      (Real.exp (-D'*(2:ℝ)^N*((N+1:ℕ):ℝ)^(ν-1))) ≤
      ENNReal.ofReal (∏ i : I, scaleI i) := by
    apply ENNReal.ofReal_le_ofReal
    have hexp : -D'*(2:ℝ)^N*((N+1:ℕ):ℝ)^(ν-1) =
        -(-Real.log eta)*(Cdim*(2:ℝ)^N*
          (((N+1:ℕ):ℝ)^(ν-1))*polynomialBudget (1/2) 1) := by
      dsimp [D']
      ring
    rw [hexp]
    exact hdet
  rw [hD']
  have hradius : 2*ρ =
      2*A*Real.rpow 2 (-(2*(m₀:ℝ)+1)*(N:ℝ)/2)*
        Real.sqrt (((N+1:ℕ):ℝ)^ν) := by
    have hexp : -β*(N:ℝ)/2 = -(2*(m₀:ℝ)+1)*(N:ℝ)/2 := by
      dsimp [β,r]
      ring
    dsimp [ρ,rate,poly]
    rw [hexp]
    ring
  have hconf' : ENNReal.ofReal (∏ i : I, scaleI i) *
      ((1/2:ENNReal)*(1/2:ENNReal)) ≤
      P {ω | ∀ j, |BrownianSharp.AlignmentGaussianRates.integrateSheetPath
        m (B.path ω) (x j)| ≤
          2*A*Real.rpow 2 (-(2*(m₀:ℝ)+1)*(N:ℝ)/2)*
            Real.sqrt (((N+1:ℕ):ℝ)^ν)} := by
    simpa only [hradius] using hconf
  calc
    ENNReal.ofReal (Real.exp (-D'*(2:ℝ)^N*((N+1:ℕ):ℝ)^(ν-1))) *
        ((1/2:ENNReal)*(1/2:ENNReal)) ≤
      ENNReal.ofReal (∏ i : I, scaleI i) * ((1/2:ENNReal)*(1/2:ENNReal)) := by
        exact mul_le_mul_of_nonneg_right hdetENN (by positivity)
    _ ≤ P {ω | ∀ j, |BrownianSharp.AlignmentGaussianRates.integrateSheetPath
        m (B.path ω) (x j)| ≤
          2*A*Real.rpow 2 (-(2*(m₀:ℝ)+1)*(N:ℝ)/2)*
            Real.sqrt (((N+1:ℕ):ℝ)^ν)} := hconf'

end BrownianSharp.AlignmentGaussianIntegratedGridLower
