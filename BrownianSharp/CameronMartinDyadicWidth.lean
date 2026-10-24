import BrownianSharp.FiniteDictionaryLayerAssembly
import BrownianSharp.HaarGradeRowBound
import BrownianSharp.FiniteHaarLowDimension
import BrownianSharp.CubeWidthLifting
import BrownianSharp.CubeSamplingRate
import BrownianSharp.DKLLRankAllocation

/-! Assemble finite dictionary approximations of the actual tensor Haar
rows into continuous-path Cameron–Martin widths at the sharp dyadic scale. -/
noncomputable section
open scoped BigOperators ENNReal
namespace BrownianSharp
open HaarQuarter CameronMartin DKLLRankAllocation

/-- The exact square-summed high-grade dictionary error on the depth-`2n`
endpoint grid, with half-base geometric rank allocation. -/
def dyadicHaarDictionaryErrorSum (C : ℝ) (d n : ℕ) : ℝ :=
  ∑ j : HaarHighGradeIndex d (2*n) n,
    (C*haarGradeRowRadius d (n+j.val)*Real.sqrt
      (Real.log (2*(Fintype.card (CubeDyadicGrid d (2*n)):ℝ)+2)/
        ((allocatedRank (Fintype.card (LayerIndex d n)/2) j.val:ℝ)+1)))^2

/-- This bridge has only two numerical inputs: the universal finite
approximation theorem and its evaluated, square-summed error. All function
spaces, Haar vectors, grids and approximation dimensions here are actual. -/
theorem KdUnitCube_dyadic_width_of_finite_dictionary
    {d : ℕ} (hd : 2≤d) {C A : ℝ} (hfin : FinDictionaryApproximation C)
    (hC : 0≤C) (hA : 0<A)
    (herror : ∀ n : ℕ,2≤n → dyadicHaarDictionaryErrorSum C d n≤
      A*((n:ℝ)+1)*(((2:ℝ)^n)⁻¹)^2) :
    ∃ B : ℝ,0<B ∧ ∀ n : ℕ,2≤n →
      TheoremD.Width.kolmogorovWidth (KdUnitCube d)
        (4*Fintype.card (LayerIndex d n))≤
      ENNReal.ofReal (B*Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n) := by
  let B : ℝ := Real.sqrt (2*(d:ℝ))+Real.sqrt A
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro n hn
  let N := 2*n
  let D := Fintype.card (LayerIndex d n)
  let J := HaarHighGradeIndex d N n
  let m : J → ℕ := fun j => allocatedRank (D/2) j.val
  let R : J → ℝ := fun j => haarGradeRowRadius d (n+j.val)
  obtain ⟨W,hW,happrox⟩ := finiteRow_dictionary_layer_assembly hfin hC
    (haarLowHighGrade (d:=d) (N:=N) n) (haarGridRows d N) m R
    (fun j => haarGradeRowRadius_nonneg _ _)
    (fun j g => haarHighGradeRow_norm_le (by omega) j g)
  have hlow : Fintype.card {a : FiniteHaarIndex d N // haarLowHighGrade n a=none}≤D := by
    let e : {a : FiniteHaarIndex d (2*n) // haarLowHighGrade n a=none} ≃
        {a : FiniteHaarIndex d (2*n) // finiteHaarGrade a<n} := {
      toFun := fun a => (⟨a.1, (haarLowHighGrade_eq_none (n₀:=n) a.1).mp a.2⟩ :
        {a : FiniteHaarIndex d (2*n) // finiteHaarGrade a < n})
      invFun := fun a => (⟨a.1, (haarLowHighGrade_eq_none (n₀:=n) a.1).mpr a.2⟩ :
        {a : FiniteHaarIndex d (2*n) // haarLowHighGrade n a = none})
      left_inv := by intro a; apply Subtype.ext; rfl
      right_inv := by intro a; apply Subtype.ext; rfl }
    rw [Fintype.card_congr e]
    dsimp [D]
    rw [layerIndex_card d n (by omega)]
    exact finiteHaarLowIndex_card_le (by omega)
  have hbudget : Fintype.card {a : FiniteHaarIndex d N // haarLowHighGrade n a=none}+
      ∑ j : J,m j≤4*D := by
    have hsum : (∑ j : J,m j)=
        ∑ j ∈ Finset.range (d*N+1-n),allocatedRank (D/2) j := by
      exact Fin.sum_univ_eq_sum_range (fun j => allocatedRank (D/2) j) _
    rw [hsum]
    exact low_plus_half_allocatedRank_le _ _ _ hlow
  have hWrank : Module.rank ℝ W≤((4*D:ℕ):Cardinal) := hW.trans (by exact_mod_cast hbudget)
  have hgrid : ∀ g : AmbientL2 d,‖g‖≤1 → ∃ w∈W,
      ‖cubeGridEvaluationLinear d N g-w‖≤Real.sqrt (dyadicHaarDictionaryErrorSum C d n) := by
    have h := haarGrid_unitBall_approximation_transfer d N W happrox
    exact h
  have hwidth := KdUnitCube_width_le_of_grid_approximation d N (4*D) W hWrank hgrid
  have hsqrt : Real.sqrt (dyadicHaarDictionaryErrorSum C d n)≤
      Real.sqrt A*Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hsq : (Real.sqrt A*Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n)^2=
        A*((n:ℝ)+1)*(((2:ℝ)^n)⁻¹)^2 := by
      rw [div_pow,mul_pow,Real.sq_sqrt hA.le,Real.sq_sqrt (by positivity)]
      ring
    rw [hsq]
    exact herror n hn
  apply hwidth.trans
  apply ENNReal.ofReal_le_ofReal
  have hsampling := cubeSampling_doubleDepth_error_le d n
  dsimp [N,B] at *
  calc
    Real.sqrt ((d:ℝ)*(2*((2:ℝ)^(2*n))⁻¹)) +
        Real.sqrt (dyadicHaarDictionaryErrorSum C d n) ≤
      Real.sqrt (2*(d:ℝ))*Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n +
        Real.sqrt A*Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n := add_le_add hsampling hsqrt
    _ = (Real.sqrt (2*(d:ℝ))+Real.sqrt A)*
        Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n := by ring

end BrownianSharp
