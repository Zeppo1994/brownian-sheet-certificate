import BrownianSharp.FiniteHaarGeometry
import BrownianSharp.CubeDyadicGrid
import BrownianSharp.FiniteOrthogonalCoordinates
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The finite tensor Haar family spans every feature on the same endpoint
grid. Dimension counting avoids introducing an infinite Haar basis. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter CameronMartin

abbrev CubePositiveGrid (d N : ℕ) := Fin d → Fin (2^N)

def positiveGridToGrid {d N : ℕ} (j : CubePositiveGrid d N) : CubeDyadicGrid d N :=
  fun i => ⟨(j i).val+1,by have := (j i).isLt; omega⟩

def finiteGridFeatureSpan (d N : ℕ) : Submodule ℝ (brownianCubeBoxSpan d) :=
  Submodule.span ℝ (Set.range (fun j : CubePositiveGrid d N =>
    featureVector (cubeDyadicAnchor (positiveGridToGrid j))))

instance finiteGridFeatureSpan_finite (d N : ℕ) :
    FiniteDimensional ℝ (finiteGridFeatureSpan d N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem finiteGridFeatureSpan_finrank_le (d N : ℕ) :
    Module.finrank ℝ (finiteGridFeatureSpan d N) ≤ (2^N)^d := by
  have h := finrank_range_le_card (R:=ℝ) (fun j : CubePositiveGrid d N =>
      featureVector (cubeDyadicAnchor (positiveGridToGrid j)))
  change Module.finrank ℝ (finiteGridFeatureSpan d N) ≤ Fintype.card (CubePositiveGrid d N) at h
  simpa [CubePositiveGrid] using h

theorem featureVector_eq_zero_of_coordinate {d : ℕ} (x : BrownianCubeAnchor d)
    (i : Fin d) (hi : x.val i=0) : featureVector x=0 := by
  have hself : ‖featureVector x‖^2=0 := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪brownianSheetBoxIndicatorLp x.val,brownianSheetBoxIndicatorLp x.val⟫=0
    rw [brownianSheetBoxIndicatorLp_inner _ _
      (fun j => (x.property j).1) (fun j => (x.property j).1)]
    simp only [min_self]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (featureVector x)])

theorem grid_feature_mem_finiteGridFeatureSpan {d N : ℕ} (j : CubeDyadicGrid d N) :
    featureVector (cubeDyadicAnchor j) ∈ finiteGridFeatureSpan d N := by
  classical
  by_cases hz : ∃ i,(j i).val=0
  · obtain ⟨i,hi⟩ := hz
    rw [featureVector_eq_zero_of_coordinate (cubeDyadicAnchor j) i (by simp [cubeDyadicAnchor,hi])]
    exact Submodule.zero_mem _
  · have hpos : ∀ i,0<(j i).val := by intro i; have := not_exists.mp hz i; omega
    let k : CubePositiveGrid d N := fun i => ⟨(j i).val-1,by
      have := (j i).isLt
      have := hpos i
      omega⟩
    have hk : positiveGridToGrid k=j := by
      funext i
      apply Fin.ext
      dsimp [positiveGridToGrid,k]
      have := hpos i
      omega
    rw [← hk]
    exact Submodule.subset_span (Set.mem_range_self k)

private theorem dyadic_fraction_on_grid {N r j : ℕ} (hr : r≤N) (hj : j≤2^r) :
    ∃ k : Fin (2^N+1), (j:ℝ)/(2:ℝ)^r=(k:ℝ)/(2:ℝ)^N := by
  have hpow : 2^r*2^(N-r)=2^N := by rw [← pow_add,Nat.add_sub_of_le hr]
  refine ⟨⟨j*2^(N-r),by nlinarith [Nat.mul_le_mul_right (2^(N-r)) hj]⟩,?_⟩
  have hpowreal : (2:ℝ)^r*(2:ℝ)^(N-r)=(2:ℝ)^N := by exact_mod_cast hpow
  change (j:ℝ)/(2:ℝ)^r=(j*2^(N-r):ℕ)/(2:ℝ)^N
  push_cast
  rw [← hpowreal]
  field_simp

private theorem finiteHaarEndpoint_on_grid {N : ℕ} (a : FiniteHaarAxis N) (k : Fin 3) :
    ∃ j : Fin (2^N+1), finiteHaarEndpoint a k=(j:ℝ)/(2:ℝ)^N := by
  cases a with
  | none =>
    refine ⟨⟨2^N,by omega⟩,?_⟩
    simp [finiteHaarEndpoint]
  | some a =>
    obtain ⟨r,j⟩ := a
    have hr : r.val+1≤N := by omega
    fin_cases k
    · simpa [finiteHaarEndpoint,haarCorner,dyadicHaarLeft] using
        dyadic_fraction_on_grid (Nat.le_of_succ_le hr) (Nat.le_of_lt j.isLt)
    · have hj : 2*j.val+1≤2^(r.val+1) := by rw [pow_succ]; have := j.isLt; omega
      obtain ⟨k,hk⟩ := dyadic_fraction_on_grid hr hj
      refine ⟨k,?_⟩
      change dyadicHaarMid r.val j.val = _
      rw [← hk]
      simp only [dyadicHaarMid,dyadicHaarLeft,dyadicHaarRight,pow_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
      ring
    · simpa [finiteHaarEndpoint,haarCorner,dyadicHaarRight] using
        dyadic_fraction_on_grid (Nat.le_of_succ_le hr) (Nat.succ_le_of_lt j.isLt)

/-- Each mixed Haar corner is an endpoint-grid feature; a zero-coordinate
corner is automatically the zero vector. -/
theorem finiteHaarVector_mem_finiteGridFeatureSpan {d N : ℕ} (a : FiniteHaarIndex d N) :
    finiteHaarVector a ∈ finiteGridFeatureSpan d N := by
  classical
  have hcorner (k : Fin d → Fin 3) : ∃ j : CubeDyadicGrid d N,
      (cubeDyadicAnchor j).val=fun i => finiteHaarEndpoint (a i) (k i) := by
    have hh : ∀ i,∃ j : Fin (2^N+1),finiteHaarEndpoint (a i) (k i)=(j:ℝ)/(2:ℝ)^N :=
      fun i => finiteHaarEndpoint_on_grid (a i) (k i)
    choose j hj using hh
    exact ⟨j,by funext i; exact (hj i).symm⟩
  have heq : finiteHaarVector a = (∏ i,finiteHaarAxisScale (a i)) •
      ∑ k : Fin d → Fin 3,
        (∏ i,finiteHaarCornerWeight (a i) (k i)) •
          featureVector (cubeDyadicAnchor (Classical.choose (hcorner k))) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul,Submodule.coe_sum,featureVector,
      finiteHaarVector,finiteHaarVectorAmbient]
    congr 2
    funext k
    rw [Classical.choose_spec (hcorner k)]
  rw [heq]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (grid_feature_mem_finiteGridFeatureSpan _)

/-- Dimension counting identifies the two finite spans. Only the elementary
index cardinality is separated so this geometric lemma can be reused. -/
theorem finiteGridFeatureSpan_eq_haarSpan {d N : ℕ}
    (hcard : Fintype.card (FiniteHaarIndex d N)=(2^N)^d) :
    finiteGridFeatureSpan d N = Submodule.span ℝ (Set.range (finiteHaarVector (d:=d) (N:=N))) := by
  have horth : Orthonormal ℝ (finiteHaarVector (d:=d) (N:=N)) :=
    orthonormal_iff_ite.mpr finiteHaarVector_orthonormal
  have hle : Submodule.span ℝ (Set.range (finiteHaarVector (d:=d) (N:=N))) ≤
      finiteGridFeatureSpan d N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact finiteHaarVector_mem_finiteGridFeatureSpan a
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_span_eq_card horth.linearIndependent,hcard]
  exact finiteGridFeatureSpan_finrank_le d N

/-- Exact expansion of every grid feature in the actual finite tensor Haar
family. No residual or infinite-series assertion is hidden in this identity. -/
theorem grid_feature_eq_finite_haar_sum {d N : ℕ}
    (hcard : Fintype.card (FiniteHaarIndex d N)=(2^N)^d) (j : CubeDyadicGrid d N) :
    featureVector (cubeDyadicAnchor j) =
      ∑ a : FiniteHaarIndex d N,
        ⟪featureVector (cubeDyadicAnchor j),finiteHaarVector a⟫ • finiteHaarVector a := by
  have hm := grid_feature_mem_finiteGridFeatureSpan j
  rw [finiteGridFeatureSpan_eq_haarSpan hcard] at hm
  exact (finiteProjectionLinear_eq_of_mem_span _
    (orthonormal_iff_ite.mpr finiteHaarVector_orthonormal) hm).symm

/-- Evaluation of the original ambient L² integration path, expressed through
its finite Haar coordinates on the endpoint grid. -/
theorem anchoredIntegrationPath_grid_eq_haar_sum {d N : ℕ}
    (hcard : Fintype.card (FiniteHaarIndex d N)=(2^N)^d)
    (g : AmbientL2 d) (j : CubeDyadicGrid d N) :
    anchoredIntegrationPath g (cubeDyadicAnchor j) =
      ∑ a : FiniteHaarIndex d N,
        ⟪g,(finiteHaarVector a : AmbientL2 d)⟫ *
          ⟪finiteHaarVector a,featureVector (cubeDyadicAnchor j)⟫ := by
  have heq := congrArg (fun v : brownianCubeBoxSpan d => (v : AmbientL2 d))
    (grid_feature_eq_finite_haar_sum hcard j)
  change ⟪g,(featureVector (cubeDyadicAnchor j) : AmbientL2 d)⟫ = _
  rw [heq]
  simp only [Submodule.coe_sum,Submodule.coe_smul,inner_sum,inner_smul_right]
  apply Finset.sum_congr rfl
  intro a ha
  rw [real_inner_comm (featureVector (cubeDyadicAnchor j)) (finiteHaarVector a)]
  ring

end BrownianSharp
