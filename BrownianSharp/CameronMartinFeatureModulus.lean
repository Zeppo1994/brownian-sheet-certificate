import BrownianSharp.CameronMartin

/-! Quantitative feature continuity for the actual anchored integration ball. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.CameronMartin
open HaarQuarter

private theorem abs_prod_sub_prod_le_sum_abs {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |(∏ i, a i)-(∏ i, b i)| ≤ ∑ i, |a i-b i| := by
  classical
  have hgen (S : Finset ι) : |(∏ i ∈ S, a i)-(∏ i ∈ S, b i)| ≤
      ∑ i ∈ S, |a i-b i| := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]
      have hB0 : 0 ≤ ∏ j ∈ S, b j := Finset.prod_nonneg (fun j hj => (hb j).1)
      have hB1 : (∏ j ∈ S, b j) ≤ 1 :=
        Finset.prod_le_one₀ (fun j hj => (hb j).1) (fun j hj => (hb j).2)
      have heq : a i*(∏ j ∈ S,a j)-b i*(∏ j ∈ S,b j) =
          a i*((∏ j ∈ S,a j)-(∏ j ∈ S,b j))+(a i-b i)*(∏ j ∈ S,b j) := by ring
      rw [heq]
      calc
        _ ≤ |a i*((∏ j ∈ S,a j)-(∏ j ∈ S,b j))| + 
            |(a i-b i)*(∏ j ∈ S,b j)| := abs_add_le _ _
        _ = a i* |(∏ j ∈ S,a j)-(∏ j ∈ S,b j)| + |a i-b i| * (∏ j ∈ S,b j) := by
          rw [abs_mul,abs_mul,abs_of_nonneg (ha i).1,abs_of_nonneg hB0]
        _ ≤ (∑ j ∈ S,|a j-b j|)+ |a i-b i| := by
          have hfirst : a i* |(∏ j ∈ S,a j)-(∏ j ∈ S,b j)| ≤
              ∑ j ∈ S,|a j-b j| := by
            have hmul := mul_le_mul_of_nonneg_right (ha i).2
              (abs_nonneg ((∏ j ∈ S,a j)-(∏ j ∈ S,b j)))
            nlinarith
          have hsecond : |a i-b i| * (∏ j ∈ S,b j) ≤ |a i-b i| := by
            nlinarith [abs_nonneg (a i-b i)]
          exact add_le_add hfirst hsecond
        _ = _ := by ring
  exact hgen Finset.univ

/-- The covariance metric is bounded by the coordinate l1 metric. -/
theorem featureVector_sub_norm_sq_le {d : ℕ} (x y : BrownianCubeAnchor d) :
    ‖(featureVector x : AmbientL2 d)-(featureVector y : AmbientL2 d)‖^2 ≤
      ∑ i : Fin d, |x.val i-y.val i| := by
  have hnorm : ‖(featureVector x : AmbientL2 d)-(featureVector y : AmbientL2 d)‖^2 =
      (∏ i,x.val i)+(∏ i,y.val i)-2*(∏ i,min (x.val i) (y.val i)) := by
    change ‖brownianSheetBoxIndicatorLp x.val-brownianSheetBoxIndicatorLp y.val‖^2 = _
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right]
    rw [brownianSheetBoxIndicatorLp_inner x.val x.val
      (fun i => (x.property i).1) (fun i => (x.property i).1),
      brownianSheetBoxIndicatorLp_inner x.val y.val
      (fun i => (x.property i).1) (fun i => (y.property i).1),
      brownianSheetBoxIndicatorLp_inner y.val x.val
      (fun i => (y.property i).1) (fun i => (x.property i).1),
      brownianSheetBoxIndicatorLp_inner y.val y.val
      (fun i => (y.property i).1) (fun i => (y.property i).1)]
    simp only [min_self,min_comm]
    ring
  let z : Fin d → ℝ := fun i => min (x.val i) (y.val i)
  have hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := fun i =>
    ⟨le_min (x.property i).1 (y.property i).1,(min_le_left _ _).trans (x.property i).2⟩
  have hx := abs_prod_sub_prod_le_sum_abs x.val z x.property hz
  have hy := abs_prod_sub_prod_le_sum_abs y.val z y.property hz
  have hsum : (∑ i : Fin d, |x.val i-z i|)+(∑ i : Fin d, |y.val i-z i|) =
      ∑ i : Fin d, |x.val i-y.val i| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [z]
    by_cases hxy : x.val i ≤ y.val i
    · rw [min_eq_left hxy]
      simp [abs_of_nonneg (sub_nonneg.mpr hxy),abs_of_nonpos (sub_nonpos.mpr hxy)]
    · have hyx : y.val i ≤ x.val i := le_of_not_ge hxy
      rw [min_eq_right hyx]
      simp [abs_of_nonneg (sub_nonneg.mpr hyx)]
  rw [hnorm]
  have hxabs := le_abs_self ((∏ i,x.val i)-(∏ i,z i))
  have hyabs := le_abs_self ((∏ i,y.val i)-(∏ i,z i))
  change (∏ i,x.val i)+(∏ i,y.val i)-2*(∏ i,z i) ≤ _
  nlinarith

/-- Uniform square-root modulus, including cube boundary points. -/
theorem featureVector_sub_norm_le {d : ℕ} (x y : BrownianCubeAnchor d)
    {δ : ℝ} (hδ : 0 ≤ δ) (hxy : ∀ i, |x.val i-y.val i| ≤ δ) :
    ‖(featureVector x : AmbientL2 d)-(featureVector y : AmbientL2 d)‖ ≤
      Real.sqrt ((d:ℝ)*δ) := by
  have hsum : (∑ i : Fin d,|x.val i-y.val i|) ≤ (d:ℝ)*δ := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i hi => hxy i)
  have hsq := (featureVector_sub_norm_sq_le x y).trans hsum
  have hsqrt := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg d) hδ)
  nlinarith [norm_nonneg ((featureVector x : AmbientL2 d)-(featureVector y : AmbientL2 d)),
    Real.sqrt_nonneg ((d:ℝ)*δ)]

theorem anchoredIntegrationPath_modulus {d : ℕ} (g : AmbientL2 d) (hg : ‖g‖ ≤ 1)
    (x y : BrownianCubeAnchor d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hxy : ∀ i, |x.val i-y.val i| ≤ δ) :
    |anchoredIntegrationPath g x-anchoredIntegrationPath g y| ≤ Real.sqrt ((d:ℝ)*δ) := by
  change |⟪g,(featureVector x : AmbientL2 d)⟫-⟪g,(featureVector y : AmbientL2 d)⟫| ≤ _
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans
    (by simpa using featureVector_sub_norm_le x y hδ hxy))

end BrownianSharp.CameronMartin
