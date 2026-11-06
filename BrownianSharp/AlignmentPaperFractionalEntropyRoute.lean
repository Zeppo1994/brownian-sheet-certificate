import BrownianSharp.AlignmentExponentialFractionalEntropy

/-! Direct route from scalar fractional atom preimages to the actual native
Gaussian mass estimate and entropy lower bound. The scalar provider is an
explicit input, supplied by the Fourier route (5.5). -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPaperFractionalEntropyRoute
open AlignmentFractionalL2 AlignmentFractionalTranslation AlignmentFractionalDensity
  AlignmentFractionalTensorOperator AlignmentFractionalTensorAtoms AlignmentL2TensorProduct
  AlignmentFractionalNativeLayer AlignmentFractionalCompactness

/-- Exact scalar source conclusion needed by the tensor atom construction. -/
def ScalarPreimages : Prop :=
  ∀ (α : ℝ) (hα : 1/2 < α), ∃ Cα : ℝ, 0 < Cα ∧
    ∀ (s m : ℕ), m < 2^s → ∃ g : UnitL2,
      fractionalRL α hα g = restrictProfile
        (fun t => smoothAtom (((2^s:ℝ) * t) - m))
        ((smoothAtom_contDiff.comp
          ((contDiff_const.mul contDiff_id).sub contDiff_const)).continuous) ∧
      ‖g‖^2 ≤ Cα * (2:ℝ)^((2*α-1)*(s:ℝ))

theorem tensor_preimages_of_scalar {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) (hscalar : ScalarPreimages) :
    ∃ C : ℝ, 0<C ∧ ∀ (s : Fin d → ℕ) (m : ∀ i, Fin (2^(s i))),
      ∃ g : CameronMartin.UnitCubeL2 d,
        fractionalTensorRL a ha g = cubeTensorAtom s m ∧
        ‖g‖^2 ≤ C*(2:ℝ)^(∑ i, (2*a i-1)*(s i:ℝ)) := by
  classical
  choose C hC hpre using fun i => hscalar (a i) (ha i)
  refine ⟨∏ i,C i,Finset.prod_pos (fun i hi => hC i),?_⟩
  intro s m
  choose v hv hvnorm using fun i => hpre i (s i) (m i).val (m i).isLt
  refine ⟨productToCube d (productVector v),?_,?_⟩
  · ext t
    rw [fractionalTensorRL_product]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hv i]
    rfl
  · have hn := cube_productVector_norm_le v
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
    calc
      ‖productToCube d (productVector v)‖^2 ≤ (∏ i,‖v i‖)^2 := hsq
      _ = ∏ i,‖v i‖^2 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ i, C i*(2:ℝ)^((2*a i-1)*(s i:ℝ)) := by
        exact Finset.prod_le_prod₀ (fun i hi => sq_nonneg _) (fun i hi => hvnorm i)
      _ = (∏ i,C i)*(2:ℝ)^(∑ i, (2*a i-1)*(s i:ℝ)) := by
        rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos (by norm_num : (0:ℝ)<2)]

/-- The isotropic grade-n specialization used by the Gaussian entropy
obstruction. All constants are fixed before the grade and atom are chosen. -/
theorem layer_preimages_of_scalar {d : ℕ} {r : ℝ} (hr : 1/2<r) (hscalar : ScalarPreimages) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∀ s : Fin d → ℕ, (∑ i,s i)=n →
      ∀ m : ∀ i, Fin (2^(s i)), ∃ g : CameronMartin.UnitCubeL2 d,
        fractionalTensorRL (fun _ => r) (fun _ => hr) g = cubeTensorAtom s m ∧
        ‖g‖^2 ≤ C*(2:ℝ)^((2*r-1)*(n:ℝ)) := by
  obtain ⟨C,hC,hpre⟩ := tensor_preimages_of_scalar (fun _ : Fin d => r) (fun _ => hr) hscalar
  refine ⟨C,hC,?_⟩
  intro n s hs m
  obtain ⟨g,hg,hbound⟩ := hpre s m
  refine ⟨g,hg,?_⟩
  convert hbound using 1
  rw [← Finset.mul_sum, ← Nat.cast_sum, hs]

theorem native_preimages_of_scalar (d : ℕ) {r : ℝ} (hr : 1/2<r) (hscalar : ScalarPreimages) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ,
      ∃ v : LayerIndex d n → CameronMartin.UnitCubeL2 d,
        (∀ a, fractionalTensorRL (fun _ => r) (fun _ => hr) (v a) = cubeNativeAtom a) ∧
        ∀ a, ‖v a‖^2 ≤ C*(2:ℝ)^((2*r-1)*(n:ℝ)) := by
  classical
  obtain ⟨C,hC,hpre⟩ := layer_preimages_of_scalar (d:=d) hr hscalar
  refine ⟨C,hC,?_⟩
  intro n
  have hh : ∀ a : LayerIndex d n, ∃ g : CameronMartin.UnitCubeL2 d,
      fractionalTensorRL (fun _ => r) (fun _ => hr) g = cubeNativeAtom a ∧
      ‖g‖^2 ≤ C*(2:ℝ)^((2*r-1)*(n:ℝ)) := by
    intro a
    exact hpre n (layerIndexDepth a)
      (by simpa [layerIndexDepth,Finsupp.sum_fintype] using layerIndexDepth_grade a) a.2
  choose v hv hnorm using hh
  exact ⟨v,hv,hnorm⟩

theorem scaled_class_mass_of_scalar {d : ℕ} (hd : 1≤d)
    {r : ℝ} (hr : 1/2<r) (hscalar : ScalarPreimages) :
    ∃ a : ℝ, 0<a ∧ ∀ n : ℕ,
      (1/2:ENNReal) ≤ productStandardGaussian (LayerIndex d n)
        {x | (a*periodicSynthesisScale d n r 0) • cubeNativeSynthesisLinear x ∈
          Latest.fractionalIntegrationBall (fun _ : Fin d => r)} := by
  classical
  obtain ⟨C,hC,hsource⟩ := native_preimages_of_scalar d hr hscalar
  let B : ℝ := 2*(1+C)
  let a : ℝ := B⁻¹
  have hB : 1≤B := by dsimp [B]; linarith
  have hBpos : 0<B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨a,inv_pos.mpr hBpos,?_⟩
  intro n
  obtain ⟨v,hv,hvb⟩ := hsource n
  let R := nativeSourceRadius d n r
  let A := a*periodicSynthesisScale d n r 0
  have hR : 1≤R := nativeSourceRadius_ge_one hd (by linarith)
  have hRpos : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hA : 0<A := mul_pos (inv_pos.mpr hBpos) (periodicSynthesisScale_pos hd r 0)
  have htrace : ∑ j,‖v j‖^2 ≤ C*R^2 := by
    have ht := native_preimage_trace_bound hd v hvb
    dsimp [R]
    rw [nativeSourceRadius_sq hd]
    nlinarith [ht]
  apply (fractionalGaussianSynthesis_cutoff_mass v).trans
  apply measure_mono
  intro x hx
  have hcut : ‖fractionalGaussianSynthesis v x‖^2 ≤ 2*(1+∑ j,‖v j‖^2) := hx
  have hR2 : 1≤R^2 := by nlinarith [sq_nonneg (R-1)]
  have hbound : ‖fractionalGaussianSynthesis v x‖^2 ≤ (B*R)^2 := by
    calc
      _ ≤ 2*(1+∑ j,‖v j‖^2) := hcut
      _ ≤ 2*(1+C*R^2) := by linarith [htrace]
      _ ≤ B*R^2 := by dsimp [B]; nlinarith [hR2]
      _ ≤ (B*R)^2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hB] : B≤B^2) (sq_nonneg R)
  have hN : ‖fractionalGaussianSynthesis v x‖≤B*R := by
    nlinarith [norm_nonneg (fractionalGaussianSynthesis v x), mul_nonneg (le_trans zero_le_one hB) (le_trans zero_le_one hR)]
  have hNorm : ‖A • fractionalGaussianSynthesis v x‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hA]
    calc
      A*‖fractionalGaussianSynthesis v x‖ ≤ A*(B*R) :=
        mul_le_mul_of_nonneg_left hN hA.le
      _ = (B⁻¹*R⁻¹)*(B*R) := by
        dsimp [A,a,R]
        rw [periodicSynthesisScale_zero_eq_inv_sourceRadius hd]
      _ = 1 := by field_simp [hBpos.ne',hRpos.ne']
  change A • cubeNativeSynthesisLinear x ∈ Latest.fractionalIntegrationBall (fun _ : Fin d => r)
  rw [fractionalIntegrationBall_eq_operator_image (fun _ : Fin d => r) (fun _ => hr)]
  refine ⟨A • fractionalGaussianSynthesis v x,hNorm,?_⟩
  rw [map_smul,fractionalTensorRL_native_synthesis hr v hv x]

theorem entropy_lower_of_scalar {d : ℕ} (hd : 2 ≤ d)
    {r : ℝ} (hr : 1/2 < r) (hscalar : ScalarPreimages) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+1/2)) ≤
          HaarQuarter.TheoremD.entropyNumber k
            (Latest.fractionalIntegrationBall (fun _ : Fin d => r)) := by
  obtain ⟨a,ha,hmass⟩ := scaled_class_mass_of_scalar (d:=d) (by omega) hr hscalar
  let K := Latest.fractionalIntegrationBall (fun _ : Fin d => r)
  have hclass : ∀ n : ℕ, 0 ≤ n →
      (1/2:ENNReal)^Nat.choose (n+d-1) (d-1) ≤
        productStandardGaussian (LayerIndex d n)
          {x | (a*periodicSynthesisScale d n r 0) •
            cubeNativeSynthesisLinear x ∈ K} := by
    intro n hn
    have hmass' := hmass n
    let S := Nat.choose (n+d-1) (d-1)
    have hSpos : 1 ≤ S := by
      dsimp [S]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have hpow : (1/2:ENNReal)^S ≤ (1/2:ENNReal) := by
      have hrepr : S = (S-1)+1 := by omega
      rw [hrepr, pow_succ]
      calc
        (1/2:ENNReal)^(S-1) * (1/2:ENNReal) ≤ 1 * (1/2:ENNReal) :=
          mul_le_mul_of_nonneg_right
            (pow_le_one₀ (a := (1/2:ENNReal)) (by norm_num) (by norm_num)) (by norm_num)
        _ = 1/2 := by simp
    change (1/2:ENNReal)^S ≤ _
    exact hpow.trans hmass'
  let F : ∀ n : ℕ, (LayerIndex d n → ℝ) →ₗ[ℝ]
      C(HaarQuarter.BrownianCubeAnchor d,ℝ) :=
    fun n => cubeNativeSynthesisLinear (d:=d) (n:=n)
  simpa only [zero_mul, add_zero, K] using
    (AlignmentExponentialNativeEntropy.entropy_rate_of_scaled_native_class_mass
    (α:=HaarQuarter.BrownianCubeAnchor d) (d:=d) hd K r 0 a
    (lt_trans (by norm_num : (0:ℝ)<1/2) hr) ha 0 F
    (fun n x s hs => ⟨⟨s, fun i => hs i (Set.mem_univ i)⟩,
      AlignmentExponentialFractionalEntropy.cubeNativeSynthesis_cube_eq x _⟩)
    hclass)

end BrownianSharp.AlignmentPaperFractionalEntropyRoute
