import BrownianSharp.PeriodicSynthesisScale
import BrownianSharp.AlignmentFractionalTensorAtoms
import BrownianSharp.AlignmentFractionalGaussianTrace
import BrownianSharp.PeriodicNativeGrid
import BrownianSharp.NativeRow
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalNativeLayer
open AlignmentFractionalTensorAtoms AlignmentFractionalTensorOperator

def cubeNativeAtom {d n : ℕ} (a : LayerIndex d n) : C(BrownianCubeAnchor d,ℝ) :=
  cubeTensorAtom (layerIndexDepth a) a.2

def cubeNativeSynthesisLinear {d n : ℕ} :
    (LayerIndex d n → ℝ) →ₗ[ℝ] C(BrownianCubeAnchor d,ℝ) where
  toFun x := ∑ a, x a • cubeNativeAtom a
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum,smul_smul,mul_comm]

theorem cubeNativeAtom_midpoint {d n : ℕ} (a : LayerIndex d n)
    (q : MidpointGridIndex d n) :
    cubeNativeAtom a (nativeMidpointBrownianAnchor q) = smoothLayerAtom smoothAtom q a := rfl

theorem cubeNativeSynthesis_midpoint {d n : ℕ} (x : LayerIndex d n → ℝ)
    (q : MidpointGridIndex d n) :
    cubeNativeSynthesisLinear x (nativeMidpointBrownianAnchor q) =
      ∑ a, smoothLayerAtom smoothAtom q a*x a := by
  change (∑ a, x a • cubeNativeAtom a) (nativeMidpointBrownianAnchor q) = _
  simp [cubeNativeAtom_midpoint,mul_comm]

/-- One fixed constant controls the source norms of every native atom at
every grade. The source family need not be orthogonal. -/
theorem isotropic_native_preimages (d : ℕ) {r : ℝ} (hr : 1/2<r) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ,
      ∃ v : LayerIndex d n → CameronMartin.UnitCubeL2 d,
        (∀ a, fractionalTensorRL (fun _ => r) (fun _ => hr) (v a) = cubeNativeAtom a) ∧
        ∀ a, ‖v a‖^2 ≤ C*(2:ℝ)^((2*r-1)*(n:ℝ)) := by
  classical
  obtain ⟨C,hC,hpre⟩ := isotropic_layer_preimages (d:=d) hr
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

theorem fractionalTensorRL_native_synthesis {d n : ℕ} {r : ℝ} (hr : 1/2<r)
    (v : LayerIndex d n → CameronMartin.UnitCubeL2 d)
    (hv : ∀ a, fractionalTensorRL (fun _ => r) (fun _ => hr) (v a) = cubeNativeAtom a)
    (x : LayerIndex d n → ℝ) :
    fractionalTensorRL (fun _ => r) (fun _ => hr) (fractionalGaussianSynthesis v x) =
      cubeNativeSynthesisLinear x := by
  unfold fractionalGaussianSynthesis cubeNativeSynthesisLinear
  rw [map_sum]
  simp_rw [map_smul,hv]
  rfl

theorem native_preimage_trace_le {d n : ℕ} (v : LayerIndex d n → CameronMartin.UnitCubeL2 d)
    {r C : ℝ} (hv : ∀ a, ‖v a‖^2 ≤ C*(2:ℝ)^((2*r-1)*(n:ℝ))) :
    ∑ a, ‖v a‖^2 ≤ (Fintype.card (LayerIndex d n):ℝ)*C*(2:ℝ)^((2*r-1)*(n:ℝ)) := by
  calc
    ∑ a,‖v a‖^2 ≤ ∑ _a : LayerIndex d n,C*(2:ℝ)^((2*r-1)*(n:ℝ)) :=
      Finset.sum_le_sum fun a ha => hv a
    _ = _ := by simp; ring

theorem native_preimage_trace_bound {d n : ℕ} (hd : 1≤d)
    (v : LayerIndex d n → CameronMartin.UnitCubeL2 d) {r C : ℝ}
    (hv : ∀ a, ‖v a‖^2 ≤ C*(2:ℝ)^((2*r-1)*(n:ℝ))) :
    ∑ a, ‖v a‖^2 ≤ C*(2:ℝ)^(2*r*(n:ℝ))*hyperbolicCount d n := by
  have hD : (Fintype.card (LayerIndex d n):ℝ) =
      (2:ℝ)^n*hyperbolicCount d n := by
    rw [layerIndex_card d n (by omega)]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,hyperbolicCount]
  have hp : (2:ℝ)^n * (2:ℝ)^((2*r-1)*(n:ℝ)) = (2:ℝ)^(2*r*(n:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  calc
    _ ≤ (Fintype.card (LayerIndex d n):ℝ)*C*(2:ℝ)^((2*r-1)*(n:ℝ)) :=
      native_preimage_trace_le v hv
    _ = C*((2:ℝ)^n*(2:ℝ)^((2*r-1)*(n:ℝ)))*hyperbolicCount d n := by rw [hD]; ring
    _ = _ := by rw [hp]

def nativeSourceRadius (d n : ℕ) (r : ℝ) : ℝ :=
  (2:ℝ)^(r*(n:ℝ))*Real.sqrt (hyperbolicCount d n)

theorem nativeSourceRadius_ge_one {d n : ℕ} (hd : 1≤d) {r : ℝ} (hr : 0≤r) :
    1≤nativeSourceRadius d n r := by
  have hS : 1≤hyperbolicCount d n := by
    unfold hyperbolicCount
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.choose_pos (by omega : d-1≤n+d-1)))
  have hp : 1≤(2:ℝ)^(r*(n:ℝ)) := Real.one_le_rpow (by norm_num) (mul_nonneg hr (Nat.cast_nonneg n))
  have hsq : 1≤Real.sqrt (hyperbolicCount d n) := by
    simpa using Real.sqrt_le_sqrt hS
  exact one_le_mul_of_one_le_of_one_le hp hsq

theorem nativeSourceRadius_sq {d n : ℕ} (hd : 1≤d) (r : ℝ) :
    (nativeSourceRadius d n r)^2 =
      (2:ℝ)^(2*r*(n:ℝ))*hyperbolicCount d n := by
  have hp : ((2:ℝ)^(r*(n:ℝ)))^2 = (2:ℝ)^(2*r*(n:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  unfold nativeSourceRadius
  rw [mul_pow,hp,Real.sq_sqrt (hyperbolicCount_pos hd).le]

theorem periodicSynthesisScale_zero_eq_inv_sourceRadius {d n : ℕ} (hd : 1≤d) (r : ℝ) :
    periodicSynthesisScale d n r 0 = (nativeSourceRadius d n r)⁻¹ := by
  have hS := hyperbolicCount_pos (n:=n) hd
  unfold periodicSynthesisScale nativeSourceRadius
  rw [Real.sqrt_eq_rpow, mul_inv_rev,
    ← Real.rpow_neg (by norm_num : (0:ℝ)≤2), ← Real.rpow_neg hS.le]
  simp only [zero_sub,neg_mul]
  ring

/-- A grade-independent normalization puts at least half of each Gaussian
native layer in the actual RL unit ball. The trace identity, rather than a
false orthogonality assumption for overlapping preimages, supplies the mass. -/
theorem isotropic_fractional_scaled_class_mass {d : ℕ} (hd : 1≤d)
    {r : ℝ} (hr : 1/2<r) :
    ∃ a : ℝ, 0<a ∧ ∀ n : ℕ,
      (1/2:ENNReal) ≤ productStandardGaussian (LayerIndex d n)
        {x | (a*periodicSynthesisScale d n r 0) • cubeNativeSynthesisLinear x ∈
          Latest.fractionalIntegrationBall (fun _ : Fin d => r)} := by
  classical
  obtain ⟨C,hC,hsource⟩ := isotropic_native_preimages d hr
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

end BrownianSharp.AlignmentFractionalNativeLayer
