import BrownianSharp.AlignmentGaussianChaining
import BrownianSharp.AlignmentExponentialGaussianMaximum
import BrownianSharp.AlignmentHolderChainingBudget

/-! Quantitative continuum Gaussian chaining at every positive Hölder exponent. -/
noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators NNReal
namespace BrownianSharp.AlignmentHolderGaussianChaining
open AlignmentGaussianChaining AlignmentExponentialGaussianMaximum
open AlignmentHolderChainingBudget

def holderChainingConstant (d : ℕ) (h : ℝ) : ℝ :=
  2*Real.sqrt ((d:ℝ)+2) +
    2*Real.sqrt (2*(d:ℝ)+2)*holderTailConstant h + 1

theorem holderChainingConstant_pos (d : ℕ) (h : ℝ) :
    0 < holderChainingConstant d h := by
  have hc := holderTailConstant_nonneg h
  unfold holderChainingConstant
  positivity

theorem gaussian_chaining_expected_norm_holder (h : ℝ) (hh : 0 < h)
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Ω→C(BrownianCubeAnchor d,ℝ))
    (hF : Measurable F) (v : BrownianCubeAnchor d→ℝ≥0)
    (vinc : (N : ℕ)→CubeNearPairs d N→ℝ≥0)
    (hLaw : ∀x,HasLaw (fun ω=>F ω x) (gaussianReal 0 (v x)) P)
    (hLawInc : ∀N (p : CubeNearPairs d N),HasLaw
      (fun ω=>F ω (cubeDyadicAnchor p.val.2)-F ω (cubeDyadicAnchor p.val.1))
      (gaussianReal 0 (vinc N p)) P)
    (σ L : ℝ) (hσ : 0≤σ) (hL : 0≤L)
    (hvar : ∀x,(v x:ℝ)≤σ^2)
    (hvarInc : ∀N p,(vinc N p:ℝ)≤(L*(2:ℝ)^(-h*(N:ℝ)))^2)
    (n₀ : ℕ) :
    Integrable (fun ω=>‖F ω‖) P ∧
      (∫ω,‖F ω‖ ∂P)≤holderChainingConstant d h*Real.sqrt ((n₀:ℝ)+1)*
        (σ+L*(2:ℝ)^(-h*(n₀:ℝ))) := by
  let U : ℝ := 2*Real.sqrt ((d:ℝ)+2)
  let V : ℝ := 2*Real.sqrt (2*(d:ℝ)+2)
  let B₀ : ℝ := U*σ*Real.sqrt ((n₀:ℝ)+1)
  let b : ℕ→ℝ := fun k=>V*L*((2:ℝ)^(-h*((n₀+k:ℕ):ℝ))*
    Real.sqrt (((n₀+k:ℕ):ℝ)+2))
  have hU : 0≤U := by dsimp [U]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hb : ∀k,0≤b k := by intro k; dsimp [b]; positivity
  have hbs : Summable b := (summable_holder_chaining_tail hh n₀).mul_left (V*L)
  have hbaseInt : Integrable (fun ω=>cubeGridMaximum n₀ (F ω)) P := by
    exact gaussian_max_abs_integrable
      (fun j : CubeDyadicGrid d n₀=>fun ω=>F ω (cubeDyadicAnchor j))
      (fun j=>hLaw _)
  have hincInt : ∀n,Integrable (fun ω=>cubeGridIncrementMaximum (n₀+n) (F ω)) P := by
    intro n
    exact gaussian_max_abs_integrable
      (fun p : CubeNearPairs d (n₀+n)=>fun ω=>
        F ω (cubeDyadicAnchor p.val.2)-F ω (cubeDyadicAnchor p.val.1))
      (hLawInc (n₀+n))
  have hbase : (∫ω,cubeGridMaximum n₀ (F ω) ∂P)≤B₀ := by
    have hm := expected_max_le_sqrt_log
      (fun j : CubeDyadicGrid d n₀=>fun ω=>F ω (cubeDyadicAnchor j))
      (fun j=>hLaw _) hσ (fun j=>hvar _)
    calc
      _≤2*σ*Real.sqrt (Real.log (2*(Fintype.card (CubeDyadicGrid d n₀):ℝ)+2)) := hm
      _≤2*σ*Real.sqrt (((d:ℝ)+2)*((n₀:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (cubeGrid_log_card_le d n₀))
          (mul_nonneg (by norm_num) hσ)
      _=B₀ := by rw [Real.sqrt_mul (by positivity)]; dsimp [B₀,U]; ring
  have hinc : ∀n,(∫ω,cubeGridIncrementMaximum (n₀+n) (F ω) ∂P)≤b n := by
    intro n
    let N := n₀+n
    have hm := expected_max_le_sqrt_log
      (fun p : CubeNearPairs d N=>fun ω=>
        F ω (cubeDyadicAnchor p.val.2)-F ω (cubeDyadicAnchor p.val.1))
      (hLawInc N) (show 0≤L*(2:ℝ)^(-h*(N:ℝ)) by positivity) (hvarInc N)
    calc
      _≤2*(L*(2:ℝ)^(-h*(N:ℝ)))*
          Real.sqrt (Real.log (2*(Fintype.card (CubeNearPairs d N):ℝ)+2)) := hm
      _≤2*(L*(2:ℝ)^(-h*(N:ℝ)))*
          Real.sqrt ((2*(d:ℝ)+2)*((N:ℝ)+2)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (cubeNearPairs_log_card_le d N))
          (by positivity)
      _=b n := by rw [Real.sqrt_mul (by positivity)]; dsimp [b,V,N]; ring
  obtain ⟨hInt,hE⟩ := integrable_norm_and_integral_le_of_grid_bounds P F hF n₀
    B₀ (by dsimp [B₀]; positivity) b hb hbs hbaseInt hincInt hbase hinc
  refine ⟨hInt,hE.trans ?_⟩
  have hsum : (∑'k,b k)≤V*L*(holderTailConstant h)*
      (2:ℝ)^(-h*(n₀:ℝ))*Real.sqrt ((n₀:ℝ)+1) := by
    rw [show b=(fun k=>V*L*((2:ℝ)^(-h*((n₀+k:ℕ):ℝ))*
      Real.sqrt (((n₀+k:ℕ):ℝ)+2))) by rfl,tsum_mul_left]
    have hh := mul_le_mul_of_nonneg_left (holder_chaining_tail_le hh n₀) (mul_nonneg hV hL)
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc] using hh
  have hUC : U≤holderChainingConstant d h := by
    dsimp [U,holderChainingConstant]
    have hc := mul_nonneg (Real.sqrt_nonneg (2*(d:ℝ)+2)) (holderTailConstant_nonneg h)
    nlinarith
  have hVC : V*(holderTailConstant h)≤holderChainingConstant d h := by
    dsimp [V,holderChainingConstant]
    nlinarith [Real.sqrt_nonneg ((d:ℝ)+2)]
  calc
    B₀+∑'k,b k≤U*σ*Real.sqrt ((n₀:ℝ)+1)+
        V*L*(holderTailConstant h)*(2:ℝ)^(-h*(n₀:ℝ))*Real.sqrt ((n₀:ℝ)+1) :=
      add_le_add le_rfl hsum
    _≤holderChainingConstant d h*σ*Real.sqrt ((n₀:ℝ)+1)+
        holderChainingConstant d h*L*(2:ℝ)^(-h*(n₀:ℝ))*Real.sqrt ((n₀:ℝ)+1) := by
      apply add_le_add
      · gcongr
      · calc
          _=(V*(holderTailConstant h))*L*(2:ℝ)^(-h*(n₀:ℝ))*Real.sqrt ((n₀:ℝ)+1) := by ring
          _≤_ := by gcongr
    _=holderChainingConstant d h*Real.sqrt ((n₀:ℝ)+1)*
        (σ+L*(2:ℝ)^(-h*(n₀:ℝ))) := by ring


end BrownianSharp.AlignmentHolderGaussianChaining
