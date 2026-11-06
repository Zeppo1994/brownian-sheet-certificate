import BrownianSharp.AlignmentEndpointWidthExtraction
import BrownianSharp.AlignmentEndpointDyadicEntropy
import BrownianSharp.AlignmentExponentialFractionalEntropy
import BrownianSharp.AlignmentFractionalAnisotropicEntropy
import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentAuditPeriodicBoundedness
import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.LayerIndex
import Mathlib.Tactic
import BrownianSharp.AlignmentFractionalGradedPolynomialWidth
import BrownianSharp.AlignmentOperatorStatements
import BrownianSharp.AlignmentOperatorWidthIndexShift
import BrownianSharp.AlignmentPaperFractionalEntropyRoute

/-! Carl closure with an explicit entropy-lower provider. This lets the paper
endpoint use Fourier-derived preimages all the way through its lower bound. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPaperFractionalCarlRoute
open BrownianSharp.Latest
open BrownianSharp.AlignmentEndpointWidthExtraction
open BrownianSharp.AlignmentEndpointDyadicEntropy
open BrownianSharp.AlignmentWidthRates
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentAuditPeriodicBoundedness
open HaarQuarter.TheoremD.Width
open BrownianSharp.AlignmentOperatorWidthIndexShift
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentOperatorNumbers

theorem entropy_width_of_lower_and_dyadic_upper
    {d ν : ℕ} (hd : 2 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) {r : ℝ} (hr : 1/2 < r)
    (hν : 2 ≤ ν)
    (hlower : ∃ cL : ℝ, 0 < cL ∧ ∃ kL : ℕ, 2 ≤ kL ∧
      ∀ k : ℕ, kL ≤ k →
        ENNReal.ofReal (cL * (k:ℝ)^(-r) * (Real.log (k:ℝ))^
          (r*((ν-1:ℕ):ℝ)+1/2)) ≤
            HaarQuarter.TheoremD.entropyNumber k (fractionalIntegrationBall a))
    (hdyadic : ∃ A : ℕ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      kolmogorovWidth (fractionalIntegrationBall a)
        (A * Fintype.card (LayerIndex ν n)) ≤
        ENNReal.ofReal (B * (2 : ℝ)^(-r * (n : ℝ)) *
          Real.sqrt ((n : ℝ) + 1))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r
        (r * ((ν - 1 : ℕ) : ℝ) + 1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            (fractionalIntegrationBall a) ∧
      HaarQuarter.TheoremD.entropyNumber k
          (fractionalIntegrationBall a) ≤
        ENNReal.ofReal (C * logarithmicIndexRate r
          (r * ((ν - 1 : ℕ) : ℝ) + 1/2) k) ∧
      ENNReal.ofReal (c * logarithmicIndexRate r
        (r * ((ν - 1 : ℕ) : ℝ) + 1/2) k) ≤
          kolmogorovWidth (fractionalIntegrationBall a) k ∧
      kolmogorovWidth (fractionalIntegrationBall a) k ≤
        ENNReal.ofReal (C * logarithmicIndexRate r
          (r * ((ν - 1 : ℕ) : ℝ) + 1/2) k) := by
  classical
  let K : Set C(BrownianCubeAnchor d, ℝ) :=
    fractionalIntegrationBall a
  let α : ℝ := r * ((ν - 1 : ℕ) : ℝ) + 1/2
  obtain ⟨A,hA,B,hB,hdyadic⟩ := hdyadic
  have hrpos : 0 < r := by linarith
  obtain ⟨CW,hCW,mW,hmW,hwidth⟩ :=
    all_index_width_rate_of_dyadic_layer_bound hν K A hA r (1/2) B
      hrpos (by norm_num) hB 0 (by
        intro n hn
        have h := hdyadic n
        simpa only [Real.sqrt_eq_rpow] using h)
  let op : CameronMartin.UnitCubeL2 d →L[ℝ] C(BrownianCubeAnchor d, ℝ) :=
    fractionalTensorRL a ha
  let R : ℝ := ‖op‖
  have hR : 0 ≤ R := by dsimp [R]; exact norm_nonneg op
  have hbound : ∀ f ∈ K, ‖f‖ ≤ R := by
    intro f hf
    change f ∈ fractionalIntegrationBall a at hf
    rw [fractionalIntegrationBall_eq_operator_image a ha] at hf
    rcases hf with ⟨g,hg,rfl⟩
    dsimp [R,op]
    calc
      ‖fractionalTensorRL a ha g‖ ≤
          ‖fractionalTensorRL a ha‖ * ‖g‖ :=
        (fractionalTensorRL a ha).le_opNorm g
      _ ≤ ‖fractionalTensorRL a ha‖ :=
        mul_le_of_le_one_right (norm_nonneg (fractionalTensorRL a ha)) hg
  have hzero : kolmogorovWidth K 0 ≤ ENNReal.ofReal R :=
    kolmogorovWidth_zero_le_of_norm_bound K R hbound
  let mW' := max 2 mW
  obtain ⟨CE,hCE,kE,hkE,hEntropyUpper⟩ :=
    entropy_upper_all_indices_of_width_upper K (s:=r) (a:=α) (R:=R) (C:=CW)
      (by linarith) (by positivity) hR hCW mW' (le_max_left _ _) hzero
      (by
        intro k hk
        exact hwidth k ((le_max_right _ _).trans hk))
  obtain ⟨cL,hcL,kL,hkL,hEntropyLowerRaw⟩ :=
    hlower
  have hEntropyLower : ∀ k : ℕ, kL ≤ k →
      ENNReal.ofReal (cL * logarithmicIndexRate r α k) ≤
        HaarQuarter.TheoremD.entropyNumber k K := by
    intro k hk
    have h := hEntropyLowerRaw k hk
    simpa only [logarithmicIndexRate, ← mul_assoc, K, α] using h
  obtain ⟨cW,CW',hcW,hCW',kW,hkW,hWidth⟩ :=
    twoSidedWidthRate_of_entropy_lower_and_width_upper K r α R hrpos
      (by positivity) hR hzero
      ⟨cL,hcL,kL,fun k hk => hEntropyLower k hk⟩
      ⟨CW,hCW,mW,fun k hk => by
        simpa only [K, logarithmicIndexRate] using hwidth k hk⟩
  have hWidthLower : ∀ k : ℕ, kW ≤ k →
      ENNReal.ofReal (cW * logarithmicIndexRate r α k) ≤
        kolmogorovWidth K k := by
    intro k hk
    exact (hWidth k hk).1
  have hWidthUpper : ∀ k : ℕ, kW ≤ k →
      kolmogorovWidth K k ≤
        ENNReal.ofReal (CW' * logarithmicIndexRate r α k) := by
    intro k hk
    exact (hWidth k hk).2
  let c := min cL cW
  let C := max CE CW'
  let k₀ := max 2 (max kL (max kE (max kW mW')))
  have hc : 0 < c := by dsimp [c]; exact lt_min hcL hcW
  have hC : 0 < C := by dsimp [C]; exact lt_max_of_lt_left hCE
  refine ⟨c,C,hc,hC,k₀,?_,?_⟩
  · dsimp [k₀]
    omega
  · intro k hk
    have hkL' : kL ≤ k := by dsimp [k₀] at hk; omega
    have hkE' : kE ≤ k := by dsimp [k₀] at hk; omega
    have hkW' : kW ≤ k := by dsimp [k₀] at hk; omega
    have hmW'k : mW' ≤ k := by dsimp [k₀] at hk; omega
    have hrate : 0 ≤ logarithmicIndexRate r α k :=
      logarithmicIndexRate_nonneg r α k
    have hEL := hEntropyLower k hkL'
    have hEU := hEntropyUpper k hkE'
    have hWL := hWidthLower k hkW'
    have hWU := hWidthUpper k hkW'
    refine ⟨?_,?_,?_,?_⟩
    · exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hrate)).trans hEL
    · exact hEU.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hrate))
    · exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hrate)).trans hWL
    · exact hWU.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hrate))

/-- All four isotropic rates, with the lower bound supplied by the scalar
preimage route and the upper bound by the actual polynomial width theorem. -/
theorem isotropic_rates_of_scalar
    {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 1/2 < r)
    (hscalar : AlignmentPaperFractionalEntropyRoute.ScalarPreimages) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r
        (r * ((d - 1 : ℕ) : ℝ) + 1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            (fractionalIntegrationBall (fun _ : Fin d => r)) ∧
      HaarQuarter.TheoremD.entropyNumber k
          (fractionalIntegrationBall (fun _ : Fin d => r)) ≤
        ENNReal.ofReal (C * logarithmicIndexRate r
          (r * ((d - 1 : ℕ) : ℝ) + 1/2) k) ∧
      ENNReal.ofReal (c * logarithmicIndexRate r
        (r * ((d - 1 : ℕ) : ℝ) + 1/2) k) ≤
          kolmogorovWidth (fractionalIntegrationBall (fun _ : Fin d => r)) k ∧
      kolmogorovWidth (fractionalIntegrationBall (fun _ : Fin d => r)) k ≤
        ENNReal.ofReal (C * logarithmicIndexRate r
          (r * ((d - 1 : ℕ) : ℝ) + 1/2) k) := by
  have hmin : minimumMultiplicity (fun _ : Fin d => r) r d := by
    constructor
    · intro i; exact le_rfl
    · simp
  have hupper :=
    AlignmentFractionalGradedPolynomialWidth.polynomial_fractional_tensor_RL_dyadic_width
      (ν := d) (e := 0) hd hr (fun _ => r) (fun _ => hr) hmin
  exact entropy_width_of_lower_and_dyadic_upper hd (fun _ => r) (fun _ => hr)
    hr hd (AlignmentPaperFractionalEntropyRoute.entropy_lower_of_scalar hd hr hscalar)
    hupper

/-- The manuscript uses operator Kolmogorov numbers (subspace dimension
strictly less than k); apply the established predecessor-index comparison. -/
theorem isotropic_operator_rates_of_scalar
    {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 1/2 < r)
    (hscalar : AlignmentPaperFractionalEntropyRoute.ScalarPreimages) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate r
          (r * (d - 1 : ℕ) + 1/2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k
              (fractionalIntegrationBall (fun _ : Fin d => r)) ∧
        HaarQuarter.TheoremD.entropyNumber k
          (fractionalIntegrationBall (fun _ : Fin d => r)) ≤
            ENNReal.ofReal (C * logarithmicIndexRate r
              (r * (d - 1 : ℕ) + 1/2) k) ∧
        ENNReal.ofReal (c * logarithmicIndexRate r
          (r * (d - 1 : ℕ) + 1/2) k) ≤
            AlignmentOperatorNumbers.operatorKolmogorovNumber
              (fractionalIntegrationBall (fun _ : Fin d => r)) k ∧
        AlignmentOperatorNumbers.operatorKolmogorovNumber
          (fractionalIntegrationBall (fun _ : Fin d => r)) k ≤
            ENNReal.ofReal (C * logarithmicIndexRate r
              (r * (d - 1 : ℕ) + 1/2) k) := by
  classical
  have hrpos : 0 < r := by linarith
  let α : ℝ := r * (d-1:ℕ) + 1/2
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨c₀,C₀,hc₀,hC₀,kOld,hkOld,hindex⟩ :=
    isotropic_rates_of_scalar hd hr hscalar
  let C : ℝ := max C₀ (C₀ * 2^r)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨c₀,C,hc₀,hC,max (kOld+1) 3,by omega,?_⟩
  intro k hk
  have hk3 : 3 ≤ k := (le_max_right _ _).trans hk
  have hkOld' : kOld ≤ k-1 := by
    have := (le_max_left (kOld+1) 3).trans hk
    omega
  have hkOldK : kOld ≤ k := by omega
  have hK := hindex k hkOldK
  have hPred := hindex (k-1) hkOld'
  have hrate : 0 ≤ logarithmicIndexRate r α k :=
    logarithmicIndexRate_nonneg r α k
  have hpredRate := (rate_succ_comparable hrpos hα hk3).2
  change logarithmicIndexRate r α (k-1) ≤ 2^r * logarithmicIndexRate r α k at hpredRate
  refine ⟨hK.1,?_,?_,?_⟩
  · exact hK.2.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left C₀ (C₀*2^r)) hrate))
  · rw [operatorKolmogorovNumber_eq_width_pred
      (Latest.fractionalIntegrationBall (fun _ : Fin d => r)) (by omega : 1 ≤ k)]
    exact hK.2.2.1.trans (kolmogorovWidth_antitone
      (Latest.fractionalIntegrationBall (fun _ : Fin d => r)) (Nat.sub_le k 1))
  · rw [operatorKolmogorovNumber_eq_width_pred
      (Latest.fractionalIntegrationBall (fun _ : Fin d => r)) (by omega : 1 ≤ k)]
    refine hPred.2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmul := mul_le_mul_of_nonneg_left hpredRate hc₀.le
    have hmul' := mul_le_mul_of_nonneg_left hpredRate hC₀.le
    calc
      C₀ * logarithmicIndexRate r α (k-1) ≤
          (C₀ * 2^r) * logarithmicIndexRate r α k := by
            simpa only [mul_assoc] using hmul'
      _ ≤ C * logarithmicIndexRate r α k :=
        mul_le_mul_of_nonneg_right (le_max_right C₀ (C₀*2^r)) hrate

end BrownianSharp.AlignmentPaperFractionalCarlRoute
