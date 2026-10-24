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

noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
open HaarQuarter

namespace BrownianSharp.AlignmentFractionalIsotropicRates

open BrownianSharp.Latest
open BrownianSharp.AlignmentEndpointWidthExtraction
open BrownianSharp.AlignmentEndpointDyadicEntropy
open BrownianSharp.AlignmentExponentialFractionalEntropy
open BrownianSharp.AlignmentWidthRates
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentAuditPeriodicBoundedness
open HaarQuarter.TheoremD.Width

/-- Conditional isotropic fractional entropy and width closure.  The only
unproved input is the displayed dyadic width estimate; once the actual sharp
width construction supplies it, all four rates follow with common constants. -/
theorem fractional_entropy_width_of_dyadic_upper
    {d ν : ℕ} (hd : 2 ≤ d) (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) {r : ℝ} (hr : 1/2 < r)
    (hν : 2 ≤ ν) (hm : Latest.minimumMultiplicity a r ν)
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
    AlignmentFractionalAnisotropicEntropy.fractional_entropy_lower_general
      hd a ha r hr hν hm
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

/-- The full literal latest fractional entropy/width target follows if the
corresponding honest dyadic width estimate is available for every tuple. The
active-coordinate condition itself supplies `r>1/2`. -/
theorem latest_fractional_entropy_width_of_dyadic_upper
    (hdyadic : ∀ (d : ℕ), 2 ≤ d → ∀ (a : Fin d → ℝ),
      (∀ i, 1/2 < a i) → ∀ (r : ℝ) (ν : ℕ), 2 ≤ ν →
      Latest.minimumMultiplicity a r ν →
      ∃ A : ℕ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
        kolmogorovWidth (Latest.fractionalIntegrationBall a)
          (A * Fintype.card (LayerIndex ν n)) ≤
          ENNReal.ofReal (B * (2 : ℝ)^(-r * (n : ℝ)) *
            Real.sqrt ((n : ℝ) + 1))) :
    Latest.FractionalEntropyWidthStatement := by
  intro d hd a ha r ν hν hm
  have hcount : 0 < (Finset.univ.filter (fun i : Fin d => a i = r)).card := by
    rw [hm.2]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcount
  have hieq : a i = r := (Finset.mem_filter.mp hi).2
  have hr : 1/2 < r := by rw [← hieq]; exact ha i
  exact fractional_entropy_width_of_dyadic_upper hd a ha hr hν hm
    (hdyadic d hd a ha r ν hν hm)

/-- The preceding conditional theorem is exactly the isotropic
`FractionalEntropyWidthStatement` instance with multiplicity `ν=d`. -/
theorem isotropic_fractional_entropy_width_of_dyadic_upper
    {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 1/2 < r)
    (hdyadic : ∃ A : ℕ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      kolmogorovWidth (fractionalIntegrationBall (fun _ : Fin d => r))
        (A * Fintype.card (LayerIndex d n)) ≤
        ENNReal.ofReal (B * (2 : ℝ)^(-r * (n : ℝ)) *
          Real.sqrt ((n : ℝ) + 1))) :
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
  have hmult : Latest.minimumMultiplicity (fun _ : Fin d => r) r d := by
    change (∀ i, r ≤ r) ∧
      (Finset.univ.filter (fun i : Fin d => r = r)).card = d
    simp
  exact fractional_entropy_width_of_dyadic_upper hd (fun _ => r)
    (fun _ => hr) hr hd hmult hdyadic

end BrownianSharp.AlignmentFractionalIsotropicRates
