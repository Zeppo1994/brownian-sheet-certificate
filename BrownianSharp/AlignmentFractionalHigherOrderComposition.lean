import BrownianSharp.AlignmentFractionalTensorL2Semigroup
import BrownianSharp.AlignmentFractionalApproximationProductLower
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.ExtendedStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! General semigroup composition transfer: a lower approximation rate at any
order `M > r+1/2`, together with the actual L² upper rate at `M-r`, yields the
sharp lower rate at order `r`. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
open scoped ENNReal

namespace BrownianSharp.AlignmentFractionalHigherOrderComposition

open BrownianSharp.AlignmentFractionalTensorOperator
  BrownianSharp.AlignmentFractionalTensorL2Semigroup
  BrownianSharp.AlignmentFractionalApproximationNumbers
  BrownianSharp.AlignmentFractionalApproximationProductLower
  BrownianSharp

private theorem rate_at_double_index_le
    (k : ℕ) (hk : 2 ≤ k) (b ell : ℝ) (hb : 0 < b) (hell : 0 ≤ ell) :
    logarithmicIndexRate b ell k ≤
      (2:ℝ)^b * logarithmicIndexRate b ell (2*k-1) := by
  have hkR : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hqR : 0 < ((2*k-1:ℕ):ℝ) := by exact_mod_cast (show 0<2*k-1 by omega)
  have hqle : ((2*k-1:ℕ):ℝ) ≤ 2*(k:ℝ) := by
    exact_mod_cast (show 2*k-1 ≤ 2*k by omega)
  have hkq : (k:ℝ) ≤ ((2*k-1:ℕ):ℝ) := by
    exact_mod_cast (show k ≤ 2*k-1 by omega)
  have hlogk : 0 < Real.log (k:ℝ) := Real.log_pos (by exact_mod_cast (show 1<k by omega))
  have hlogq : 0 < Real.log ((2*k-1:ℕ):ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<2*k-1 by omega))
  have hlogle : Real.log (k:ℝ) ≤ Real.log ((2*k-1:ℕ):ℝ) :=
    Real.log_le_log hkR hkq
  have hpower : (Real.log (k:ℝ))^ell ≤
      (Real.log ((2*k-1:ℕ):ℝ))^ell :=
    Real.rpow_le_rpow hlogk.le hlogle hell
  have hscale : (k:ℝ)^(-b) ≤ (2:ℝ)^b * ((2*k-1:ℕ):ℝ)^(-b) := by
    have hpow : ((2*k-1:ℕ):ℝ)^b ≤ (2*(k:ℝ))^b :=
      Real.rpow_le_rpow hqR.le hqle hb.le
    have htwo : (2*(k:ℝ))^b = (2:ℝ)^b*(k:ℝ)^b := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hkR.le]
    rw [Real.rpow_neg hkR.le, Real.rpow_neg hqR.le]
    change ((k:ℝ)^b)⁻¹ ≤ (2:ℝ)^b * (((2*k-1:ℕ):ℝ)^b)⁻¹
    have hposk : 0 < (k:ℝ)^b := Real.rpow_pos_of_pos hkR b
    have hposq : 0 < ((2*k-1:ℕ):ℝ)^b := Real.rpow_pos_of_pos hqR b
    have hbase : ((2*k-1:ℕ):ℝ)^b ≤ (2:ℝ)^b*(k:ℝ)^b := by
      rw [← htwo]
      exact hpow
    have hdiv : 1/((k:ℝ)^b) ≤ (2:ℝ)^b/((2*k-1:ℕ):ℝ)^b :=
      (div_le_div_iff₀ hposk hposq).2 (by nlinarith [hbase])
    simpa [div_eq_mul_inv] using hdiv
  unfold logarithmicIndexRate
  calc
    (k:ℝ)^(-b) * (Real.log (k:ℝ))^ell ≤
        ((2:ℝ)^b*((2*k-1:ℕ):ℝ)^(-b)) *
          (Real.log ((2*k-1:ℕ):ℝ))^ell :=
      mul_le_mul hscale hpower (Real.rpow_nonneg hlogk.le _) (by positivity)
    _ = (2:ℝ)^b * (((2*k-1:ℕ):ℝ)^(-b) *
          (Real.log ((2*k-1:ℕ):ℝ))^ell) := by ring

/-- Higher-order isotropic lower-rate transfer. The analytic inputs are only
the actual order-`M` C-valued lower rate and the actual order-`M-r` L² upper
rate; the RL semigroup and approximation-number product inequality are proved
for the actual operators. -/
theorem isotropic_fractional_approximation_lower_of_higher_order_and_L2
    {d : ℕ} (hd : 2 ≤ d) (r M : ℝ)
    (hr : 1/2 < r) (hM : r+1/2 < M)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∃ k₁ : ℕ, 2 ≤ k₁ ∧
      ∀ k : ℕ, k₁ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate (M-1/2)
          (M*((d-1:ℕ):ℝ)) k) ≤
          approximationNumber (fractionalTensorRL (fun _ : Fin d => M)
            (fun _ => by linarith)) k)
    (hupper : ∃ C : ℝ, 0 < C ∧ ∃ k₂ : ℕ, 2 ≤ k₂ ∧
      ∀ k : ℕ, k₂ ≤ k →
        approximationNumber (fractionalTensorRLToL2 (d:=d)
          (fun _ : Fin d => M-r) (fun _ => by linarith)) k ≤
          ENNReal.ofReal (C * logarithmicIndexRate (M-r)
            ((M-r)*((d-1:ℕ):ℝ)) k)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c₀ * logarithmicIndexRate (r-1/2)
        (r*((d-1:ℕ):ℝ)) k) ≤
        approximationNumber (fractionalTensorRL (fun _ : Fin d => r)
          (fun _ => hr)) k := by
  obtain ⟨c,hc,k₁,hk₁,hlo⟩ := hlower
  obtain ⟨C,hC,k₂,hk₂,hup⟩ := hupper
  let b : ℝ := M-r
  let a : ℝ := ((d-1:ℕ):ℝ)
  have hb : 1/2 < b := by dsimp [b]; linarith
  have hb0 : 0 < b := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hC' : 0 < C*(2:ℝ)^b := by positivity
  let k₀ : ℕ := max 2 (max k₁ k₂)
  refine ⟨(c/(C*(2:ℝ)^b))*(2:ℝ)^(-(r-1/2)), ?_, k₀,
    le_max_left _ _, ?_⟩
  · positivity
  · intro k hk
    have hk2 : 2 ≤ k := (le_max_left 2 _).trans hk
    have hk1 : k₁ ≤ k :=
      le_trans (le_max_left k₁ k₂) (le_trans (le_max_right 2 (max k₁ k₂)) hk)
    have hk2' : k₂ ≤ k :=
      le_trans (le_max_right k₁ k₂) (le_trans (le_max_right 2 (max k₁ k₂)) hk)
    let q : ℕ := k+k-1
    have hqeq : q = 2*k-1 := by dsimp [q]; omega
    have hq1 : 1 ≤ q := by dsimp [q]; omega
    have hqk : k₁ ≤ q := by dsimp [q]; omega
    have hqR : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
    have hy : 0 < Real.log (q:ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1<q by omega))
    have hlow := hlo q hqk
    have hupk := hup k hk2'
    have hrateβ := rate_at_double_index_le k hk2 b (b*a) hb0 (mul_nonneg hb0.le ha)
    have hrateβq : logarithmicIndexRate b (b*a) k ≤
        (2:ℝ)^b * logarithmicIndexRate b (b*a) q := by
      simpa [hqeq] using hrateβ
    have hup' : approximationNumber (fractionalTensorRLToL2 (d:=d)
        (fun _ : Fin d => b) (fun _ => hb)) k ≤
        ENNReal.ofReal ((C*(2:ℝ)^b) * logarithmicIndexRate b (b*a) q) := by
      apply hupk.trans
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left hrateβq hC.le]
    have hsemigroup := fractionalTensorRL_semigroup (d:=d) hr hb
    have hsum : r+b=M := by dsimp [b]; ring
    have hsem : fractionalTensorRL (fun _ : Fin d => M) (fun _ => by linarith) =
        (fractionalTensorRL (fun _ : Fin d => r) (fun _ => hr)).comp
          (fractionalTensorRLToL2 (d:=d) (fun _ : Fin d => b) (fun _ => hb)) := by
      simpa [hsum] using hsemigroup
    have hlowAt : ENNReal.ofReal
        (c*((q:ℝ)^(-M+1/2)*(Real.log (q:ℝ))^(M*a))) ≤
        approximationNumber
          ((fractionalTensorRL (fun _ : Fin d => r) (fun _ => hr)).comp
            (fractionalTensorRLToL2 (d:=d) (fun _ : Fin d => b) (fun _ => hb))) q := by
      rw [hsem] at hlow
      have hlow' := hlow
      simp only [logarithmicIndexRate] at hlow'
      have hexp : -(M-1/2) = -M+1/2 := by ring
      rw [hexp] at hlow'
      simpa [a, mul_assoc] using hlow'
    have hprod := approximationNumber_lower_power_log
      (fractionalTensorRL (fun _ : Fin d => r) (fun _ => hr))
      (fractionalTensorRLToL2 (d:=d) (fun _ : Fin d => b) (fun _ => hb))
      (m:=k) (n:=k) (by omega) (by omega) (q:ℝ) (Real.log (q:ℝ)) c
      (C*(2:ℝ)^b) M b a hqR hy hC' hlowAt hup'
    have hγ : 0 < r-1/2 := by linarith
    have hrateγ := rate_at_double_index_le k hk2 (r-1/2) (r*a) hγ
      (mul_nonneg (by linarith) ha)
    have hfac : (2:ℝ)^(-(r-1/2))*(2:ℝ)^(r-1/2)=1 := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) (r-1/2)))
    have hrate' : (c/(C*(2:ℝ)^b))*(2:ℝ)^(-(r-1/2)) *
        logarithmicIndexRate (r-1/2) (r*a) k ≤
        (c/(C*(2:ℝ)^b))*(q:ℝ)^(-(r-1/2))*(Real.log (q:ℝ))^(r*a) := by
      unfold logarithmicIndexRate at hrateγ ⊢
      calc
        _ ≤ (c/(C*(2:ℝ)^b))*(2:ℝ)^(-(r-1/2)) *
            ((2:ℝ)^(r-1/2) *
              (((2*k-1:ℕ):ℝ)^(-(r-1/2)) *
                (Real.log ((2*k-1:ℕ):ℝ))^(r*a))) := by
          exact mul_le_mul_of_nonneg_left hrateγ
            (by positivity : 0 ≤ (c/(C*(2:ℝ)^b))*(2:ℝ)^(-(r-1/2)))
        _ = (c/(C*(2:ℝ)^b))*(q:ℝ)^(-(r-1/2)) *
              (Real.log (q:ℝ))^(r*a) := by
          rw [hqeq]
          calc
            _ = (c/(C*(2:ℝ)^b)) *
                ((2:ℝ)^(-(r-1/2))*(2:ℝ)^(r-1/2)) *
                  ((2*k-1:ℕ):ℝ)^(-(r-1/2)) *
                    (Real.log ((2*k-1:ℕ):ℝ))^(r*a) := by ring
            _ = _ := by rw [hfac]; ring
    have hfinaltrans : ENNReal.ofReal
        ((c/(C*(2:ℝ)^b))*(2:ℝ)^(-(r-1/2)) *
          logarithmicIndexRate (r-1/2) (r*a) k) ≤
        ENNReal.ofReal ((c/(C*(2:ℝ)^b))*(q:ℝ)^(-(r-1/2)) *
          (Real.log (q:ℝ))^(r*a)) := ENNReal.ofReal_le_ofReal hrate'
    have hprod' : ENNReal.ofReal ((c/(C*(2:ℝ)^b))*(q:ℝ)^(-(r-1/2)) *
          (Real.log (q:ℝ))^(r*a)) ≤
        approximationNumber (fractionalTensorRL (fun _ : Fin d => r)
          (fun _ => hr)) k := by
      have hMminus : M-b=r := by dsimp [b]; ring
      convert hprod using 1 <;> congr 1 <;> rw [hMminus] <;>
        dsimp [a] <;> ring_nf
    have hfinal := hfinaltrans.trans hprod'
    convert hfinal using 1 <;> congr 1 <;> dsimp [a] <;> ring_nf

end BrownianSharp.AlignmentFractionalHigherOrderComposition
