import BrownianSharp.AlignmentPeriodicL1Fourier
import Mathlib.Analysis.Normed.Field.Basic

/-! Actual real-part Fourier coefficient and weighted-energy transfer, used
to pass from the complex inverse-Fourier source to the real Matérn field. -/
noncomputable section
open MeasureTheory UnitAddTorus
open scoped ComplexConjugate BigOperators
namespace BrownianSharp.AlignmentPaperPeriodicRealPartEnergy

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_realPart_formula {d : ℕ}
    (f : UnitAddTorus (Fin d) → ℂ)
    (hf : Integrable f (volume : Measure (UnitAddTorus (Fin d))))
    (k : Fin d → ℤ) :
    mFourierCoeff (fun x => ((f x).re : ℂ)) k =
      (mFourierCoeff f k + conj (mFourierCoeff f (-k))) / 2 := by
  have hreal : Integrable (fun x => ((f x).re : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact Complex.ofRealCLM.integrable_comp
      ((@RCLike.reCLM ℂ _).integrable_comp hf)
  have h1 : Integrable (fun x => mFourier (-k) x * f x)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hf.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have h2 : Integrable (fun x => mFourier k x * f x)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hf.bdd_smul 1 (mFourier k).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier k x‖ ≤ ‖mFourier k‖ := (mFourier k).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have h3 : Integrable (fun x => mFourier (-k) x * ((f x).re : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hreal.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have hrealFormula (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
    apply Complex.ext <;> simp <;> ring
  have hp : (fun x => mFourier (-k) x • ((f x).re : ℂ)) =
      fun x => (mFourier (-k) x * f x + conj (mFourier k x * f x)) / 2 := by
    funext x
    simp only [smul_eq_mul]
    rw [hrealFormula]
    simp only [map_mul, mFourier_neg]
    ring
  calc
    mFourierCoeff (fun x => ((f x).re : ℂ)) k =
        ∫ x, (mFourier (-k) x * f x + conj (mFourier k x * f x)) / 2 ∂
          (volume : Measure (UnitAddTorus (Fin d))) := by
      unfold mFourierCoeff
      rw [integral_congr_ae (Filter.Eventually.of_forall (congrFun hp))]
    _ = (mFourierCoeff f k + conj (mFourierCoeff f (-k))) / 2 := by
      have h2c : Integrable (fun x => conj (mFourier k x * f x))
          (volume : Measure (UnitAddTorus (Fin d))) := by
        exact h2.congr'_enorm
          (Complex.continuous_conj.comp_aestronglyMeasurable h2.1)
          (Filter.Eventually.of_forall fun x => by simp)
      have hsum : Integrable (fun x => mFourier (-k) x * f x +
          conj (mFourier k x * f x)) (volume : Measure (UnitAddTorus (Fin d))) := h1.add h2c
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_add h1 h2c, integral_conj]
      simp only [mFourierCoeff, smul_eq_mul, neg_neg, div_eq_mul_inv]

/-- Taking real parts preserves a uniform weighted coefficient-energy bound
up to a fixed factor, provided the Fourier weight is even. -/
theorem realPart_weighted_fourier_energy_le {d : ℕ}
    (f : C(UnitAddTorus (Fin d),ℂ)) (w : (Fin d → ℤ) → ℝ)
    (hw : ∀ k, 0 ≤ w k) (heven : ∀ k, w (-k)=w k)
    (B : ℝ) (henergy : ∀ S : Finset (Fin d → ℤ),
      ∑ k ∈ S, w k * ‖mFourierCoeff f k‖^2 ≤ B)
    (S : Finset (Fin d → ℤ)) :
    ∑ k ∈ S, w k * ‖mFourierCoeff (fun x => ((f x).re : ℂ)) k‖^2 ≤ 2*B := by
  have hi : Integrable f (volume : Measure (UnitAddTorus (Fin d))) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm (a b : ℂ) : ‖(a+conj b)/2‖^2 ≤ ‖a‖^2+‖b‖^2 := by
    have ht := norm_add_le a (conj b)
    simp only [norm_div, Complex.norm_conj] at ht ⊢
    norm_num
    nlinarith [norm_nonneg (a+conj b), norm_nonneg a, norm_nonneg b,
      sq_nonneg (‖a‖-‖b‖)]
  have hneg : (∑ k ∈ S, w k * ‖mFourierCoeff f (-k)‖^2) ≤ B := by
    have hsum : (∑ l ∈ S.image (fun k => -k), w l*‖mFourierCoeff f l‖^2) =
        ∑ k ∈ S, w k*‖mFourierCoeff f (-k)‖^2 := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [heven]
      · intro a ha b hb hab
        exact neg_injective hab
    rw [← hsum]
    exact henergy _
  calc
    _ ≤ ∑ k ∈ S, w k*(‖mFourierCoeff f k‖^2+‖mFourierCoeff f (-k)‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [mFourierCoeff_realPart_formula f hi k]
      exact mul_le_mul_of_nonneg_left (hnorm _ _) (hw k)
    _ = (∑ k ∈ S, w k*‖mFourierCoeff f k‖^2)+
        ∑ k ∈ S, w k*‖mFourierCoeff f (-k)‖^2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ ≤ B+B := add_le_add (henergy S) hneg
    _ = 2*B := by ring

/-- The same actual real-part bound as an ENNReal coefficient tsum, directly
compatible with the literal square-function Sobolev norm. -/
theorem realPart_weighted_fourier_tsum_le {d : ℕ}
    (f : C(UnitAddTorus (Fin d),ℂ)) (w : (Fin d → ℤ) → ℝ)
    (hw : ∀ k, 0 ≤ w k) (heven : ∀ k, w (-k)=w k)
    (B : ℝ) (henergy : ∀ S : Finset (Fin d → ℤ),
      ∑ k ∈ S, w k * ‖mFourierCoeff f k‖^2 ≤ B) :
    (∑' k : Fin d → ℤ, ENNReal.ofReal
      (w k * ‖mFourierCoeff (fun x => ((f x).re : ℂ)) k‖^2)) ≤ ENNReal.ofReal (2*B) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k hk => mul_nonneg (hw k) (sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal
    (realPart_weighted_fourier_energy_le f w hw heven B henergy S)

end BrownianSharp.AlignmentPaperPeriodicRealPartEnergy
