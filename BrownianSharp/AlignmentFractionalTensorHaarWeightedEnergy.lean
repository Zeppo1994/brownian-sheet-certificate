import BrownianSharp.AlignmentFractionalTensorHaarEnergy
import BrownianSharp.AlignmentFractionalWeightedGrades
import Mathlib.Tactic

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalTensorHaarWeightedEnergy

open BrownianSharp
open BrownianSharp.AlignmentFractionalTensorHaar
open BrownianSharp.AlignmentFractionalTensorHaarEnergy
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalWeightedGrades

theorem scalarAxisDecay_eq_rpow_of_le_one {α : ℝ}
    (hα : 1/2 < α) (hα1 : α ≤ 1) :
    scalarAxisDecay α = Real.rpow 2 (-(2*α-1)) := by
  unfold scalarAxisDecay scalarAxisExponent
  rw [min_eq_left (by linarith : 2*α-1 ≤ 1)]
  rfl

private theorem rpow_nat_power (β : ℝ) (k : ℕ) :
    (Real.rpow 2 (-β))^k = Real.rpow 2 (-β * (k:ℝ)) := by
  calc
    (Real.rpow 2 (-β))^k = (Real.rpow 2 (-β))^(k:ℝ) := by
      rw [← Real.rpow_natCast]
    _ = Real.rpow 2 (-β * (k:ℝ)) :=
      (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-β) (k:ℝ)).symm

/-- Coordinate exponential factors are exactly the weighted active/inactive
energy exponent used by the anisotropic slab estimate. -/
theorem weightedProfile_rate_eq_rpow
    {ν e M : ℕ} (r : ℝ) (w : Fin e → ℝ)
    (a : ActiveBox ν M) (b : InactiveBox e M) :
    (∏ i : Fin ν, Real.rpow 2 (-(2*r-1)) ^ (a i).val) *
      ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1)) ^ (b j).val =
      Real.rpow 2 (-((2*r-1)*activeGradeNat a +
        inactiveEnergyExponent r w b)) := by
  have hactive :
      (∏ i : Fin ν, Real.rpow 2 (-(2*r-1)) ^ (a i).val) =
        Real.rpow 2 (-((2*r-1)*activeGradeNat a)) := by
    calc
      _ = ∏ i : Fin ν, Real.rpow 2 (-(2*r-1) * (a i).val) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact rpow_nat_power (2*r-1) (a i).val
      _ = Real.rpow 2 (∑ i : Fin ν, -(2*r-1) * (a i).val) := by
        symm
        simpa using (Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)
          (fun i : Fin ν => -(2*r-1) * (a i).val) Finset.univ)
      _ = Real.rpow 2 (-((2*r-1)*activeGradeNat a)) := by
        congr 1
        rw [activeGradeNat, Nat.cast_sum, ← Finset.mul_sum]
        ring
  have hinactive :
      (∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1)) ^ (b j).val) =
        Real.rpow 2 (-inactiveEnergyExponent r w b) := by
    calc
      _ = ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1) * (b j).val) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact rpow_nat_power (2*r*w j-1) (b j).val
      _ = Real.rpow 2 (∑ j : Fin e, -(2*r*w j-1) * (b j).val) := by
        symm
        simpa using (Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)
          (fun j : Fin e => -(2*r*w j-1) * (b j).val) Finset.univ)
      _ = Real.rpow 2 (-inactiveEnergyExponent r w b) := by
        congr 1
        rw [inactiveEnergyExponent, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  calc
    _ = Real.rpow 2 (-((2*r-1)*activeGradeNat a)) *
        Real.rpow 2 (-inactiveEnergyExponent r w b) := by rw [hactive, hinactive]
    _ = Real.rpow 2 (-((2*r-1)*activeGradeNat a + inactiveEnergyExponent r w b)) := by
      calc
        _ = Real.rpow 2 (-((2*r-1)*activeGradeNat a) +
            -inactiveEnergyExponent r w b) :=
          (Real.rpow_add (by norm_num : (0:ℝ) < 2)
            (-((2*r-1)*activeGradeNat a)) (-inactiveEnergyExponent r w b)).symm
        _ = Real.rpow 2 (-((2*r-1)*activeGradeNat a +
            inactiveEnergyExponent r w b)) := by congr 1 <;> ring

/-- For an arbitrary anisotropic fractional RL kernel, energy in a fixed
coordinatewise Haar-grade profile is bounded by the product of the actual
one-dimensional scalar grade envelopes. -/
theorem tensorHaarProfile_energy_le {d N n : ℕ}
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (t : HaarQuarter.BrownianCubeAnchor d)
    (r : Fin d → ℕ) (hr : ∑ i : Fin d, r i = n) :
    (∑ a : FiniteHaarProfileFiber (N := N) r,
      tensorHaarCoefficient α hα t a.1 ^ 2) ≤
      ∏ i : Fin d,
        scalarAxisEnvelope (α i) (hα i) * scalarAxisDecay (α i) ^ (r i) := by
  classical
  rw [tensorHaarProfile_energy_eq_product α hα t r hr]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun a ha => sq_nonneg
      (inner ℝ (kernelVector (α i) (t.val i) (hα i)
        (t.property i).1 (t.property i).2) (tensorHaarAxis a.1))
  · intro i hi
    simpa using scalarAxisGrade_decay_bound (hα i)
      (t.property i).1 (t.property i).2 N (r i)

/-- The scalar weighted-slab energy estimate remains valid after multiplying
each feature coefficient by a common product of one-dimensional envelope
constants. This is the form consumed by the actual tensor profile fibers. -/
theorem weighted_energy_slab_scaled_le
    {ν e M n : ℕ} (hν : 0 < ν) {r C : ℝ} (hr : 1/2 < r)
    (hC : 0 ≤ C) (w : Fin e → ℝ) (hw : ∀ j, 1 < w j) :
    (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
      if activeGradeNat a + inactiveFloor w b = n then
        C * Real.rpow 2 (-((2*r-1)*activeGradeNat a +
          inactiveEnergyExponent r w b)) else 0) ≤
      C * (Real.rpow 2 (-(2*r-1)*n) * ((((n+1:ℕ):ℝ)^(ν-1) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) := by
  calc
    _ = C * (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          Real.rpow 2 (-((2*r-1)*activeGradeNat a +
            inactiveEnergyExponent r w b)) else 0) := by
          symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases h : activeGradeNat a + inactiveFloor w b = n <;> simp [h]
    _ ≤ C * (Real.rpow 2 (-(2*r-1)*n) * ((((n+1:ℕ):ℝ)^(ν-1) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) := by
          apply mul_le_mul_of_nonneg_left
            (weighted_energy_slab_sum_le hν hr w hw) hC

/-- Product-form envelope energy over actual active/inactive dyadic depth
boxes is controlled by the weighted slab estimate. -/
theorem weighted_box_profile_energy_le
    {ν e M n : ℕ} (hν : 0 < ν) {r C : ℝ} (hr : 1/2 < r)
    (hC : 0 ≤ C) (w : Fin e → ℝ) (hw : ∀ j, 1 < w j) :
    (∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
      if activeGradeNat a + inactiveFloor w b = n then
        C * ((∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(a i).val) *
          ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(b j).val) else 0) ≤
      C * (Real.rpow 2 (-(2*r-1)*n) * ((((n+1:ℕ):ℝ)^(ν-1) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) := by
  calc
    _ = ∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then
          C * Real.rpow 2 (-((2*r-1)*activeGradeNat a +
            inactiveEnergyExponent r w b)) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hgrade : activeGradeNat a + inactiveFloor w b = n
          · simp only [if_pos hgrade]
            rw [weightedProfile_rate_eq_rpow]
          · simp [hgrade]
    _ ≤ C * (Real.rpow 2 (-(2*r-1)*n) * ((((n+1:ℕ):ℝ)^(ν-1) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) :=
      weighted_energy_slab_scaled_le hν hr hC w hw

/-- The same bound in subtype-sum form, for consumers that first reindex a
weighted Haar fiber by its coordinate profile. -/
theorem weighted_box_profile_subtype_energy_le
    {ν e M n : ℕ} (hν : 0 < ν) {r C : ℝ} (hr : 1/2 < r)
    (hC : 0 ≤ C) (w : Fin e → ℝ) (hw : ∀ j, 1 < w j) :
    (∑ p : {p : ActiveBox ν M × InactiveBox e M //
        weightedGradeFloor w p.1 p.2 = n},
      C * ((∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
        ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val)) ≤
      C * (Real.rpow 2 (-(2*r-1)*n) * ((((n+1:ℕ):ℝ)^(ν-1) *
        ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹))) := by
  classical
  let P : ActiveBox ν M × InactiveBox e M → Prop :=
    fun p => weightedGradeFloor w p.1 p.2 = n
  let f : ActiveBox ν M × InactiveBox e M → ℝ := fun p =>
    C * ((∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1 i).val) *
      ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.2 j).val)
  have hsum :
      (∑ p : {p : ActiveBox ν M × InactiveBox e M // P p}, f p.1) =
      ∑ b : InactiveBox e M, ∑ a : ActiveBox ν M,
        if activeGradeNat a + inactiveFloor w b = n then f (a,b) else 0 := by
    rw [← Finset.sum_subtype
      (s := Finset.univ.filter P) (h := by intro p; simp [P]) (f := f)]
    simp only [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp [P, f, weightedGradeFloor_eq_active_add_inactiveFloor w
      (fun j => le_trans (by norm_num) (le_of_lt (hw j)))]
  rw [show (∑ p : {p : ActiveBox ν M × InactiveBox e M //
      weightedGradeFloor w p.1 p.2 = n},
        C * ((∏ i : Fin ν, Real.rpow 2 (-(2*r-1))^(p.1.1 i).val) *
          ∏ j : Fin e, Real.rpow 2 (-(2*r*w j-1))^(p.1.2 j).val)) =
      ∑ p : {p : ActiveBox ν M × InactiveBox e M // P p}, f p.1 by
        rfl]
  rw [hsum]
  exact weighted_box_profile_energy_le hν hr hC w hw

end BrownianSharp.AlignmentFractionalTensorHaarWeightedEnergy
