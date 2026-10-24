import BrownianSharp.FiniteHaarGeometry
import BrownianSharp.CameronMartin
import BrownianSharp.LayerIndex

/-! Bounds for endpoint-feature energy in finite mixed father/mother Haar layers. -/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace BrownianSharp
open HaarQuarter

private theorem sum_pow_two_fin (N : ℕ) :
    (∑ r : Fin N, (2 : ℕ) ^ r.val) = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero]
      simp only [Fin.val_succ]
      have hs : (∑ x : Fin N, (2 : ℕ) ^ (x.val + 1)) =
          (∑ x : Fin N, (2 : ℕ) ^ x.val) * 2 := by
        simp_rw [pow_succ]
        rw [Finset.sum_mul]
      rw [hs, ih]
      have hp : (2 : ℕ) ^ (N + 1) = 2 ^ N * 2 := by rw [pow_succ]
      rw [hp]
      let x : ℕ := 2 ^ N
      have hx : 1 ≤ x := by dsimp [x]; exact Nat.one_le_two_pow
      change 1 + (x - 1) * 2 = x * 2 - 1
      omega

theorem finiteHaarAxis_card (N : ℕ) : Fintype.card (FiniteHaarAxis N) = 2 ^ N := by
  classical
  change Fintype.card (Option (Σ r : Fin N, Fin (2 ^ r.val))) = 2 ^ N
  rw [Fintype.card_option, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [sum_pow_two_fin]
  have hp : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  exact Nat.sub_add_cancel hp

theorem finiteHaarIndex_card (d N : ℕ) :
    Fintype.card (FiniteHaarIndex d N) = 2 ^ (N * d) := by
  classical
  change Fintype.card (Fin d → FiniteHaarAxis N) = 2 ^ (N * d)
  rw [Fintype.card_pi]
  calc
    (∏ i : Fin d, Fintype.card (FiniteHaarAxis N)) =
        ∏ i : Fin d, (2 : ℕ) ^ N := by
          apply Finset.prod_congr rfl
          intro i hi
          exact finiteHaarAxis_card N
    _ = (2 ^ N) ^ d := by simp
    _ = 2 ^ (N * d) := by rw [pow_mul]

/-- A fixed shifted-grade profile, with the address cells left free. -/
abbrev FiniteHaarProfileFiber {d N : ℕ} (r : Fin d → ℕ) :=
  {a : FiniteHaarIndex d N // ∀ i, finiteHaarAxisGrade (a i) = r i}

noncomputable def finiteHaarGridCoefficient {d N : ℕ}
    (a : FiniteHaarIndex d N) (t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) : ℝ :=
  ⟪finiteHaarVector a,
    (⟨brownianSheetBoxIndicatorLp t,
      brownianCubeBoxIndicator_mem ⟨t, fun i => ⟨(ht i).1, (ht i).2⟩⟩⟩ :
      brownianCubeBoxSpan d)⟫

noncomputable def finiteHaarAxisPointFeature {N : ℕ}
    (a : FiniteHaarAxis N) (t : ℝ) : ℝ :=
  match a with
  | none => t
  | some ⟨s, j⟩ => Real.sqrt 2 ^ s.val * dyadicHaarTentAt s.val j.val t

private theorem dyadicHaar_interiors_disjoint {r j k : ℕ} {t : ℝ}
    (hjk : j ≠ k)
    (hj : dyadicHaarLeft r j < t ∧ t < dyadicHaarRight r j)
    (hk : dyadicHaarLeft r k < t ∧ t < dyadicHaarRight r k) : False := by
  rcases lt_or_gt_of_ne hjk with hjk' | hkj'
  · have hsep : dyadicHaarRight r j ≤ dyadicHaarLeft r k := by
      unfold dyadicHaarRight dyadicHaarLeft
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ r)).2
      exact_mod_cast Nat.succ_le_of_lt hjk'
    linarith
  · have hsep : dyadicHaarRight r k ≤ dyadicHaarLeft r j := by
      unfold dyadicHaarRight dyadicHaarLeft
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ r)).2
      exact_mod_cast Nat.succ_le_of_lt hkj'
    linarith

private theorem finiteHaarProfile_coeff_unique {d N : ℕ}
    (r : Fin d → ℕ) (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1)
    (a b : FiniteHaarProfileFiber (N := N) r)
    (ha : finiteHaarGridCoefficient a.1 t ht ≠ 0)
    (hb : finiteHaarGridCoefficient b.1 t ht ≠ 0) : a = b := by
  apply Subtype.ext
  funext i
  have hprodA : ∏ i : Fin d, (match a.1 i with
      | none => t i
      | some ⟨s, j⟩ => Real.sqrt 2 ^ s.val * dyadicHaarTentAt s.val j.val (t i)) ≠ 0 := by
    unfold finiteHaarGridCoefficient at ha
    rw [finiteHaarVector_inner_box_eq_product_feature a.1 t ht] at ha
    exact ha
  have hprodB : ∏ i : Fin d, (match b.1 i with
      | none => t i
      | some ⟨s, j⟩ => Real.sqrt 2 ^ s.val * dyadicHaarTentAt s.val j.val (t i)) ≠ 0 := by
    unfold finiteHaarGridCoefficient at hb
    rw [finiteHaarVector_inner_box_eq_product_feature b.1 t ht] at hb
    exact hb
  have hAi : (match a.1 i with
      | none => t i
      | some ⟨s, j⟩ => Real.sqrt 2 ^ s.val * dyadicHaarTentAt s.val j.val (t i)) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprodA) i (Finset.mem_univ i)
  have hBi : (match b.1 i with
      | none => t i
      | some ⟨s, j⟩ => Real.sqrt 2 ^ s.val * dyadicHaarTentAt s.val j.val (t i)) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprodB) i (Finset.mem_univ i)
  have hri := a.2 i
  have hsi := b.2 i
  cases haAxis : a.1 i with
  | none =>
      have hr : r i = 0 := by simpa [haAxis, finiteHaarAxisGrade] using hri.symm
      have hbNone : b.1 i = none := by
        cases hcase : b.1 i with
        | none => rfl
        | some x =>
            have : finiteHaarAxisGrade (b.1 i) = 0 := by rw [hsi, hr]
            simp [hcase, finiteHaarAxisGrade] at this
      simpa [hbNone]
  | some ax =>
      rcases ax with ⟨s, j⟩
      have hr : s.val + 1 = r i := by
        simpa [haAxis, finiteHaarAxisGrade] using hri
      cases hbAxis : b.1 i with
      | none =>
          simp [hbAxis, finiteHaarAxisGrade] at hsi
          omega
      | some bx =>
          rcases bx with ⟨u, k⟩
          have hu : u.val = s.val := by
            have hh : u.val + 1 = r i := by
              simpa [hbAxis, finiteHaarAxisGrade] using hsi
            omega
          have htenA : dyadicHaarTentAt s.val j.val (t i) ≠ 0 := by
            have : Real.sqrt 2 ^ s.val * dyadicHaarTentAt s.val j.val (t i) ≠ 0 := by
              simpa [haAxis] using hAi
            exact (mul_ne_zero_iff.mp this).2
          have htenB0 : dyadicHaarTentAt u.val k.val (t i) ≠ 0 := by
            have : Real.sqrt 2 ^ u.val * dyadicHaarTentAt u.val k.val (t i) ≠ 0 := by
              simpa [hbAxis] using hBi
            have hsqrt : Real.sqrt 2 ^ u.val ≠ 0 := by positivity
            have hmul := (mul_ne_zero_iff.mp this).2
            exact hmul
          have htenB : dyadicHaarTentAt s.val k.val (t i) ≠ 0 := by
            simpa [hu] using htenB0
          have hs : s = u := Fin.ext hu.symm
          subst u
          have hposA : 0 < dyadicHaarTentAt s.val j.val (t i) := by
            have hnonneg := (dyadicHaarTentAt_bounds (t i) j.isLt).1
            rcases lt_or_gt_of_ne htenA with hlt | hgt
            · exact False.elim (htenA (by linarith))
            · exact hgt
          have hposB0 : 0 < dyadicHaarTentAt s.val k.val (t i) := by
            have hnonneg := (dyadicHaarTentAt_bounds (t i) k.isLt).1
            rcases lt_or_gt_of_ne htenB with hlt | hgt
            · exact False.elim (htenB (by linarith [hnonneg]))
            · exact hgt
          have hk : k.val < 2 ^ s.val := k.isLt
          have hintervalA := (dyadicHaarTentAt_pos_iff (t := t i) j.isLt).mp hposA
          have hintervalB := (dyadicHaarTentAt_pos_iff (t := t i) hk).mp hposB0
          have hjk : j.val = k.val := by
            by_contra hne
            exact dyadicHaar_interiors_disjoint (by omega) hintervalA hintervalB
          have hj : j = k := Fin.ext hjk
          subst k
          rfl

/-- For each fixed shifted-depth profile, disjoint dyadic tent interiors imply
that at most one address tuple has nonzero feature coefficient. Hence its
total squared endpoint-feature energy is bounded by the single-coefficient
bound `2^-sum(profile)`. -/
theorem finiteHaarProfile_grid_energy_le {d N : ℕ}
    (r : Fin d → ℕ) (t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    (∑ a : FiniteHaarProfileFiber (N := N) r,
      finiteHaarGridCoefficient a.1 t ht ^ 2) ≤
      1 / (2 : ℝ) ^ (∑ i : Fin d, r i) := by
  classical
  let f : FiniteHaarProfileFiber (N := N) r → ℝ :=
    fun a => finiteHaarGridCoefficient a.1 t ht ^ 2
  by_cases hex : ∃ a, f a ≠ 0
  · obtain ⟨a, ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · have hgrade : finiteHaarGrade a.1 = ∑ i : Fin d, r i := by
        simp only [finiteHaarGrade]
        apply Finset.sum_congr rfl
        intro i hi
        exact a.2 i
      simpa [f, finiteHaarGridCoefficient, hgrade] using
        finiteHaarVector_box_inner_sq_le a.1 t ht
    · intro b hb hba
      have hzero : f b = 0 := by
        by_contra hn
        have hEq := finiteHaarProfile_coeff_unique r t ht a b
          (by simpa [f] using ha) (by simpa [f] using hn)
        exact hba hEq.symm
      exact hzero
    · intro hmem
      exact (hmem (Finset.mem_univ a)).elim
  · have hz : ∀ a : FiniteHaarProfileFiber (N := N) r, f a = 0 := by
      intro a
      by_contra hn
      exact hex ⟨a, hn⟩
    simp [f, hz]

end BrownianSharp
