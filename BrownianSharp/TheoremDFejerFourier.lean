import BrownianSharp.TheoremDFejerSampling
import BrownianSharp.FourierExtractionCoefficient
import BrownianSharp.TrigonometricHaarExtraction
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

namespace HaarQuarter.TheoremD.FejerFourier

open HaarQuarter.FourierExtractionKernel

private theorem normSq_finset_sum_expand {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (Complex.normSq (∑ i ∈ s, f i) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, star (f i) * f j := by
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
  simp only [starRingEnd_apply]

noncomputable def fejerFourierPolynomial (N : ℕ) : UnitAddCircle → ℂ := fun x =>
  (N : ℂ)⁻¹ * ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
    fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x

noncomputable def deLaValleePoussinPolynomial (N : ℕ) : UnitAddCircle → ℂ :=
  fun x => 2 * fejerFourierPolynomial (2 * N) x - fejerFourierPolynomial N x

noncomputable def realFejerKernel (N : ℕ) (x : ℝ) : ℝ :=
  Complex.normSq (∑ r ∈ Finset.range N,
    HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x) / N

noncomputable def realDeLaValleePoussinKernel (N : ℕ) (x : ℝ) : ℝ :=
  2 * realFejerKernel (2 * N) x - realFejerKernel N x

private theorem fourier_mode_integrable (n : ℤ) :
    Integrable (fun x : UnitAddCircle => fourier (T := (1 : ℝ)) n x)
      (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
  have hc : Continuous (fun x : UnitAddCircle => fourier (T := (1 : ℝ)) n x) := by fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem fejerFourierPolynomial_integrable (N : ℕ) :
    Integrable (fejerFourierPolynomial N)
      (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
  have hc : Continuous (fejerFourierPolynomial N) := by
    unfold fejerFourierPolynomial
    fun_prop
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem fourierCoeff_single_mode (a q : ℤ) :
    fourierCoeff (T := (1 : ℝ)) (fourier (T := (1 : ℝ)) a) q =
      if q = a then (1 : ℂ) else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) a) q
  simpa [Pi.single_apply] using h

private theorem fourierCoeff_inner_sum (N r q : ℕ) :
    fourierCoeff (T := (1 : ℝ))
      (fun x : UnitAddCircle => ∑ s ∈ Finset.range N,
        fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) (q : ℤ) =
      ∑ s ∈ Finset.range N,
        (if (q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℂ) else 0) := by
  have hterm (s : ℕ) (hs : s ∈ Finset.range N) :
      Integrable (fun x : UnitAddCircle => fourier (T := (1 : ℝ))
        ((s : ℤ) - (r : ℤ)) x) (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    fourier_mode_integrable _
  have hsum := fourierCoeff.sum (T := (1 : ℝ)) (Finset.range N)
    (fun s x => fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) hterm
  have hpoint (s : ℕ) (hs : s ∈ Finset.range N) :
      fourierCoeff (T := (1 : ℝ))
        (fun x : UnitAddCircle => fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) (q : ℤ) =
        if (q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℂ) else 0 := by
    change fourierCoeff (T := (1 : ℝ))
      (fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ))) (q : ℤ) = _
    simpa using fourierCoeff_single_mode ((s : ℤ) - (r : ℤ)) (q : ℤ)
  have hfunc :
      (fun x : UnitAddCircle => ∑ s ∈ Finset.range N,
        fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) =
      ∑ s ∈ Finset.range N,
        (fun x : UnitAddCircle => fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) := by
    funext x
    simp
  rw [hfunc, hsum]
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s hs
  exact hpoint s hs

private theorem mode_count_signed (N q : ℕ) (hq : q ≤ N) :
    (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
      (if (q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℝ) else 0)) =
      ((N - q : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  have hcond (s r : ℕ) :
      ((q : ℤ) = (s : ℤ) - (r : ℤ)) ↔
        (r : ℤ) - (s : ℤ) = -(q : ℤ) := by omega
  simp_rw [hcond]
  exact HaarQuarter.TheoremD.Fejer.mode_difference_count_neg N q hq

private theorem mode_count_signed_neg (N q : ℕ) (hq : q ≤ N) :
    (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
      (if -(q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℝ) else 0)) =
      ((N - q : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  have hcond (s r : ℕ) :
      (-(q : ℤ) = (s : ℤ) - (r : ℤ)) ↔
        (r : ℤ) - (s : ℤ) = (q : ℤ) := by omega
  simp_rw [hcond]
  exact HaarQuarter.TheoremD.Fejer.mode_difference_count N q hq

private theorem fejerFourierPolynomial_fourierCoeff_count (N q : ℕ) :
    fourierCoeff (T := (1 : ℝ)) (fejerFourierPolynomial N) (q : ℤ) =
      (N : ℂ)⁻¹ * ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        (if (q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℂ) else 0) := by
  let f : ℕ → UnitAddCircle → ℂ := fun r x =>
    ∑ s ∈ Finset.range N, fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x
  have hf (r : ℕ) : Integrable (f r) (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    dsimp [f]
    apply integrable_finset_sum
    intro s hs
    exact fourier_mode_integrable _
  have hsum := fourierCoeff.sum (T := (1 : ℝ)) (Finset.range N) f
    (fun r hr => hf r)
  rw [show fejerFourierPolynomial N = (N : ℂ)⁻¹ • ∑ r ∈ Finset.range N, f r by
    funext x
    simp [fejerFourierPolynomial, f, smul_eq_mul]]
  rw [fourierCoeff.const_smul, hsum]
  rw [Finset.sum_apply]
  apply congrArg (fun z : ℂ => (N : ℂ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro r hr
  simpa [f] using fourierCoeff_inner_sum N r q

private theorem fejerFourierPolynomial_fourierCoeff_count_neg (N q : ℕ) :
    fourierCoeff (T := (1 : ℝ)) (fejerFourierPolynomial N) (-(q : ℤ)) =
      (N : ℂ)⁻¹ * ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        (if -(q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℂ) else 0) := by
  let f : ℕ → UnitAddCircle → ℂ := fun r x =>
    ∑ s ∈ Finset.range N, fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x
  have hf (r : ℕ) : Integrable (f r) (AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    dsimp [f]
    apply integrable_finset_sum
    intro s hs
    exact fourier_mode_integrable _
  have hsum := fourierCoeff.sum (T := (1 : ℝ)) (Finset.range N) f
    (fun r hr => hf r)
  rw [show fejerFourierPolynomial N = (N : ℂ)⁻¹ • ∑ r ∈ Finset.range N, f r by
    funext x
    simp [fejerFourierPolynomial, f, smul_eq_mul]]
  rw [fourierCoeff.const_smul, hsum]
  rw [Finset.sum_apply]
  apply congrArg (fun z : ℂ => (N : ℂ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro r hr
  have hinner := fourierCoeff.sum (T := (1 : ℝ)) (Finset.range N)
    (fun s x => fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x)
    (fun s hs => fourier_mode_integrable _)
  have hfunc :
      (fun x : UnitAddCircle => ∑ s ∈ Finset.range N,
        fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) =
      ∑ s ∈ Finset.range N,
        (fun x : UnitAddCircle => fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) := by
    funext x
    simp
  change fourierCoeff (T := (1 : ℝ))
    (fun x : UnitAddCircle => ∑ s ∈ Finset.range N,
      fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) x) (-(q : ℤ)) = _
  rw [hfunc, hinner, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro s hs
  change fourierCoeff (T := (1 : ℝ))
    (fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ))) (-(q : ℤ)) = _
  simpa using fourierCoeff_single_mode ((s : ℤ) - (r : ℤ)) (-(q : ℤ))

theorem fejerFourierPolynomial_fourierCoeff_nat (N q : ℕ) (hN : 0 < N)
    (hq : q ≤ N) :
    fourierCoeff (T := (1 : ℝ)) (fejerFourierPolynomial N) (q : ℤ) =
      ((N - q : ℕ) : ℂ) / (N : ℂ) := by
  rw [fejerFourierPolynomial_fourierCoeff_count]
  have hcountR :
      (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        (if (q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℝ) else 0)) =
          ((N - q : ℕ) : ℝ) := mode_count_signed N q hq
  have hcountC :
      (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        (if (q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℂ) else 0)) =
          ((N - q : ℕ) : ℂ) := by exact_mod_cast hcountR
  rw [hcountC]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem fejerFourierPolynomial_fourierCoeff_neg_nat (N q : ℕ) (hN : 0 < N)
    (hq : q ≤ N) :
    fourierCoeff (T := (1 : ℝ)) (fejerFourierPolynomial N) (-(q : ℤ)) =
      ((N - q : ℕ) : ℂ) / (N : ℂ) := by
  rw [fejerFourierPolynomial_fourierCoeff_count_neg]
  have hcountR :
      (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        (if -(q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℝ) else 0)) =
          ((N - q : ℕ) : ℝ) := mode_count_signed_neg N q hq
  have hcountC :
      (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        (if -(q : ℤ) = (s : ℤ) - (r : ℤ) then (1 : ℂ) else 0)) =
          ((N - q : ℕ) : ℂ) := by exact_mod_cast hcountR
  rw [hcountC]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

private theorem character_frequency_add (k l : ℤ) (x : ℝ) :
    HaarQuarter.TrigonometricHaarExtraction.character (k + l) x =
      HaarQuarter.TrigonometricHaarExtraction.character k x *
        HaarQuarter.TrigonometricHaarExtraction.character l x := by
  unfold HaarQuarter.TrigonometricHaarExtraction.character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem character_star (k : ℤ) (x : ℝ) :
    star (HaarQuarter.TrigonometricHaarExtraction.character k x) =
      HaarQuarter.TrigonometricHaarExtraction.character (-k) x := by
  unfold HaarQuarter.TrigonometricHaarExtraction.character
  change (starRingEnd ℂ) (Complex.exp ((2 * Real.pi * (k : ℝ) * x) * Complex.I)) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, map_intCast, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem fejerFourierPolynomial_eval (N : ℕ) (x : ℝ) :
    fejerFourierPolynomial N (x : UnitAddCircle) =
      (N : ℂ)⁻¹ * Complex.normSq
        (∑ r ∈ Finset.range N,
          HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x) := by
  have hchar (r : ℤ) :
      fourier (T := (1 : ℝ)) r (x : UnitAddCircle) =
        HaarQuarter.TrigonometricHaarExtraction.character r x := by
    simpa [HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter] using
      HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter_coe r x
  have hprod (r s : ℕ) :
      star (HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x) *
          HaarQuarter.TrigonometricHaarExtraction.character (s : ℤ) x =
        HaarQuarter.TrigonometricHaarExtraction.character ((s : ℤ) - (r : ℤ)) x := by
    rw [character_star, ← character_frequency_add]
    congr 1
    omega
  change (N : ℂ)⁻¹ *
      (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        fourier (T := (1 : ℝ)) ((s : ℤ) - (r : ℤ)) (x : UnitAddCircle)) = _
  rw [normSq_finset_sum_expand]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [hchar ((s : ℤ) - (r : ℤ))]
  exact (hprod r s).symm

theorem fejerFourierPolynomial_eval_eq_real (N : ℕ) (x : ℝ) :
    fejerFourierPolynomial N (x : UnitAddCircle) =
      (realFejerKernel N x : ℂ) := by
  rw [fejerFourierPolynomial_eval]
  simp only [realFejerKernel]
  by_cases hN0 : N = 0
  · subst N
    simp
  · have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hN0
    push_cast
    field_simp

noncomputable def deLaValleePoussinCircleKernel (N : ℕ) : C(UnitAddCircle, ℂ) :=
  ⟨deLaValleePoussinPolynomial N, by
    unfold deLaValleePoussinPolynomial fejerFourierPolynomial
    fun_prop⟩

theorem deLaValleePoussinCircleKernel_eval_eq_real (N : ℕ) (x : ℝ) :
    deLaValleePoussinCircleKernel N (x : UnitAddCircle) =
      (realDeLaValleePoussinKernel N x : ℂ) := by
  change deLaValleePoussinPolynomial N (x : UnitAddCircle) = _
  rw [deLaValleePoussinPolynomial]
  rw [fejerFourierPolynomial_eval_eq_real (2 * N) x,
    fejerFourierPolynomial_eval_eq_real N x]
  simp [realDeLaValleePoussinKernel]

theorem shifted_midpoint_character_eq_real (N r j : ℕ) (t : ℝ) :
    HaarQuarter.TheoremD.Fejer.shiftedMidpointCharacter N r j t =
      HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ)
        (((j : ℝ) + 1 / 2) / N - t) := by
  unfold HaarQuarter.TheoremD.Fejer.shiftedMidpointCharacter
    HaarQuarter.TheoremD.Fejer.midpointPhaseShift
    HaarQuarter.TheoremD.Fejer.midpointCharacter
    HaarQuarter.TheoremD.Fejer.midpointPhase
    HaarQuarter.TrigonometricHaarExtraction.character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realDeLaValleePoussin_grid_average_abs_le_five (N : ℕ) (t : ℝ)
    (hN : 0 < N) :
    (∑ j ∈ Finset.range N,
      |realDeLaValleePoussinKernel N (((j : ℝ) + 1 / 2) / N - t)|) / N ≤ 5 := by
  have hkernel (L : ℕ) (j : ℕ) :
      realFejerKernel L (((j : ℝ) + 1 / 2) / N - t) =
        Complex.normSq (∑ r ∈ Finset.range L,
          HaarQuarter.TheoremD.Fejer.shiftedMidpointCharacter N r j t) / L := by
    unfold realFejerKernel
    congr 1
    apply congrArg Complex.normSq
    apply Finset.sum_congr rfl
    intro r hr
    rw [shifted_midpoint_character_eq_real]
  have hmass := HaarQuarter.TheoremD.Fejer.shifted_v_fejer_average_abs_le_five N t hN
  convert hmass using 1
  apply congrArg (fun x : ℝ => x / N)
  apply Finset.sum_congr rfl
  intro j hj
  rw [realDeLaValleePoussinKernel, hkernel, hkernel]
  norm_num

theorem deLaValleePoussin_fourierCoeff_nat (N q : ℕ) (hN : 0 < N)
    (hq : q ≤ N) :
    fourierCoeff (T := (1 : ℝ)) (deLaValleePoussinPolynomial N) (q : ℤ) = 1 := by
  have hN2 : 0 < 2 * N := by omega
  have hq2 : q ≤ 2 * N := by omega
  change fourierCoeff (T := (1 : ℝ))
    (fun x => 2 * fejerFourierPolynomial (2 * N) x - fejerFourierPolynomial N x)
    (q : ℤ) = 1
  rw [show (fun x => 2 * fejerFourierPolynomial (2 * N) x - fejerFourierPolynomial N x) =
    (fun x => (2 : ℂ) * fejerFourierPolynomial (2 * N) x) +
      (fun x => (-1 : ℂ) * fejerFourierPolynomial N x) by
        funext x
        simp [sub_eq_add_neg]]
  rw [fourierCoeff.add
      ((fejerFourierPolynomial_integrable (2 * N)).const_mul (2 : ℂ))
      ((fejerFourierPolynomial_integrable N).const_mul (-1 : ℂ))]
  simp only [Pi.add_apply, fourierCoeff.const_mul]
  rw [
    fejerFourierPolynomial_fourierCoeff_nat (2 * N) q hN2 hq2,
    fejerFourierPolynomial_fourierCoeff_nat N q hN hq]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsub : 2 * N - q = N + (N - q) := by omega
  rw [hsub, Nat.cast_add, Nat.cast_sub hq]
  field_simp
  push_cast
  ring

theorem deLaValleePoussin_fourierCoeff_neg_nat (N q : ℕ) (hN : 0 < N)
    (hq : q ≤ N) :
    fourierCoeff (T := (1 : ℝ)) (deLaValleePoussinPolynomial N) (-(q : ℤ)) = 1 := by
  have hN2 : 0 < 2 * N := by omega
  have hq2 : q ≤ 2 * N := by omega
  change fourierCoeff (T := (1 : ℝ))
    (fun x => 2 * fejerFourierPolynomial (2 * N) x - fejerFourierPolynomial N x)
    (-(q : ℤ)) = 1
  rw [show (fun x => 2 * fejerFourierPolynomial (2 * N) x - fejerFourierPolynomial N x) =
    (fun x => (2 : ℂ) * fejerFourierPolynomial (2 * N) x) +
      (fun x => (-1 : ℂ) * fejerFourierPolynomial N x) by
        funext x
        simp [sub_eq_add_neg]]
  rw [fourierCoeff.add
      ((fejerFourierPolynomial_integrable (2 * N)).const_mul (2 : ℂ))
      ((fejerFourierPolynomial_integrable N).const_mul (-1 : ℂ))]
  simp only [Pi.add_apply, fourierCoeff.const_mul]
  rw [
    fejerFourierPolynomial_fourierCoeff_neg_nat (2 * N) q hN2 hq2,
    fejerFourierPolynomial_fourierCoeff_neg_nat N q hN hq]
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsub : 2 * N - q = N + (N - q) := by omega
  rw [hsub, Nat.cast_add, Nat.cast_sub hq]
  field_simp
  push_cast
  ring

theorem deLaValleePoussinCircleKernel_fourierCoeff_of_natAbs_le
    (N : ℕ) (hN : 0 < N) (n : ℤ) (hn : n.natAbs ≤ N) :
    fourierCoeff (T := (1 : ℝ)) (deLaValleePoussinCircleKernel N) n = 1 := by
  cases n with
  | ofNat q =>
      change fourierCoeff (T := (1 : ℝ)) (deLaValleePoussinPolynomial N) (q : ℤ) = 1
      exact deLaValleePoussin_fourierCoeff_nat N q hN hn
  | negSucc q =>
      have hq : q + 1 ≤ N := by simpa using hn
      change fourierCoeff (T := (1 : ℝ))
        (deLaValleePoussinPolynomial N) (-(q + 1 : ℕ) : ℤ) = 1
      simpa using deLaValleePoussin_fourierCoeff_neg_nat N (q + 1) hN hq

theorem deLaValleePoussinCircleKernel_reproduces_bandlimited_polynomial
    (N : ℕ) (hN : 0 < N) (s : Finset ℤ) (a : ℤ → ℂ)
    (hband : ∀ n ∈ s, n.natAbs ≤ N) (x : UnitAddCircle) :
    circleConvolution (deLaValleePoussinCircleKernel N)
        (finiteCircleFourierPolynomial s a) x =
      finiteCircleFourierPolynomial s a x := by
  rw [circleConvolution_finiteFourierPolynomial]
  calc
    (∑ n ∈ s, (a n * fourierCoeff (deLaValleePoussinCircleKernel N) n) * fourier n x) =
        ∑ n ∈ s, a n * fourier n x := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [deLaValleePoussinCircleKernel_fourierCoeff_of_natAbs_le N hN n
            (hband n hn)]
          ring
    _ = finiteCircleFourierPolynomial s a x := by
          simp [finiteCircleFourierPolynomial, ContinuousMap.sum_apply,
            ContinuousMap.smul_apply, smul_eq_mul]

end HaarQuarter.TheoremD.FejerFourier
