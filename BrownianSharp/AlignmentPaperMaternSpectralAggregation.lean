import BrownianSharp.AlignmentPaperMaternSpectralApproximation
import BrownianSharp.AlignmentPaperMaternSpectralApproximationPartition
import BrownianSharp.AlignmentMaternScalarFeature
import BrownianSharp.AlignmentMaternContinuousFeature
import Mathlib.Algebra.Field.GeomSum
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Quantitative summation lemmas for the genuine finite-cell Matérn
spectral residual. This leaf is separate from the level-space construction. -/

noncomputable section
open MeasureTheory
open scoped ENNReal Topology RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMaternSpectralAggregation

/-- A finite geometric sum is bounded by the full geometric sum. -/
theorem finite_geometric_sum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, r^k) ≤ (1-r)⁻¹ := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, r^k :=
    Finset.sum_nonneg fun k hk => pow_nonneg hr0 k
  have hgeom := geom_sum_mul_of_le_one hr1.le n
  have hmul : (∑ k ∈ Finset.range n, r^k) * (1-r) = 1-r^n := by
    simpa [mul_comm] using hgeom
  have hnum : 1-r^n ≤ 1 := by nlinarith [pow_nonneg hr0 n]
  have hden : 0 < 1-r := by linarith
  rw [← one_div]
  exact (le_div_iff₀ hden).2 (by rw [hmul]; exact hnum)

/-- The mesh-width errors over the dyadic bands have a uniformly bounded
geometric sum whenever the Taylor order is strictly larger than `2h`. -/
theorem dyadicBandTaylorEnergySum_le (h : ℝ) (q N : ℕ)
    (hq : 2*h < (q:ℝ)) :
    (∑ j ∈ Finset.range (N+1),
      Real.rpow 2 (-2*(q:ℝ)*(((N-j)/2:ℕ):ℝ) - 2*h*(j:ℕ))) ≤
      Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) *
        (1 - Real.rpow 2 (-(q:ℝ)+2*h))⁻¹ := by
  let ρ : ℝ := Real.rpow 2 (-(q:ℝ)+2*h)
  have hρ0 : 0 ≤ ρ := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2)
    linarith
  have hgeom := finite_geometric_sum_le_inv hρ0 hρ1 (N+1)
  have hterm : ∀ j ∈ Finset.range (N+1),
      Real.rpow 2 (-2*(q:ℝ)*(((N-j)/2:ℕ):ℝ) - 2*h*(j:ℕ)) ≤
        Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) * ρ^(N-j) := by
    intro j hj
    have hjN : j ≤ N := by simp only [Finset.mem_range] at hj; omega
    let k : ℕ := N-j
    let m : ℕ := (N-j)/2
    have hfloorNat : k ≤ 2*m+1 := by dsimp [k,m]; omega
    have hfloor : (k:ℝ)-1 ≤ 2*(m:ℝ) := by
      have hc : (k:ℝ) ≤ 2*(m:ℝ)+1 := by exact_mod_cast hfloorNat
      linarith
    have hq0 : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
    have hN : (N:ℝ) = (k:ℝ)+(j:ℝ) := by
      dsimp [k]
      exact_mod_cast (Nat.sub_add_cancel hjN).symm
    have hexp : -2*(q:ℝ)*(m:ℝ)-2*h*(j:ℕ) ≤
        (q:ℝ)-2*h*(N:ℕ)-((q:ℝ)-2*h)*(k:ℕ) := by
      rw [hN]
      nlinarith [mul_nonneg hq0 (by linarith [hfloor] : 0 ≤ 2*(m:ℝ)-((k:ℝ)-1))]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 2) hexp
    have hrho : ρ^(N-j) = Real.rpow 2 ((-(q:ℝ)+2*h)*(k:ℝ)) := by
      dsimp [ρ, k]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hproduct : Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) * ρ^(N-j) =
        Real.rpow 2 ((q:ℝ)-2*h*(N:ℕ)-((q:ℝ)-2*h)*(k:ℕ)) := by
      rw [hrho]
      calc
        Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) *
            Real.rpow 2 ((-(q:ℝ)+2*h)*(k:ℝ)) =
          Real.rpow 2 ((q:ℝ)+(-2*h*(N:ℕ))) *
            Real.rpow 2 ((-(q:ℝ)+2*h)*(k:ℝ)) := by
              exact congrArg (fun x : ℝ => x * Real.rpow 2 ((-(q:ℝ)+2*h)*(k:ℝ)))
                ((Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm)
        _ = Real.rpow 2 (((q:ℝ)+(-2*h*(N:ℕ))) + (-(q:ℝ)+2*h)*(k:ℝ)) :=
              (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
        _ = Real.rpow 2 ((q:ℝ)-2*h*(N:ℕ)-((q:ℝ)-2*h)*(k:ℕ)) := by
              congr 1
              rw [hN]
              ring
    rw [hproduct]
    exact hpow
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1),
        Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) * ρ^(N-j) :=
      Finset.sum_le_sum fun j hj => hterm j hj
    _ = Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) *
        ∑ j ∈ Finset.range (N+1), ρ^(N-j) := by
      let C := Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ))
      change (∑ j ∈ Finset.range (N+1), C * ρ^(N-j)) = C * _
      rw [← Finset.mul_sum]
    _ = Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) *
        ∑ k ∈ Finset.range (N+1), ρ^k := by
      congr 1
      simpa using (Finset.sum_range_reflect (fun k => ρ^k) (N+1))
    _ ≤ Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) * (1-ρ)⁻¹ := by
      have hc : 0 ≤ Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℕ)) :=
        mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
          (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      have hden : 0 < 1-ρ := by linarith
      exact mul_le_mul_of_nonneg_left hgeom hc
    _ = _ := by simp [ρ]

open BrownianSharp.AlignmentPaperMaternSpectralApproximation
open BrownianSharp.AlignmentPaperMaternSpectralApproximationPartition
open BrownianSharp.AlignmentMaternScalarFeature
open BrownianSharp.AlignmentMaternSpectralFeature

/-- The actual residual on one finite frequency cell. -/
def levelCellErrorVec (κ h t : ℝ) (N q : ℕ) (a : spectralLevelCellIndex N)
    (hκ : 0 < κ) (hh : 0 < h) : SpectralAxisL2 κ h := by
  let I := spectralLevelCellInterval N a
  exact scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh -
    spectralCellTaylorApproxL2 κ h t I.1 I.2 q hκ hh
      (spectralLevelCellInterval_order N a)

/-- The omitted high-frequency part is the scalar feature restricted to the
complement of the exact finite union of Taylor cells. -/
def spectralLevelTailSet (N : ℕ) : Set ℝ :=
  (Set.Ico (-((2:ℝ)^(N+1))) ((2:ℝ)^(N+1)))ᶜ

noncomputable def spectralLevelTailL2 (κ h t : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) : SpectralAxisL2 κ h :=
  ((scalarPhaseMemLp κ h t hκ hh).indicator
    ((measurableSet_Ico.compl))).toLp
      ((spectralLevelTailSet N).indicator (scalarPhase t))

theorem levelCellErrorVec_coeFn (κ h t : ℝ) (N q : ℕ)
    (a : spectralLevelCellIndex N) (hκ : 0 < κ) (hh : 0 < h) :
    (levelCellErrorVec κ h t N q a hκ hh : ℝ → ℝ) =ᵐ[spectralMeasure κ h]
      scalarCellTaylorErrorFunction t (spectralLevelCellInterval N a).1
        (spectralLevelCellInterval N a).2 q := by
  let I := spectralLevelCellInterval N a
  have hK := scalarCellFeatureRestrictedL2_coeFn κ h t I.1 I.2 hκ hh
  have hA := spectralCellTaylorApproxL2_coeFn κ h t I.1 I.2 q hκ hh
    (spectralLevelCellInterval_order N a)
  filter_upwards [Lp.coeFn_sub
    (scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh)
    (spectralCellTaylorApproxL2 κ h t I.1 I.2 q hκ hh
      (spectralLevelCellInterval_order N a)), hK, hA] with ξ hsub hk ha
  change ((scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh -
      spectralCellTaylorApproxL2 κ h t I.1 I.2 q hκ hh
        (spectralLevelCellInterval_order N a) : SpectralAxisL2 κ h) : ℝ → ℝ) ξ = _
  rw [hsub, Pi.sub_apply, hk, ha]
  by_cases hx : ξ ∈ Set.Ico I.1 I.2
  · simp [scalarCellTaylorErrorFunction, I, hx]
  · simp [scalarCellTaylorErrorFunction, I, hx]

theorem levelCellErrorVec_pairwise_orthogonal (κ h t : ℝ) (N q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h)
    {a b : spectralLevelCellIndex N} (hab : a ≠ b) :
    inner ℝ (levelCellErrorVec κ h t N q a hκ hh)
      (levelCellErrorVec κ h t N q b hκ hh) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hd := spectralLevelCellIntervals_pairwise_disjoint N hab
  filter_upwards [levelCellErrorVec_coeFn κ h t N q a hκ hh,
    levelCellErrorVec_coeFn κ h t N q b hκ hh] with ξ ha hb
  rw [ha, hb, Real.inner_apply]
  by_cases hξa : ξ ∈ Set.Ico (spectralLevelCellInterval N a).1
      (spectralLevelCellInterval N a).2
  · have hξb : ξ ∉ Set.Ico (spectralLevelCellInterval N b).1
        (spectralLevelCellInterval N b).2 := by
      intro hmem
      exact (Set.disjoint_left.mp hd) hξa hmem
    simp [scalarCellTaylorErrorFunction, hξa, hξb]
  · simp [scalarCellTaylorErrorFunction, hξa]

theorem spectralLevelTailL2_coeFn (κ h t : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    (spectralLevelTailL2 κ h t N hκ hh : ℝ → ℝ) =ᵐ[spectralMeasure κ h]
      (spectralLevelTailSet N).indicator (scalarPhase t) := by
  exact (((scalarPhaseMemLp κ h t hκ hh).indicator
    ((measurableSet_Ico.compl))).coeFn_toLp)

theorem levelCellErrorVec_tail_orthogonal (κ h t : ℝ) (N q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (a : spectralLevelCellIndex N) :
    inner ℝ (levelCellErrorVec κ h t N q a hκ hh)
      (spectralLevelTailL2 κ h t N hκ hh) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hsubset := spectralLevelCellInterval_subset N a
  filter_upwards [levelCellErrorVec_coeFn κ h t N q a hκ hh,
    spectralLevelTailL2_coeFn κ h t N hκ hh] with ξ ha ht
  rw [ha, ht, Real.inner_apply]
  by_cases hξ : ξ ∈ Set.Ico (spectralLevelCellInterval N a).1
      (spectralLevelCellInterval N a).2
  · have hnot : ξ ∉ spectralLevelTailSet N := by
      intro hmem
      have hout : ξ ∉ Set.Ico (-((2:ℝ)^(N+1))) ((2:ℝ)^(N+1)) := hmem
      exact hout (hsubset hξ)
    have hin : ξ ∈ Set.Ico (-((2:ℝ)^(N+1))) ((2:ℝ)^(N+1)) := hsubset hξ
    simp [scalarCellTaylorErrorFunction, spectralLevelTailSet, hξ, hin]
  · simp [scalarCellTaylorErrorFunction, hξ]

private theorem sum_indicator_eq_indicator_iUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (S : ι → Set α) (f : α → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (x : α) :
    (∑ i, (S i).indicator f x) = (⋃ i, S i).indicator f x := by
  classical
  by_cases hx : x ∈ ⋃ i, S i
  · rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    have hnot : ∀ j, j ≠ i → x ∉ S j := by
      intro j hji hxj
      exact (Set.disjoint_left.mp (hdisj i j hji.symm)) hxi hxj
    have hsum : (∑ j, (S j).indicator f x) = f x := by
      rw [Finset.sum_eq_single i]
      · simp [Set.indicator_of_mem hxi]
      · intro j hj hji
        simp [Set.indicator, hnot j hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    rw [hsum, Set.indicator_of_mem hx]
  · have hnot : ∀ i, x ∉ S i := by
      intro i hxi
      exact hx (Set.mem_iUnion.mpr ⟨i,hxi⟩)
    simp [Set.indicator, hnot, hx]

theorem scalarFeature_eq_cellRestrictions_add_tail
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h) :
    scalarFeature κ h t hκ hh =
      (∑ a : spectralLevelCellIndex N,
        let I := spectralLevelCellInterval N a
        scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh) +
        spectralLevelTailL2 κ h t N hκ hh := by
  classical
  apply Lp.ext
  let μ := spectralMeasure κ h
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ
    (fun a : spectralLevelCellIndex N =>
      let I := spectralLevelCellInterval N a
      scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh)
  have hcellall : ∀ᵐ ξ ∂μ, ∀ a : spectralLevelCellIndex N,
      ((let I := spectralLevelCellInterval N a
        scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh : SpectralAxisL2 κ h) : ℝ → ℝ) ξ =
        (Set.Ico (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2).indicator
          (scalarPhase t) ξ := by
    rw [ae_all_iff]
    intro a
    let I := spectralLevelCellInterval N a
    exact scalarCellFeatureRestrictedL2_coeFn κ h t I.1 I.2 hκ hh
  have htail := spectralLevelTailL2_coeFn κ h t N hκ hh
  have hphase := (scalarPhaseMemLp κ h t hκ hh).coeFn_toLp
  have hadd := Lp.coeFn_add
    (∑ a : spectralLevelCellIndex N,
      let I := spectralLevelCellInterval N a
      scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh)
    (spectralLevelTailL2 κ h t N hκ hh)
  filter_upwards [hphase, hsum, hcellall, htail, hadd] with ξ hphase' hsum' hcell' htail' hadd'
  change ((scalarPhaseMemLp κ h t hκ hh).toLp (scalarPhase t) : SpectralAxisL2 κ h) ξ = _
  rw [hphase', hadd']
  rw [Pi.add_apply, hsum', htail']
  have hdisj : ∀ a b : spectralLevelCellIndex N, a ≠ b →
      Disjoint (Set.Ico (spectralLevelCellInterval N a).1
        (spectralLevelCellInterval N a).2)
        (Set.Ico (spectralLevelCellInterval N b).1
        (spectralLevelCellInterval N b).2) :=
    fun a b hab => spectralLevelCellIntervals_pairwise_disjoint N hab
  have hsumind := sum_indicator_eq_indicator_iUnion
    (fun a : spectralLevelCellIndex N =>
      Set.Ico (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2)
    (scalarPhase t) hdisj ξ
  have hunion := spectralLevelCellIntervals_iUnion N
  have hpoint :
      (∑ a : spectralLevelCellIndex N,
        (Set.Ico (spectralLevelCellInterval N a).1
          (spectralLevelCellInterval N a).2).indicator (scalarPhase t) ξ) +
        (spectralLevelTailSet N).indicator (scalarPhase t) ξ = scalarPhase t ξ := by
    rw [hsumind, hunion]
    by_cases hx : ξ ∈ Set.Ico (-((2:ℝ)^(N+1))) ((2:ℝ)^(N+1))
    · simp [spectralLevelTailSet, hx]
    · simp [spectralLevelTailSet, hx]
  have hsumcell :
      (∑ a : spectralLevelCellIndex N,
        ((let I := spectralLevelCellInterval N a
          scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh : SpectralAxisL2 κ h) : ℝ → ℝ) ξ) =
        ∑ a : spectralLevelCellIndex N,
          (Set.Ico (spectralLevelCellInterval N a).1
            (spectralLevelCellInterval N a).2).indicator (scalarPhase t) ξ := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hcell' a
  rw [hsumcell]
  exact hpoint.symm

theorem scalarFeature_levelTaylor_residual_eq_cells_add_tail
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h) :
    scalarFeature κ h t hκ hh - spectralLevelTaylorApproxL2 κ h t N q hκ hh =
      (∑ a : spectralLevelCellIndex N, levelCellErrorVec κ h t N q a hκ hh) +
        spectralLevelTailL2 κ h t N hκ hh := by
  rw [scalarFeature_eq_cellRestrictions_add_tail κ h t N q hκ hh]
  unfold spectralLevelTaylorApproxL2
  simp_rw [levelCellErrorVec]
  have hsumsub :
      (∑ a : spectralLevelCellIndex N,
        scalarCellFeatureRestrictedL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 hκ hh) -
        (∑ a : spectralLevelCellIndex N,
        spectralCellTaylorApproxL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 q hκ hh
          (spectralLevelCellInterval_order N a)) =
      ∑ a : spectralLevelCellIndex N,
        (scalarCellFeatureRestrictedL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 hκ hh -
        spectralCellTaylorApproxL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 q hκ hh
          (spectralLevelCellInterval_order N a)) := by
    rw [← Finset.sum_sub_distrib]
  calc
    _ = ((∑ a : spectralLevelCellIndex N,
        scalarCellFeatureRestrictedL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 hκ hh) -
        (∑ a : spectralLevelCellIndex N,
        spectralCellTaylorApproxL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 q hκ hh
          (spectralLevelCellInterval_order N a))) +
        spectralLevelTailL2 κ h t N hκ hh := by abel
    _ = (∑ a : spectralLevelCellIndex N,
        (scalarCellFeatureRestrictedL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 hκ hh -
        spectralCellTaylorApproxL2 κ h t
          (spectralLevelCellInterval N a).1 (spectralLevelCellInterval N a).2 q hκ hh
          (spectralLevelCellInterval_order N a))) +
        spectralLevelTailL2 κ h t N hκ hh := by rw [hsumsub]
    _ = _ := rfl

/-- Exact squared-error decomposition: pairwise disjoint cell errors and the
outside-tail residual are orthogonal in the actual weighted spectral L². -/
theorem scalarFeature_levelTaylor_residual_sq_eq_cells_add_tail
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h) :
    ‖scalarFeature κ h t hκ hh - spectralLevelTaylorApproxL2 κ h t N q hκ hh‖^2 =
      (∑ a : spectralLevelCellIndex N,
        ‖levelCellErrorVec κ h t N q a hκ hh‖^2) +
        ‖spectralLevelTailL2 κ h t N hκ hh‖^2 := by
  rw [scalarFeature_levelTaylor_residual_eq_cells_add_tail κ h t N q hκ hh]
  have hcross : inner ℝ
      (∑ a : spectralLevelCellIndex N, levelCellErrorVec κ h t N q a hκ hh)
      (spectralLevelTailL2 κ h t N hκ hh) = 0 := by
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro a ha
    exact levelCellErrorVec_tail_orthogonal κ h t N q hκ hh a
  have hpyth_mul := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (∑ a : spectralLevelCellIndex N, levelCellErrorVec κ h t N q a hκ hh)
    (spectralLevelTailL2 κ h t N hκ hh) hcross
  have hpyth :
      ‖(∑ a : spectralLevelCellIndex N,
          levelCellErrorVec κ h t N q a hκ hh) +
        spectralLevelTailL2 κ h t N hκ hh‖^2 =
      ‖∑ a : spectralLevelCellIndex N, levelCellErrorVec κ h t N q a hκ hh‖^2 +
        ‖spectralLevelTailL2 κ h t N hκ hh‖^2 := by
    simpa only [pow_two] using hpyth_mul
  rw [hpyth]
  rw [norm_sq_sum_of_pairwise_orthogonal κ h Finset.univ
    (levelCellErrorVec κ h t N q · hκ hh)
    (by
      intro a ha b hb hab
      exact levelCellErrorVec_pairwise_orthogonal κ h t N q hκ hh hab)]

/-- Weighted spectral measure of a measurable frequency set is the integral
of the actual Matérn density over that set. -/
theorem spectralMeasure_real_eq_setIntegral_density
    (κ h : ℝ) (hκ : 0 < κ) {s : Set ℝ} (hs : MeasurableSet s) :
    (spectralMeasure κ h).real s = ∫ ξ in s, density κ h ξ := by
  have hweight := integral_spectral_eq_weighted κ h hκ
    (s.indicator (fun _ : ℝ => (1:ℝ)))
  have hintegral :
      ∫ ξ, density κ h ξ * s.indicator (fun _ : ℝ => (1:ℝ)) ξ =
        ∫ ξ in s, density κ h ξ := by
    rw [← integral_indicator hs]
    congr 1
    funext ξ
    by_cases hx : ξ ∈ s <;> simp [hx]
  calc
    (spectralMeasure κ h).real s =
        ∫ ξ, s.indicator (fun _ : ℝ => (1:ℝ)) ξ ∂spectralMeasure κ h := by
          symm
          exact integral_indicator_one hs
    _ = ∫ ξ, density κ h ξ * s.indicator (fun _ : ℝ => (1:ℝ)) ξ := hweight
    _ = ∫ ξ in s, density κ h ξ := hintegral

theorem density_negative_tail_integral_eq (κ h R : ℝ) (hκ : 0 < κ) :
    (∫ ξ in Set.Iio (-R), density κ h ξ) =
      (∫ ξ in Set.Ioi R, density κ h ξ) := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  have hneg := integral_neg_eq_self
    (fun ξ : ℝ => (Set.Ioi R).indicator (density κ h) ξ) volume
  have hfun : (fun ξ : ℝ => (Set.Ioi R).indicator (density κ h) (-ξ)) =
      (Set.Iio (-R)).indicator (density κ h) := by
    funext ξ
    by_cases hx : ξ < -R
    · have hmem : -ξ ∈ Set.Ioi R := by simp only [Set.mem_Ioi]; linarith
      simp [hmem, hx, density, neg_sq]
    · have hmem : -ξ ∉ Set.Ioi R := by
        simp only [Set.mem_Ioi]
        linarith
      simp [hmem, hx, density, neg_sq]
  simpa only [hfun] using hneg

private def dyadicTwoSidedTail (R : ℝ) : Set ℝ :=
  Set.Iio (-R) ∪ Set.Ioi R

theorem dyadicBandCellInterval_subset_twoSidedTail
    (j m : ℕ) (k : Fin (2^(j+m))) (side : Fin 2) (hj : 1 ≤ j) :
    Set.Ico (dyadicBandCellInterval j m k side).1
      (dyadicBandCellInterval j m k side).2 ⊆
        dyadicTwoSidedTail ((2:ℝ)^(j-1)) := by
  have hRpos : 0 < (2:ℝ)^(j-1) := by positivity
  have hRlt : (2:ℝ)^(j-1) < (2:ℝ)^j := by
    have hjpow : (2:ℝ)^j = (2:ℝ)^(j-1) * 2 := by
      calc
        (2:ℝ)^j = (2:ℝ)^(j-1+1) := by congr 1 <;> omega
        _ = (2:ℝ)^(j-1) * 2 := by rw [pow_succ]
    rw [hjpow]
    nlinarith [hRpos]
  have hb := dyadicBandCellInterval_bounds j m k side
  by_cases hs : side.val = 0
  · have hs' : side = 0 := Fin.ext hs
    subst side
    simp at hb
    intro x hx
    change x ∈ Set.Iio (-((2:ℝ)^(j-1))) ∪ Set.Ioi ((2:ℝ)^(j-1))
    right
    simp only [Set.mem_Ioi]
    have hxi := hx
    simp only [Set.mem_Ico] at hxi
    linarith only [hxi.1, hb.1, hRlt]
  · have hs' : side = 1 := by
      apply Fin.ext
      omega
    subst side
    simp at hb
    intro x hx
    change x ∈ Set.Iio (-((2:ℝ)^(j-1))) ∪ Set.Ioi ((2:ℝ)^(j-1))
    left
    simp only [Set.mem_Iio]
    have hxi := hx
    simp only [Set.mem_Ico] at hxi
    linarith only [hxi.2, hb.2, hRlt]

theorem spectralBandCellMass_sum_le_of_pos
    (κ h : ℝ) (j m : ℕ) (hκ : 0 < κ) (hh : 0 < h) (hj : 1 ≤ j) :
    (∑ a : Fin 2 × Fin (2^(j+m)),
      (spectralMeasure κ h).real
        (Set.Ico (dyadicBandCellInterval j m a.2 a.1).1
          (dyadicBandCellInterval j m a.2 a.1).2)) ≤
      (2 * Real.rpow 2 (2*h) / (2*h)) * Real.rpow 2 (-2*h*(j:ℕ)) := by
  classical
  let μ := spectralMeasure κ h
  let I : Fin 2 × Fin (2^(j+m)) → Set ℝ := fun a =>
    Set.Ico (dyadicBandCellInterval j m a.2 a.1).1
      (dyadicBandCellInterval j m a.2 a.1).2
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  have hdisj : Set.Pairwise (↑(Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))))
      (fun a b => Disjoint (I a) (I b)) := by
    intro a ha b hb hab
    rcases a with ⟨sa,ka⟩
    rcases b with ⟨sb,kb⟩
    by_cases hs : sa = sb
    · subst sb
      have hk : ka ≠ kb := by
        intro hk
        apply hab
        cases hk
        rfl
      exact dyadicBandCellIntervals_sameBand_disjoint j m sa hk
    · exact dyadicBandCellIntervals_distinctSide_disjoint j j m m ka kb hs
  have hmeas : ∀ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), MeasurableSet (I a) := by
    intro a ha
    exact measurableSet_Ico
  have hmassunionReal : μ.real (⋃ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), I a) =
      ∑ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), μ.real (I a) :=
    measureReal_biUnion_finset hdisj hmeas (fun a ha => measure_ne_top μ (I a))
  have hsubset : (⋃ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), I a) ⊆
      dyadicTwoSidedTail ((2:ℝ)^(j-1)) := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨ha, hx⟩
    exact dyadicBandCellInterval_subset_twoSidedTail j m a.2 a.1 hj hx
  have htailmeas : MeasurableSet (dyadicTwoSidedTail ((2:ℝ)^(j-1))) := by
    simp [dyadicTwoSidedTail]
  have htailmass : μ.real (dyadicTwoSidedTail ((2:ℝ)^(j-1))) ≤
      2 * (((2:ℝ)^(j-1)) ^ (-2*h) / (2*h)) := by
    let R : ℝ := (2:ℝ)^(j-1)
    have hR : 1 ≤ R := by
      dsimp [R]
      exact one_le_pow₀ (by norm_num)
    have hbound := density_tail_Ioi_le κ h R hκ hh hR
    have hpos : (∫ ξ in Set.Ioi R, density κ h ξ) ≤ R ^ (-2*h) / (2*h) := hbound
    have hneg : (∫ ξ in Set.Iio (-R), density κ h ξ) ≤ R ^ (-2*h) / (2*h) := by
      rw [density_negative_tail_integral_eq κ h R hκ]
      exact hpos
    have hmeasurepos : μ.real (Set.Ioi R) = ∫ ξ in Set.Ioi R, density κ h ξ :=
      spectralMeasure_real_eq_setIntegral_density κ h hκ measurableSet_Ioi
    have hmeasureneg : μ.real (Set.Iio (-R)) = ∫ ξ in Set.Iio (-R), density κ h ξ :=
      spectralMeasure_real_eq_setIntegral_density κ h hκ measurableSet_Iio
    have hunion := measureReal_union_le (μ := μ) (Set.Iio (-R)) (Set.Ioi R)
    have htailEq : dyadicTwoSidedTail ((2:ℝ)^(j-1)) = Set.Iio (-R) ∪ Set.Ioi R := by
      rfl
    rw [htailEq]
    dsimp [R] at hpos hneg
    calc
      μ.real (Set.Iio (-R) ∪ Set.Ioi R) ≤
          μ.real (Set.Iio (-R)) + μ.real (Set.Ioi R) := hunion
      _ = (∫ ξ in Set.Iio (-R), density κ h ξ) +
          (∫ ξ in Set.Ioi R, density κ h ξ) := by rw [hmeasureneg, hmeasurepos]
      _ ≤ R ^ (-2*h) / (2*h) + R ^ (-2*h) / (2*h) := add_le_add hneg hpos
      _ = 2 * (R ^ (-2*h) / (2*h)) := by ring
  calc
    (∑ a : Fin 2 × Fin (2^(j+m)), μ.real (I a))
        = μ.real (⋃ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), I a) := by
            simpa using hmassunionReal.symm
    _ ≤ μ.real (dyadicTwoSidedTail ((2:ℝ)^(j-1))) := measureReal_mono hsubset
    _ ≤ 2 * (((2:ℝ)^(j-1)) ^ (-2*h) / (2*h)) := htailmass
    _ = (2 * Real.rpow 2 (2*h) / (2*h)) * Real.rpow 2 (-2*h*(j:ℕ)) := by
      have hbase : (2:ℝ)^(j-1) = Real.rpow 2 ((j-1:ℕ):ℝ) :=
        (Real.rpow_natCast 2 (j-1)).symm
      have hjid : ((j-1:ℕ):ℝ) = (j:ℝ)-1 := by norm_cast
      have hpower : Real.rpow (Real.rpow 2 ((j-1:ℕ):ℝ)) (-2*h) =
          Real.rpow 2 (((j-1:ℕ):ℝ)*(-2*h)) :=
        (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
      calc
        2 * (((2:ℝ)^(j-1)) ^ (-2*h) / (2*h)) =
            2 * (Real.rpow (Real.rpow 2 ((j-1:ℕ):ℝ)) (-2*h) / (2*h)) := by
              rw [hbase]
              rfl
        _ = 2 * (Real.rpow 2 (2*h + (-2*h*(j:ℝ))) / (2*h)) := by
          rw [hpower, hjid]
          congr 2
          ring
        _ = (2 * Real.rpow 2 (2*h) / (2*h)) * Real.rpow 2 (-2*h*(j:ℕ)) := by
          have hsplit := Real.rpow_add (by norm_num : (0:ℝ)<2)
            (2*h) (-2*h*(j:ℝ))
          calc
            2 * (Real.rpow 2 (2*h + (-2*h*(j:ℝ))) / (2*h)) =
                2 * (Real.rpow 2 (2*h) * Real.rpow 2 (-2*h*(j:ℝ)) / (2*h)) :=
                  congrArg (fun z : ℝ => 2 * (z / (2*h))) hsplit
            _ = (2 * Real.rpow 2 (2*h) / (2*h)) * Real.rpow 2 (-2*h*(j:ℕ)) := by
                  field_simp

theorem spectralLevelCellError_sq_le (κ h t : ℝ) (N q : ℕ)
    (a : spectralLevelCellIndex N) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hwidth :
      (spectralLevelCellInterval N a).2 - (spectralLevelCellInterval N a).1 ≤ 1) :
    ‖levelCellErrorVec κ h t N q a hκ hh‖^2 ≤
      (2*(2*Real.pi*((spectralLevelCellInterval N a).2 -
        (spectralLevelCellInterval N a).1))^q *
        Real.exp (2*Real.pi*((spectralLevelCellInterval N a).2 -
        (spectralLevelCellInterval N a).1)))^2 *
        (spectralMeasure κ h (Set.Ico (spectralLevelCellInterval N a).1
          (spectralLevelCellInterval N a).2)).toReal := by
  let I := spectralLevelCellInterval N a
  have hab := spectralLevelCellInterval_order N a
  have hlocal := scalarCellFeatureRestrictedL2_taylor_error_norm_le
    κ h t I.1 I.2 q hκ hh ht0 ht1 hab hwidth
  have hmass : 0 ≤ (spectralMeasure κ h (Set.Ico I.1 I.2)).toReal := ENNReal.toReal_nonneg
  have hroot : 0 ≤ (spectralMeasure κ h (Set.Ico I.1 I.2)).toReal ^ (1/2:ℝ) :=
    Real.rpow_nonneg hmass _
  have hfactor : 0 ≤ 2*(2*Real.pi*(I.2-I.1))^q*Real.exp (2*Real.pi*(I.2-I.1)) := by
    positivity
  have hsqroot : ((spectralMeasure κ h (Set.Ico I.1 I.2)).toReal ^ (1/2:ℝ))^2 =
      (spectralMeasure κ h (Set.Ico I.1 I.2)).toReal := by
    calc
      _ = Real.rpow (Real.rpow (spectralMeasure κ h (Set.Ico I.1 I.2)).toReal (1/2:ℝ)) (2:ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow (spectralMeasure κ h (Set.Ico I.1 I.2)).toReal ((1/2:ℝ)*(2:ℝ)) :=
        (Real.rpow_mul hmass (1/2:ℝ) (2:ℝ)).symm
      _ = _ := by norm_num [Real.rpow_one]
  have hsq := mul_le_mul hlocal hlocal (norm_nonneg _) (mul_nonneg hfactor hroot)
  have hsq' :
      ‖scalarCellFeatureRestrictedL2 κ h t I.1 I.2 hκ hh -
        spectralCellTaylorApproxL2 κ h t I.1 I.2 q hκ hh hab‖^2 ≤
      (2*(2*Real.pi*(I.2-I.1))^q*Real.exp (2*Real.pi*(I.2-I.1)) *
        (spectralMeasure κ h (Set.Ico I.1 I.2)).toReal^(1/2:ℝ))^2 := by
    simpa [pow_two] using hsq
  rw [mul_pow, hsqroot] at hsq'
  simpa [levelCellErrorVec, I, mul_assoc] using hsq'

theorem dyadicBandCellInterval_width (j m : ℕ) (k : Fin (2^(j+m)))
    (side : Fin 2) :
    (dyadicBandCellInterval j m k side).2 -
      (dyadicBandCellInterval j m k side).1 = (2:ℝ)^(-(m:ℝ)) := by
  by_cases hs : side.val = 0
  · simp [dyadicBandCellInterval, hs]
    field_simp
    ring
  · have hs' : side.val ≠ 0 := hs
    simp [dyadicBandCellInterval, hs']
    field_simp
    ring

theorem centralDyadicCellInterval_width (N : ℕ) (k : Fin (2^N)) :
    (centralDyadicCellInterval N k).2 - (centralDyadicCellInterval N k).1 =
      2 * (2:ℝ)^(-(N:ℝ)) := by
  simp [centralDyadicCellInterval]
  field_simp
  ring

theorem spectralBandLevelError_sq_sum_le
    (κ h t : ℝ) (N q : ℕ) (j : Fin (N+1))
    (hκ : 0 < κ) (hh : 0 < h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ a : Fin 2 × Fin (2^(j.val+(N-j.val)/2)),
      ‖levelCellErrorVec κ h t N q
        (Sum.inr ⟨j,a⟩) hκ hh‖^2) ≤
      (2*(2*Real.pi*((2:ℝ)^(-(((N-j.val)/2:ℕ):ℝ))))^q *
        Real.exp (2*Real.pi*((2:ℝ)^(-(((N-j.val)/2:ℕ):ℝ)))))^2 *
      (∑ a : Fin 2 × Fin (2^(j.val+(N-j.val)/2)),
        (spectralMeasure κ h).real
          (Set.Ico (dyadicBandCellInterval j.val ((N-j.val)/2) a.2 a.1).1
            (dyadicBandCellInterval j.val ((N-j.val)/2) a.2 a.1).2)) := by
  classical
  let m : ℕ := (N-j.val)/2
  let idx : (Fin 2 × Fin (2^(j.val+m))) → spectralLevelCellIndex N :=
    fun a => Sum.inr ⟨j,a⟩
  let δ : ℝ := Real.rpow 2 (-(m:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    have hp : 1 ≤ Real.rpow 2 (m:ℝ) :=
      Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (Nat.cast_nonneg m)
    exact inv_le_one_of_one_le₀ hp
  have hwidth (a : Fin 2 × Fin (2^(j.val+m))) :
      (spectralLevelCellInterval N (idx a)).2 -
        (spectralLevelCellInterval N (idx a)).1 = δ := by
    simp [idx, spectralLevelCellInterval, m, δ, dyadicBandCellInterval_width]
  have hterm (a : Fin 2 × Fin (2^(j.val+m))) :
      ‖levelCellErrorVec κ h t N q (idx a) hκ hh‖^2 ≤
      (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        (spectralMeasure κ h).real
          (Set.Ico (dyadicBandCellInterval j.val m a.2 a.1).1
            (dyadicBandCellInterval j.val m a.2 a.1).2) := by
    have ha := spectralLevelCellError_sq_le κ h t N q (idx a) hκ hh ht0 ht1 (by
      rw [hwidth]
      exact hδle)
    rw [hwidth a] at ha
    simpa [idx, δ, m, spectralLevelCellInterval, Measure.real] using ha
  calc
    (∑ a : Fin 2 × Fin (2^(j.val+m)),
        ‖levelCellErrorVec κ h t N q (idx a) hκ hh‖^2) ≤
      ∑ a : Fin 2 × Fin (2^(j.val+m)),
        (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
          (spectralMeasure κ h).real
            (Set.Ico (dyadicBandCellInterval j.val m a.2 a.1).1
              (dyadicBandCellInterval j.val m a.2 a.1).2) :=
        Finset.sum_le_sum fun a ha => hterm a
    _ = (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        ∑ a : Fin 2 × Fin (2^(j.val+m)),
          (spectralMeasure κ h).real
            (Set.Ico (dyadicBandCellInterval j.val m a.2 a.1).1
              (dyadicBandCellInterval j.val m a.2 a.1).2) := by
        rw [Finset.mul_sum]
    _ = _ := by simp [m, δ]

theorem centralCellMass_sum_le_total (κ h : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    (∑ k : Fin (2^N), (spectralMeasure κ h).real
      (Set.Ico (centralDyadicCellInterval N k).1 (centralDyadicCellInterval N k).2)) ≤
      (spectralMeasure κ h).real Set.univ := by
  classical
  let μ := spectralMeasure κ h
  let I : Fin (2^N) → Set ℝ := fun k =>
    Set.Ico (centralDyadicCellInterval N k).1 (centralDyadicCellInterval N k).2
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  have hd : Set.Pairwise (↑(Finset.univ : Finset (Fin (2^N))))
      (fun k l => Disjoint (I k) (I l)) := by
    intro k hk l hl hkl
    exact spectralLevelCellIntervals_pairwise_disjoint N (by
      intro heq
      apply hkl
      exact Sum.inl_injective heq)
  have hm : ∀ k ∈ (Finset.univ : Finset (Fin (2^N))), MeasurableSet (I k) := by
    intro k hk
    exact measurableSet_Ico
  have hsum : μ.real (⋃ k ∈ (Finset.univ : Finset (Fin (2^N))), I k) =
      ∑ k ∈ (Finset.univ : Finset (Fin (2^N))), μ.real (I k) :=
    measureReal_biUnion_finset hd hm (fun k hk => measure_ne_top μ (I k))
  have hsub : (⋃ k ∈ (Finset.univ : Finset (Fin (2^N))), I k) ⊆ Set.univ := Set.subset_univ _
  rw [← hsum]
  exact measureReal_mono hsub

theorem spectralBandCellMass_sum_le_total (κ h : ℝ) (j m : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    (∑ a : Fin 2 × Fin (2^(j+m)),
      (spectralMeasure κ h).real
        (Set.Ico (dyadicBandCellInterval j m a.2 a.1).1
          (dyadicBandCellInterval j m a.2 a.1).2)) ≤
      (spectralMeasure κ h).real Set.univ := by
  classical
  let μ := spectralMeasure κ h
  let I : Fin 2 × Fin (2^(j+m)) → Set ℝ := fun a =>
    Set.Ico (dyadicBandCellInterval j m a.2 a.1).1
      (dyadicBandCellInterval j m a.2 a.1).2
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  have hd : Set.Pairwise (↑(Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))))
      (fun a b => Disjoint (I a) (I b)) := by
    intro a ha b hb hab
    rcases a with ⟨sa,ka⟩
    rcases b with ⟨sb,kb⟩
    by_cases hs : sa = sb
    · subst sb
      have hk : ka ≠ kb := by
        intro heq
        apply hab
        cases heq
        rfl
      exact dyadicBandCellIntervals_sameBand_disjoint j m sa hk
    · exact dyadicBandCellIntervals_distinctSide_disjoint j j m m ka kb hs
  have hm : ∀ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), MeasurableSet (I a) := by
    intro a ha
    exact measurableSet_Ico
  have hsum : μ.real (⋃ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), I a) =
      ∑ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), μ.real (I a) :=
    measureReal_biUnion_finset hd hm (fun a ha => measure_ne_top μ (I a))
  have hsub : (⋃ a ∈ (Finset.univ : Finset (Fin 2 × Fin (2^(j+m)))), I a) ⊆ Set.univ :=
    Set.subset_univ _
  rw [← hsum]
  simpa using measureReal_mono hsub

theorem centralLevelError_sq_sum_le
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hN : 1 ≤ N) :
    (∑ k : Fin (2^N),
      ‖levelCellErrorVec κ h t N q (Sum.inl k) hκ hh‖^2) ≤
      (2*(2*Real.pi*(2*Real.rpow 2 (-(N:ℝ))))^q *
        Real.exp (2*Real.pi*(2*Real.rpow 2 (-(N:ℝ)))))^2 *
      (spectralMeasure κ h).real Set.univ := by
  classical
  let δ : ℝ := 2*Real.rpow 2 (-(N:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    have hp : (2:ℝ) ≤ (2:ℝ)^N := by
      calc
        (2:ℝ) = (2:ℝ)^1 := by norm_num
        _ ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hN
    rw [Real.rpow_natCast]
    exact (div_le_one (by positivity)).2 (by simpa [div_eq_mul_inv] using hp)
  have hwidth (k : Fin (2^N)) :
      (centralDyadicCellInterval N k).2 - (centralDyadicCellInterval N k).1 = δ := by
    simp [centralDyadicCellInterval_width, δ]
  have hterm (k : Fin (2^N)) :
      ‖levelCellErrorVec κ h t N q (Sum.inl k) hκ hh‖^2 ≤
      (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        (spectralMeasure κ h).real
          (Set.Ico (centralDyadicCellInterval N k).1 (centralDyadicCellInterval N k).2) := by
    have hwidth' : (spectralLevelCellInterval N (Sum.inl k)).2 -
        (spectralLevelCellInterval N (Sum.inl k)).1 = δ := by
      simpa [spectralLevelCellInterval] using hwidth k
    have hk := spectralLevelCellError_sq_le κ h t N q (Sum.inl k) hκ hh ht0 ht1 (by
      rw [hwidth']
      exact hδle)
    rw [hwidth'] at hk
    simpa [δ, spectralLevelCellInterval, Measure.real] using hk
  calc
    _ ≤ ∑ k : Fin (2^N),
        (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
          (spectralMeasure κ h).real
            (Set.Ico (centralDyadicCellInterval N k).1 (centralDyadicCellInterval N k).2) :=
      Finset.sum_le_sum fun k hk => hterm k
    _ = (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        ∑ k : Fin (2^N), (spectralMeasure κ h).real
          (Set.Ico (centralDyadicCellInterval N k).1 (centralDyadicCellInterval N k).2) := by
      rw [Finset.mul_sum]
    _ ≤ (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        (spectralMeasure κ h).real Set.univ :=
      mul_le_mul_of_nonneg_left (centralCellMass_sum_le_total κ h N hκ hh) (sq_nonneg _)

theorem dyadicBandTaylorFactor_sq_le (q m : ℕ) :
    (2*(2*Real.pi*(Real.rpow 2 (-(m:ℝ))))^q *
      Real.exp (2*Real.pi*(Real.rpow 2 (-(m:ℝ)))))^2 ≤
    (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
      Real.rpow 2 (-2*(q:ℝ)*(m:ℝ)) := by
  let δ : ℝ := Real.rpow 2 (-(m:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow (by norm_num : (1:ℝ)≤2) (Nat.cast_nonneg m)
  have hδq : δ^q = Real.rpow 2 (-((q:ℝ)*(m:ℝ))) := by
    calc
      δ^q = Real.rpow δ (q:ℝ) := (Real.rpow_natCast δ q).symm
      _ = Real.rpow (Real.rpow 2 (-(m:ℝ))) (q:ℝ) := rfl
      _ = Real.rpow 2 ((-(m:ℝ))*(q:ℝ)) :=
        (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
      _ = Real.rpow 2 (-((q:ℝ)*(m:ℝ))) := by congr 1 <;> ring
  have harg : 2*Real.pi*δ ≤ 2*Real.pi := by
    calc
      2*Real.pi*δ = (2*Real.pi)*δ := by ring
      _ ≤ (2*Real.pi)*1 := mul_le_mul_of_nonneg_left hδle (by positivity)
      _ = 2*Real.pi := by ring
  have hexp : Real.exp (2*Real.pi*δ) ≤ Real.exp (2*Real.pi) :=
    Real.exp_le_exp.mpr harg
  have hpowa : (2*Real.pi*δ)^q = (2*Real.pi)^q * δ^q := by rw [mul_pow]
  have hA :
      2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ) ≤
        2*(2*Real.pi)^q*Real.exp (2*Real.pi)*Real.rpow 2 (-((q:ℝ)*(m:ℝ))) := by
    rw [hpowa, hδq]
    have hpow_nonneg : 0 ≤ (2*Real.pi)^q := pow_nonneg (by positivity) q
    have hdelta_nonneg : 0 ≤ Real.rpow 2 (-((q:ℝ)*(m:ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    calc
      2*((2*Real.pi)^q*Real.rpow 2 (-((q:ℝ)*(m:ℝ))))*Real.exp (2*Real.pi*δ)
          ≤ 2*((2*Real.pi)^q*Real.rpow 2 (-((q:ℝ)*(m:ℝ))))*Real.exp (2*Real.pi) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 2*(2*Real.pi)^q*Real.exp (2*Real.pi)*
            Real.rpow 2 (-((q:ℝ)*(m:ℝ))) := by ring
  have hA_nonneg : 0 ≤ 2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ) := by positivity
  have hB_nonneg : 0 ≤ 2*(2*Real.pi)^q*Real.exp (2*Real.pi)*
      Real.rpow 2 (-((q:ℝ)*(m:ℝ))) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg (by positivity) q)) (Real.exp_pos _).le)
      (Real.rpow_nonneg (by norm_num) _)
  have hsquare := mul_le_mul hA hA hA_nonneg hB_nonneg
  have hpowSq : (Real.rpow 2 (-((q:ℝ)*(m:ℝ))))^2 =
      Real.rpow 2 (-2*(q:ℝ)*(m:ℝ)) := by
    calc
      _ = Real.rpow (Real.rpow 2 (-((q:ℝ)*(m:ℝ)))) (2:ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow 2 ((-((q:ℝ)*(m:ℝ)))*(2:ℝ)) :=
        (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
      _ = _ := by congr 1 <;> ring
  have hsquare' :
      (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 ≤
        (2*(2*Real.pi)^q*Real.exp (2*Real.pi)*
          Real.rpow 2 (-((q:ℝ)*(m:ℝ))))^2 := by
    simpa only [pow_two] using hsquare
  have hcoeff : (2*(2*Real.pi)^q*Real.exp (2*Real.pi)*
      Real.rpow 2 (-((q:ℝ)*(m:ℝ))))^2 =
      (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        Real.rpow 2 (-2*(q:ℝ)*(m:ℝ)) := by
    rw [mul_pow, hpowSq]
  calc
    _ ≤ (2*(2*Real.pi)^q*Real.exp (2*Real.pi)*
        Real.rpow 2 (-((q:ℝ)*(m:ℝ))))^2 := by simpa [δ] using hsquare'
    _ = (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        Real.rpow 2 (-2*(q:ℝ)*(m:ℝ)) := hcoeff

theorem spectralBandLevelError_sq_sum_le_rate
    (κ h t : ℝ) (N q : ℕ) (j : Fin (N+1))
    (hκ : 0 < κ) (hh : 0 < h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hj : 1 ≤ j.val) :
    (∑ a : Fin 2 × Fin (2^(j.val+(N-j.val)/2)),
      ‖levelCellErrorVec κ h t N q (Sum.inr ⟨j,a⟩) hκ hh‖^2) ≤
      (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        (2*Real.rpow 2 (2*h)/(2*h)) *
        Real.rpow 2 (-2*(q:ℝ)*(((N-j.val)/2:ℕ):ℝ)-2*h*(j.val:ℕ)) := by
  let m : ℕ := (N-j.val)/2
  let δ : ℝ := Real.rpow 2 (-(m:ℝ))
  have hband := spectralBandLevelError_sq_sum_le κ h t N q j hκ hh ht0 ht1
  have hmass := spectralBandCellMass_sum_le_of_pos κ h j.val m hκ hh hj
  have hfac := dyadicBandTaylorFactor_sq_le q m
  have hcoeff : 0 ≤ (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 := sq_nonneg _
  have hmass_nonneg : 0 ≤ (2*Real.rpow 2 (2*h)/(2*h)) *
      Real.rpow 2 (-2*h*(j.val:ℕ)) := by
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (by positivity)
    · exact Real.rpow_nonneg (by norm_num) _
  calc
    _ ≤ (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        (∑ a : Fin 2 × Fin (2^(j.val+m)),
          (spectralMeasure κ h).real
            (Set.Ico (dyadicBandCellInterval j.val m a.2 a.1).1
              (dyadicBandCellInterval j.val m a.2 a.1).2)) := by
          simpa [m, δ] using hband
    _ ≤ (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        ((2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (-2*h*(j.val:ℕ))) :=
          mul_le_mul_of_nonneg_left (by simpa [m] using hmass) (sq_nonneg _)
    _ ≤ ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          Real.rpow 2 (-2*(q:ℝ)*(m:ℝ))) *
        ((2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (-2*h*(j.val:ℕ))) :=
          mul_le_mul_of_nonneg_right (by simpa [δ, m] using hfac) hmass_nonneg
    _ = _ := by
      let A : ℝ := (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2
      let B : ℝ := 2*Real.rpow 2 (2*h)/(2*h)
      have hadd := Real.rpow_add (by norm_num : (0:ℝ)<2)
        (-2*(q:ℝ)*(m:ℝ)) (-2*h*(j.val:ℕ))
      calc
        _ = A * B * (Real.rpow 2 (-2*(q:ℝ)*(m:ℝ)) *
              Real.rpow 2 (-2*h*(j.val:ℕ))) := by dsimp [A,B]; ring
        _ = A * B * Real.rpow 2
              (-2*(q:ℝ)*(m:ℝ) + -2*h*(j.val:ℕ)) := by
                exact congrArg (fun z : ℝ => A * B * z) hadd.symm
        _ = _ := by dsimp [A,B,m]; congr 2 <;> ring

theorem positiveBandLevelErrors_sq_sum_le
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : 2*h < (q:ℝ)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
      ∑ a : Fin 2 × Fin (2^(j.val+(N-j.val)/2)),
        ‖levelCellErrorVec κ h t N q (Sum.inr ⟨j,a⟩) hκ hh‖^2) ≤
      ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        (2*Real.rpow 2 (2*h)/(2*h)) *
        Real.rpow 2 (q:ℝ) *
        (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) *
        Real.rpow 2 (-2*h*(N:ℝ)) := by
  classical
  let C : ℝ := (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
    (2*Real.rpow 2 (2*h)/(2*h))
  let term : ℕ → ℝ := fun r =>
    Real.rpow 2 (-2*(q:ℝ)*(((N-r)/2:ℕ):ℝ)-2*h*(r:ℕ))
  let err : Fin (N+1) → ℝ := fun j =>
    ∑ a : Fin 2 × Fin (2^(j.val+(N-j.val)/2)),
      ‖levelCellErrorVec κ h t N q (Sum.inr ⟨j,a⟩) hκ hh‖^2
  have hpoint (j : Fin (N+1)) (hj : 1 ≤ j.val) :
      err j ≤ C * term j.val := by
    dsimp [err,C,term]
    exact spectralBandLevelError_sq_sum_le_rate κ h t N q j hκ hh ht0 ht1 hj
  have hterms_nonneg (r : ℕ) : 0 ≤ term r := by
    dsimp [term]
    exact Real.rpow_nonneg (by norm_num) _
  have hfilter :
      (∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
        err j) ≤ C * ∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
          term j.val := by
    calc
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
          C * term j.val := by
            apply Finset.sum_le_sum
            intro j hj
            exact hpoint j (Finset.mem_filter.mp hj).2
      _ = C * _ := by rw [Finset.mul_sum]
  have hall :
      (∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
          term j.val) ≤ ∑ j ∈ (Finset.univ : Finset (Fin (N+1))), term j.val :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; exact Finset.mem_univ j)
      (by intro j hj hjnot; exact hterms_nonneg j.val)
  have hfull :
      (∑ j ∈ (Finset.univ : Finset (Fin (N+1))), term j.val) =
        ∑ r ∈ Finset.range (N+1), term r := by
    simpa [term] using (Fin.sum_univ_eq_sum_range
      (fun r => Real.rpow 2 (-2*(q:ℝ)*(((N-r)/2:ℕ):ℝ)-2*h*(r:ℕ))) (N+1))
  have hgeom := dyadicBandTaylorEnergySum_le h q N hq
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ C * ∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
        term j.val := hfilter
    _ ≤ C * ∑ j ∈ (Finset.univ : Finset (Fin (N+1))), term j.val :=
      mul_le_mul_of_nonneg_left hall hC
    _ = C * ∑ r ∈ Finset.range (N+1), term r := by rw [hfull]
    _ ≤ C * (Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℝ)) *
        (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) :=
      mul_le_mul_of_nonneg_left hgeom hC
    _ = _ := by dsimp [C]; ring

theorem dyadicFloorTaylor_decay_le (h : ℝ) (q N m : ℕ)
    (hq : 2*h < (q:ℝ)) (hm : N ≤ 2*m+1) :
    Real.rpow 2 (-2*(q:ℝ)*(m:ℝ)) ≤
      Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℝ)) := by
  have hq0 : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
  have hexp : -2*(q:ℝ)*(m:ℝ) ≤ (q:ℝ)-2*h*(N:ℝ) := by
    have hmcast : (N:ℝ) ≤ 2*(m:ℝ)+1 := by exact_mod_cast hm
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hexp
  calc
    Real.rpow 2 (-2*(q:ℝ)*(m:ℝ)) ≤
        Real.rpow 2 ((q:ℝ)+(-2*h*(N:ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
          nlinarith [hexp]
    _ = Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℝ)) :=
        Real.rpow_add (by norm_num : (0:ℝ)<2) _ _

theorem zeroBandLevelErrors_sq_sum_le
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : 2*h < (q:ℝ)) :
    (∑ a : Fin 2 × Fin (2^(0+(N-0)/2)),
      ‖levelCellErrorVec κ h t N q
        (Sum.inr ⟨⟨0, by omega⟩,a⟩) hκ hh‖^2) ≤
      (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        Real.rpow 2 (q:ℝ) *
        (spectralMeasure κ h).real Set.univ *
        Real.rpow 2 (-2*h*(N:ℝ)) := by
  classical
  let j0 : Fin (N+1) := ⟨0, by omega⟩
  let m : ℕ := N/2
  let δ : ℝ := Real.rpow 2 (-(m:ℝ))
  have hband := spectralBandLevelError_sq_sum_le κ h t N q j0 hκ hh ht0 ht1
  have hmass := spectralBandCellMass_sum_le_total κ h 0 m hκ hh
  have hfac := dyadicBandTaylorFactor_sq_le q m
  have htotal : 0 ≤ (spectralMeasure κ h).real Set.univ := ENNReal.toReal_nonneg
  have hfloor : N ≤ 2*m+1 := by omega
  have hdecay := dyadicFloorTaylor_decay_le h q N m hq hfloor
  have hcoeff : 0 ≤ (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
      Real.rpow 2 (q:ℝ) := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        (∑ a : Fin 2 × Fin (2^(0+m)),
          (spectralMeasure κ h).real
            (Set.Ico (dyadicBandCellInterval 0 m a.2 a.1).1
              (dyadicBandCellInterval 0 m a.2 a.1).2)) := by
          simpa [j0,m,δ] using hband
    _ ≤ (2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ))^2 *
        (spectralMeasure κ h).real Set.univ :=
      mul_le_mul_of_nonneg_left (by simpa [m] using hmass) (sq_nonneg _)
    _ ≤ ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          Real.rpow 2 (-2*(q:ℝ)*(m:ℝ))) *
        (spectralMeasure κ h).real Set.univ :=
      mul_le_mul_of_nonneg_right (by simpa [δ,m] using hfac) htotal
    _ ≤ ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          Real.rpow 2 (q:ℝ) * Real.rpow 2 (-2*h*(N:ℝ))) *
        (spectralMeasure κ h).real Set.univ :=
      by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdecay
              (sq_nonneg (2*(2*Real.pi)^q*Real.exp (2*Real.pi)))) htotal)
    _ = _ := by ring

theorem centralTaylorFactor_sq_le (h : ℝ) (q N : ℕ)
    (hq : 2*h < (q:ℝ)) (hN : 1 ≤ N) :
    (2*(2*Real.pi*(2*Real.rpow 2 (-(N:ℝ))))^q *
      Real.exp (2*Real.pi*(2*Real.rpow 2 (-(N:ℝ)))))^2 ≤
      (2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        Real.rpow 2 (-2*h*(N:ℝ)) := by
  let δ : ℝ := Real.rpow 2 (-(N:ℝ))
  let K : ℝ := 2*(4*Real.pi)^q*Real.exp (2*Real.pi)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1/2 := by
    dsimp [δ]
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    have hNcast : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hpow : 2 ≤ Real.rpow 2 (N:ℝ) := by
      calc
        (2:ℝ) = Real.rpow 2 1 := by norm_num [Real.rpow_one]
        _ ≤ Real.rpow 2 (N:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hNcast
    have hinv : (Real.rpow 2 (N:ℝ))⁻¹ ≤ (2:ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
    simpa using hinv
  have hδq : δ^q = Real.rpow 2 (-((q:ℝ)*(N:ℝ))) := by
    calc
      δ^q = Real.rpow δ (q:ℝ) := (Real.rpow_natCast δ q).symm
      _ = Real.rpow (Real.rpow 2 (-(N:ℝ))) (q:ℝ) := rfl
      _ = Real.rpow 2 ((-(N:ℝ))*(q:ℝ)) :=
        (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
      _ = Real.rpow 2 (-((q:ℝ)*(N:ℝ))) := by congr 1 <;> ring
  have harg : 2*Real.pi*(2*δ) ≤ 2*Real.pi := by
    calc
      2*Real.pi*(2*δ) = (2*Real.pi)*(2*δ) := by ring
      _ ≤ (2*Real.pi)*1 := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [hδle]
        · positivity
      _ = 2*Real.pi := by ring
  have hexp : Real.exp (2*Real.pi*(2*δ)) ≤ Real.exp (2*Real.pi) :=
    Real.exp_le_exp.mpr harg
  have hpowfac : (2*Real.pi*(2*δ))^q =
      (4*Real.pi)^q * Real.rpow 2 (-((q:ℝ)*(N:ℝ))) := by
    rw [show 2*Real.pi*(2*δ) = (4*Real.pi)*δ by ring, mul_pow, hδq]
  have hlinear :
      2*(2*Real.pi*(2*δ))^q*Real.exp (2*Real.pi*(2*δ)) ≤
        K*Real.rpow 2 (-((q:ℝ)*(N:ℝ))) := by
    dsimp [K]
    rw [hpowfac]
    have hbase : 0 ≤ (4*Real.pi)^q * Real.rpow 2 (-((q:ℝ)*(N:ℝ))) :=
      mul_nonneg (pow_nonneg (by positivity) q) (Real.rpow_nonneg (by norm_num) _)
    calc
      2*((4*Real.pi)^q*Real.rpow 2 (-((q:ℝ)*(N:ℝ))))*
            Real.exp (2*Real.pi*(2*δ))
          ≤ 2*((4*Real.pi)^q*Real.rpow 2 (-((q:ℝ)*(N:ℝ))))*
            Real.exp (2*Real.pi) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 2*(4*Real.pi)^q*Real.exp (2*Real.pi)*
            Real.rpow 2 (-((q:ℝ)*(N:ℝ))) := by ring
  have hlin0 : 0 ≤ 2*(2*Real.pi*(2*δ))^q*Real.exp (2*Real.pi*(2*δ)) := by positivity
  have hK0 : 0 ≤ K*Real.rpow 2 (-((q:ℝ)*(N:ℝ))) := by dsimp [K]; positivity
  have hsquare := mul_le_mul hlinear hlinear hlin0 hK0
  have hdec : Real.rpow 2 (-2*(q:ℝ)*(N:ℝ)) ≤
      Real.rpow 2 (-2*h*(N:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    nlinarith [hq, (show 0 ≤ (N:ℝ) by positivity)]
  have hpowSq : (Real.rpow 2 (-((q:ℝ)*(N:ℝ))))^2 =
      Real.rpow 2 (-2*(q:ℝ)*(N:ℝ)) := by
    calc
      _ = Real.rpow (Real.rpow 2 (-((q:ℝ)*(N:ℝ)))) (2:ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = Real.rpow 2 ((-((q:ℝ)*(N:ℝ)))*(2:ℝ)) :=
        (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
      _ = _ := by congr 1 <;> ring
  have hKsq : K^2 = (2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 := rfl
  have hsquare' :
      (2*(2*Real.pi*(2*δ))^q*Real.exp (2*Real.pi*(2*δ)))^2 ≤
        (K*Real.rpow 2 (-((q:ℝ)*(N:ℝ))))^2 := by
    simpa only [pow_two] using hsquare
  calc
    _ ≤ K^2 * (Real.rpow 2 (-((q:ℝ)*(N:ℝ))))^2 := by
      calc
        _ ≤ (K*Real.rpow 2 (-((q:ℝ)*(N:ℝ))))^2 := hsquare'
        _ = _ := by rw [mul_pow]
    _ ≤ K^2 * Real.rpow 2 (-2*h*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left (by rw [hpowSq]; exact hdec) (sq_nonneg K)
    _ = _ := by rfl

theorem centralLevelErrors_sq_sum_le_rate
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : 2*h < (q:ℝ))
    (hN : 1 ≤ N) :
    (∑ k : Fin (2^N),
      ‖levelCellErrorVec κ h t N q (Sum.inl k) hκ hh‖^2) ≤
      (2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        (spectralMeasure κ h).real Set.univ *
        Real.rpow 2 (-2*h*(N:ℝ)) := by
  have hcentral := centralLevelError_sq_sum_le κ h t N q hκ hh ht0 ht1 hN
  have hfac := centralTaylorFactor_sq_le h q N hq hN
  have hmass : 0 ≤ (spectralMeasure κ h).real Set.univ := ENNReal.toReal_nonneg
  calc
    _ ≤ (2*(2*Real.pi*(2*Real.rpow 2 (-(N:ℝ))))^q *
        Real.exp (2*Real.pi*(2*Real.rpow 2 (-(N:ℝ)))))^2 *
        (spectralMeasure κ h).real Set.univ := hcentral
    _ ≤ (2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        Real.rpow 2 (-2*h*(N:ℝ)) *
        (spectralMeasure κ h).real Set.univ :=
      mul_le_mul_of_nonneg_right hfac hmass
    _ = _ := by ring

theorem realL2_norm_sq_eq_setIntegral_sq
    (κ h t : ℝ) (N : ℕ) (hκ : 0 < κ) (hh : 0 < h) :
    ‖spectralLevelTailL2 κ h t N hκ hh‖^2 =
      ∫ ξ in spectralLevelTailSet N, (scalarPhase t ξ)^2 ∂spectralMeasure κ h := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hco := spectralLevelTailL2_coeFn κ h t N hκ hh
  have hpoint :
      (fun ξ : ℝ => inner ℝ
        (spectralLevelTailL2 κ h t N hκ hh ξ)
        (spectralLevelTailL2 κ h t N hκ hh ξ)) =ᵐ[spectralMeasure κ h]
        (spectralLevelTailSet N).indicator (fun ξ => (scalarPhase t ξ)^2) := by
    filter_upwards [hco] with ξ hξ
    rw [hξ]
    by_cases hx : ξ ∈ spectralLevelTailSet N <;>
      simp [Real.inner_apply, hx]
  rw [integral_congr_ae hpoint]
  rw [← integral_indicator (by simp [spectralLevelTailSet])]

theorem spectralLevelTail_measure_le (κ h : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    (spectralMeasure κ h).real (spectralLevelTailSet N) ≤
      2 * (((2:ℝ)^N)^(-2*h)/(2*h)) := by
  letI : IsFiniteMeasure (spectralMeasure κ h) := spectralMeasure_isFinite κ h hκ hh
  let R : ℝ := (2:ℝ)^N
  let RC : ℝ := (2:ℝ)^(N+1)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hgap : R < RC := by
    dsimp [R,RC]
    rw [pow_succ]
    nlinarith [sq_pos_of_pos (show 0 < (2:ℝ)^N by positivity)]
  have hsubset : spectralLevelTailSet N ⊆ Set.Iio (-R) ∪ Set.Ioi R := by
    intro x hx
    have hxout : x ∉ Set.Ico (-RC) RC := by simpa [spectralLevelTailSet,RC] using hx
    by_cases hneg : x < -RC
    · left
      change x < -R
      linarith
    · right
      have hle : RC ≤ x := by
        by_contra hn
        have hxlo : -RC ≤ x := le_of_not_gt hneg
        have hxhi : x < RC := lt_of_not_ge hn
        exact hxout ⟨hxlo,hxhi⟩
      change R < x
      linarith
  have hneg : (∫ ξ in Set.Iio (-R), density κ h ξ) ≤ R^(-2*h)/(2*h) := by
    rw [density_negative_tail_integral_eq κ h R hκ]
    exact density_dyadic_tail_le κ h N hκ hh
  have hpos : (∫ ξ in Set.Ioi R, density κ h ξ) ≤ R^(-2*h)/(2*h) := by
    dsimp [R]
    exact density_dyadic_tail_le κ h N hκ hh
  have htailmeas : MeasurableSet (spectralLevelTailSet N) := by
    simp [spectralLevelTailSet]
  calc
    _ ≤ (spectralMeasure κ h).real (Set.Iio (-R) ∪ Set.Ioi R) :=
      measureReal_mono hsubset
    _ ≤ (spectralMeasure κ h).real (Set.Iio (-R)) +
        (spectralMeasure κ h).real (Set.Ioi R) :=
      measureReal_union_le _ _
    _ = (∫ ξ in Set.Iio (-R), density κ h ξ) +
        (∫ ξ in Set.Ioi R, density κ h ξ) := by
          rw [spectralMeasure_real_eq_setIntegral_density κ h hκ measurableSet_Iio,
            spectralMeasure_real_eq_setIntegral_density κ h hκ measurableSet_Ioi]
    _ ≤ R^(-2*h)/(2*h) + R^(-2*h)/(2*h) := add_le_add hneg hpos
    _ = 2 * (R^(-2*h)/(2*h)) := by ring
    _ = _ := by dsimp [R]

theorem spectralLevelTail_norm_sq_le (κ h t : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    ‖spectralLevelTailL2 κ h t N hκ hh‖^2 ≤
      8 * (((2:ℝ)^N)^(-2*h)/(2*h)) := by
  let μ := spectralMeasure κ h
  let T := spectralLevelTailSet N
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  rw [realL2_norm_sq_eq_setIntegral_sq κ h t N hκ hh]
  have hphase : IntegrableOn (fun ξ : ℝ => (scalarPhase t ξ)^2) T μ := by
    have hi : Integrable (fun ξ : ℝ => ‖scalarPhase t ξ‖^2) μ :=
      (scalarPhaseMemLp κ h t hκ hh).integrable_norm_pow (p := 2) (by norm_num)
    have hi' : Integrable (fun ξ : ℝ => (scalarPhase t ξ)^2) μ := by
      simpa [Real.norm_eq_abs, sq_abs] using hi
    exact hi'.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ => (4:ℝ)) T μ :=
    integrableOn_const (measure_ne_top μ T)
  have hpoint : ∀ ξ ∈ T, (scalarPhase t ξ)^2 ≤ 4 := by
    intro ξ hξ
    have habs := scalarPhase_abs_le t ξ
    have hupper : scalarPhase t ξ ≤ 2 := (abs_le.mp habs).2
    have hlower : -2 ≤ scalarPhase t ξ := (abs_le.mp habs).1
    nlinarith
  have hmono := setIntegral_mono_on hphase hconst
    (by simp [T, spectralLevelTailSet]) hpoint
  have hconsteq : (∫ ξ in T, (4:ℝ) ∂μ) = 4 * μ.real T := by
    rw [integral_const]
    simp only [Measure.real_def, smul_eq_mul]
    rw [Measure.restrict_apply_univ T]
    ring
  calc
    (∫ ξ in T, (scalarPhase t ξ)^2 ∂μ) ≤
        ∫ ξ in T, (4:ℝ) ∂μ := hmono
    _ = 4 * μ.real T := hconsteq
    _ ≤ 8 * (((2:ℝ)^N)^(-2*h)/(2*h)) := by
      have hmass := spectralLevelTail_measure_le κ h N hκ hh
      nlinarith [hmass]

/-- Quantitative squared error for the actual finite Taylor source sum. This
combines the disjoint-cell Pythagorean identity, the central and signed-band
Taylor errors, and the omitted Matérn tail. -/
theorem scalarFeature_levelTaylor_residual_sq_le
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : 2*h < (q:ℝ))
    (hN : 1 ≤ N) :
    ‖scalarFeature κ h t hκ hh - spectralLevelTaylorApproxL2 κ h t N q hκ hh‖^2 ≤
      (((2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
          (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) +
        (8/(2*h))) * Real.rpow 2 (-2*h*(N:ℝ)) := by
  classical
  let err : spectralLevelCellIndex N → ℝ := fun a =>
    ‖levelCellErrorVec κ h t N q a hκ hh‖^2
  let j0 : Fin (N+1) := ⟨0, by omega⟩
  have hsplit :
      (∑ a : spectralLevelCellIndex N, err a) =
        (∑ k : Fin (2^N), err (Sum.inl k)) +
          (∑ j : Fin (N+1),
            ∑ a : Fin 2 × Fin (2^(j.val+(N-j.val)/2)),
              err (Sum.inr ⟨j,a⟩)) := by
    simp [err, spectralLevelCellIndex, Fintype.sum_sum_type, Fintype.sum_sigma]
  let bandErr : Fin (N+1) → ℝ := fun j =>
    ∑ a : Fin 2 × Fin (2^(j.val+(N-j.val)/2)),
      ‖levelCellErrorVec κ h t N q (Sum.inr ⟨j,a⟩) hκ hh‖^2
  have hbandSplit :
      (∑ j : Fin (N+1), bandErr j) = bandErr j0 +
        (∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
          bandErr j) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (N+1)))
      (fun j => j.val = 0)]
    have hfilterzero :
        (Finset.univ : Finset (Fin (N+1))).filter (fun j => j.val = 0) = {j0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj
        apply Fin.ext
        simpa [j0] using hj
      · intro hj
        have : j = j0 := hj
        subst j
        simp [j0]
    have hz :
        (∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => j.val = 0),
          bandErr j) = bandErr j0 := by
      rw [hfilterzero]
      simp
    have hpos :
        (Finset.univ : Finset (Fin (N+1))).filter (fun j => ¬ j.val = 0) =
          Finset.univ.filter (fun j => 1 ≤ j.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hz, hpos]
  have hcentral := centralLevelErrors_sq_sum_le_rate κ h t N q hκ hh ht0 ht1 hq hN
  have hzero := zeroBandLevelErrors_sq_sum_le κ h t N q hκ hh ht0 ht1 hq
  have hpositive := positiveBandLevelErrors_sq_sum_le κ h t N q hκ hh ht0 ht1 hq
  have hbandzero : bandErr j0 ≤
      (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
        (spectralMeasure κ h).real Set.univ * Real.rpow 2 (-2*h*(N:ℝ)) := by
    dsimp [bandErr, j0]
    convert hzero using 1 <;> rfl
  have hbandpos :
      (∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
        bandErr j) ≤
      ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
        (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
        (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) * Real.rpow 2 (-2*h*(N:ℝ)) := by
    simpa [bandErr] using hpositive
  have htail := spectralLevelTail_norm_sq_le κ h t N hκ hh
  have htailRate :
      ‖spectralLevelTailL2 κ h t N hκ hh‖^2 ≤
        (8/(2*h)) * Real.rpow 2 (-2*h*(N:ℝ)) := by
    have hpow : ((2:ℝ)^N)^(-2*h) = (2:ℝ)^(-2*h*(N:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    calc
      _ ≤ 8 * (((2:ℝ)^N)^(-2*h)/(2*h)) := htail
      _ = 8 * ((2:ℝ)^(-2*h*(N:ℝ))/(2*h)) := by rw [hpow]
      _ = (8/(2*h)) * Real.rpow 2 (-2*h*(N:ℝ)) := by
        change 8 * (Real.rpow 2 (-2*h*(N:ℝ))/(2*h)) = _
        ring
  have hcells :
      (∑ a : spectralLevelCellIndex N,
        ‖levelCellErrorVec κ h t N q a hκ hh‖^2) ≤
      (((2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
          (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹)) * Real.rpow 2 (-2*h*(N:ℝ)) := by
    calc
      _ = (∑ k : Fin (2^N), err (Sum.inl k)) +
          (∑ j : Fin (N+1), bandErr j) := by
            simpa [err, bandErr] using hsplit
      _ = (∑ k : Fin (2^N), err (Sum.inl k)) +
          (bandErr j0 +
            (∑ j ∈ (Finset.univ : Finset (Fin (N+1))).filter (fun j => 1 ≤ j.val),
              bandErr j)) := by rw [hbandSplit]
      _ ≤ (2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
            (spectralMeasure κ h).real Set.univ * Real.rpow 2 (-2*h*(N:ℝ)) +
          ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
            (spectralMeasure κ h).real Set.univ * Real.rpow 2 (-2*h*(N:ℝ)) +
          (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
            (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
            (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹ * Real.rpow 2 (-2*h*(N:ℝ))) := by
              exact add_le_add hcentral (add_le_add hbandzero hbandpos)
      _ = _ := by ring
  rw [scalarFeature_levelTaylor_residual_sq_eq_cells_add_tail]
  have := add_le_add hcells htailRate
  nlinarith

/-- Norm form of the actual normalized feature approximation endpoint. -/
theorem scalarFeature_levelTaylor_residual_norm_le
    (κ h t : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hq : 2*h < (q:ℝ))
    (hN : 1 ≤ N) :
    ‖scalarFeature κ h t hκ hh - spectralLevelTaylorApproxL2 κ h t N q hκ hh‖ ≤
      Real.sqrt (
        ((2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
            (spectralMeasure κ h).real Set.univ) +
          ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
            (spectralMeasure κ h).real Set.univ) +
          ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
            (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
            (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) +
          (8/(2*h))) * Real.rpow 2 (-h*(N:ℝ)) := by
  have hsquare := scalarFeature_levelTaylor_residual_sq_le κ h t N q hκ hh ht0 ht1 hq hN
  have hden : 0 < 1-Real.rpow 2 (-(q:ℝ)+2*h) := by
    apply sub_pos.mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2)
    linarith
  have hInv : 0 ≤ (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹ := inv_nonneg.mpr hden.le
  have hmass : 0 ≤ (spectralMeasure κ h).real Set.univ := ENNReal.toReal_nonneg
  have hA : 0 ≤ (2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
      (spectralMeasure κ h).real Set.univ := mul_nonneg (sq_nonneg _) hmass
  have hB : 0 ≤ (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
      Real.rpow 2 (q:ℝ) * (spectralMeasure κ h).real Set.univ :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)) hmass
  have hratio : 0 ≤ 2*Real.rpow 2 (2*h)/(2*h) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (le_of_lt (by positivity))
  have hCterm : 0 ≤ (2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
      (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
      (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hratio)
      (Real.rpow_nonneg (by norm_num) _)) hInv
  have hD : 0 ≤ (8/(2*h)) := div_nonneg (by norm_num) (le_of_lt (by positivity))
  have hC : 0 ≤
      ((2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
          (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) + (8/(2*h)) := by
    exact add_nonneg (add_nonneg (add_nonneg hA hB) hCterm) hD
  have hdec : 0 ≤ Real.rpow 2 (-h*(N:ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hdec2 : (Real.rpow 2 (-h*(N:ℝ)))^2 = Real.rpow 2 (-2*h*(N:ℝ)) := by
    have hadd := Real.rpow_add (by norm_num : (0:ℝ) < 2)
      (-h*(N:ℝ)) (-h*(N:ℝ))
    calc
      (Real.rpow 2 (-h*(N:ℝ)))^2 =
          Real.rpow 2 (-h*(N:ℝ)) * Real.rpow 2 (-h*(N:ℝ)) := by ring
      _ = Real.rpow 2 (-h*(N:ℝ) + -h*(N:ℝ)) := hadd.symm
      _ = Real.rpow 2 (-2*h*(N:ℝ)) := by congr 1 <;> ring
  have hsqrt : (Real.sqrt (
      ((2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
          (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) +
        (8/(2*h))))^2 =
      ((2*(4*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 * Real.rpow 2 (q:ℝ) *
          (spectralMeasure κ h).real Set.univ) +
        ((2*(2*Real.pi)^q*Real.exp (2*Real.pi))^2 *
          (2*Real.rpow 2 (2*h)/(2*h)) * Real.rpow 2 (q:ℝ) *
          (1-Real.rpow 2 (-(q:ℝ)+2*h))⁻¹) + (8/(2*h)) := by
    rw [Real.sq_sqrt hC]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hdec)).mp
  rw [mul_pow, hsqrt, hdec2]
  exact hsquare

end BrownianSharp.AlignmentPaperMaternSpectralAggregation
