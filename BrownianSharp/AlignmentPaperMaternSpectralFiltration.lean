import BrownianSharp.AlignmentPaperMaternSpectralApproximation
import BrownianSharp.AlignmentPaperCumulativeFiltration
import BrownianSharp.AlignmentMaternContinuousFeature

/-! Finite-dimensional Matérn spectral level spaces built from the actual
normalized dyadic-cell monomials used by the cell Taylor approximants. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMaternSpectralFiltration

open BrownianSharp.AlignmentPaperMaternSpectralApproximation
open BrownianSharp.AlignmentMaternContinuousFeature
open BrownianSharp.AlignmentMaternScalarFeature
open BrownianSharp.AlignmentPaperGenericGradedHilbert
open BrownianSharp.AlignmentNestedProjectionGrades

abbrev LevelIndex (N q : ℕ) :=
  (Fin (2^N) × Fin q) ⊕
    (Σ j : Fin (N+1), Fin 2 × Fin (2^(j.val+(N-j.val)/2)) × Fin q)

def levelGenerator (κ h : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (a : LevelIndex N q) : SpectralAxisL2 κ h := by
  cases a with
  | inl central =>
      let k := central.1
      let ell := central.2
      let I := centralDyadicCellInterval N k
      exact spectralCellMonomial κ h I.1 I.2 ell.val hκ hh
        (centralDyadicCellInterval_order N k)
  | inr band =>
      let j := band.1.val
      let m := (N-j)/2
      let side := band.2.1
      let k := band.2.2.1
      let ell := band.2.2.2
      let I := dyadicBandCellInterval j m k side
      exact spectralCellMonomial κ h I.1 I.2 ell.val hκ hh
        (dyadicBandCellInterval_order j m k side)

/-- The level-N spectral source space contains all degree-<q normalized
monomials on the dyadically partitioned central band and on every signed
frequency cell at band j and resolution floor((N-j)/2). -/
def levelSpace (κ h : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h) :
    Submodule ℝ (SpectralAxisL2 κ h) :=
  Submodule.span ℝ (Set.range (levelGenerator κ h N q hκ hh))

theorem levelSpace_finiteDimensional (κ h : ℝ) (N q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    FiniteDimensional ℝ ↥(levelSpace κ h N q hκ hh) := by
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem levelSpace_finrank_le_card (κ h : ℝ) (N q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    Module.finrank ℝ ↥(levelSpace κ h N q hκ hh) ≤ Fintype.card (LevelIndex N q) := by
  classical
  unfold levelSpace
  calc
    Module.finrank ℝ (Submodule.span ℝ (Set.range (levelGenerator κ h N q hκ hh))) ≤
        (Set.range (levelGenerator κ h N q hκ hh)).toFinset.card := finrank_span_le_card _
    _ ≤ Fintype.card (LevelIndex N q) := by
      simpa only [Set.toFinset_card] using
        Fintype.card_range_le (levelGenerator κ h N q hκ hh)

private def dyadicBandWeightSum (N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (N+1), 2^(j+(N-j)/2)

private theorem dyadicBandWeightSum_succ_two (N : ℕ) :
    dyadicBandWeightSum (N+2) =
      2 * dyadicBandWeightSum N + 2^(N+1) + 2^(N+2) := by
  unfold dyadicBandWeightSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hold :
      (∑ j ∈ Finset.range (N+1), 2^(j+(N+2-j)/2)) =
        2 * ∑ j ∈ Finset.range (N+1), 2^(j+(N-j)/2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N := by simp only [Finset.mem_range] at hj; omega
    have hexp : j + (N+2-j)/2 = j+(N-j)/2+1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [hold]
  have htop₁ : (N+1)+(N+2-(N+1))/2 = N+1 := by omega
  have htop₂ : (N+2)+(N+2-(N+2))/2 = N+2 := by omega
  rw [htop₁, htop₂]

private theorem dyadicBandWeightSum_le (N : ℕ) :
    dyadicBandWeightSum N ≤ 4*2^N := by
  induction N using Nat.twoStepInduction with
  | zero => norm_num [dyadicBandWeightSum]
  | one => norm_num [dyadicBandWeightSum]
  | more N ih₀ ih₁ =>
      rw [dyadicBandWeightSum_succ_two]
      have h1 : 2^(N+1) = 2*2^N := by rw [pow_succ]; ring
      have h2 : 2^(N+2) = 4*2^N := by rw [show N+2 = (N+1)+1 by omega, pow_succ, h1]; ring
      rw [h1,h2]
      nlinarith [ih₀]

theorem levelSpace_finrank_le_dyadic (κ h : ℝ) (N q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    Module.finrank ℝ ↥(levelSpace κ h N q hκ hh) ≤ (9*q)*2^N := by
  classical
  have hcard : Fintype.card (LevelIndex N q) =
      (2^N)*q + ∑ j : Fin (N+1), 2 * 2^(j.val+(N-j.val)/2) * q := by
    simp [LevelIndex, Fintype.card_sum, Fintype.card_sigma,
      Fintype.card_prod, mul_assoc]
  have hsum :
      (∑ j : Fin (N+1), 2 * 2^(j.val+(N-j.val)/2) * q) =
        2*q * dyadicBandWeightSum N := by
    rw [dyadicBandWeightSum, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    Module.finrank ℝ ↥(levelSpace κ h N q hκ hh) ≤ Fintype.card (LevelIndex N q) :=
      levelSpace_finrank_le_card κ h N q hκ hh
    _ = q*2^N + 2*q * dyadicBandWeightSum N := by rw [hcard, hsum]; ring
    _ ≤ q*2^N + (2*q)*(4*2^N) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (dyadicBandWeightSum_le N)) _
    _ = (9*q)*2^N := by ring

theorem spectralCentralCellPolynomialSubmodule_le_levelSpace
    (κ h : ℝ) (N q : ℕ) (k : Fin (2^N))
    (hκ : 0 < κ) (hh : 0 < h) :
    let I := centralDyadicCellInterval N k
    spectralCellPolynomialSubmodule κ h I.1 I.2 q hκ hh
      (centralDyadicCellInterval_order N k) ≤ levelSpace κ h N q hκ hh := by
  classical
  dsimp
  apply Submodule.span_le.mpr
  rintro _ ⟨ell, rfl⟩
  apply Submodule.subset_span
  refine ⟨Sum.inl (k, ell), ?_⟩
  rfl

theorem spectralCellPolynomialSubmodule_le_levelSpace
    (κ h : ℝ) (N q j : ℕ) (hj : j ≤ N)
    (side : Fin 2) (k : Fin (2^(j+(N-j)/2)))
    (hκ : 0 < κ) (hh : 0 < h) :
    let I := dyadicBandCellInterval j ((N-j)/2) k side
    spectralCellPolynomialSubmodule κ h I.1 I.2 q hκ hh
      (dyadicBandCellInterval_order j ((N-j)/2) k side) ≤
        levelSpace κ h N q hκ hh := by
  classical
  dsimp
  apply Submodule.span_le.mpr
  rintro _ ⟨ell, rfl⟩
  apply Submodule.subset_span
  refine ⟨Sum.inr ⟨⟨j, by omega⟩, side, k, ell⟩, ?_⟩
  rfl

/-- Each actual Taylor source vector on a spectral cell lies in the span of
its normalized monomial generators. -/
theorem spectralCellTaylorApproxL2_mem_polynomial (κ h t a b : ℝ) (q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (hab : a < b) :
    spectralCellTaylorApproxL2 κ h t a b q hκ hh hab ∈
      spectralCellPolynomialSubmodule κ h a b q hκ hh hab := by
  classical
  unfold spectralCellTaylorApproxL2
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨⟨m, Finset.mem_range.mp hm⟩, ?_⟩
  rfl

/-- The level-N actual Taylor approximant is in the exact finite-dimensional
source space, including central and signed frequency cells. -/
theorem spectralLevelTaylorApproxL2_mem (κ h t : ℝ) (N q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    spectralLevelTaylorApproxL2 κ h t N q hκ hh ∈
      levelSpace κ h N q hκ hh := by
  classical
  unfold spectralLevelTaylorApproxL2
  apply Submodule.sum_mem
  intro a ha
  let I := spectralLevelCellInterval N a
  have hcell := spectralCellTaylorApproxL2_mem_polynomial κ h t I.1 I.2 q hκ hh
    (spectralLevelCellInterval_order N a)
  have hsub : spectralCellPolynomialSubmodule κ h I.1 I.2 q hκ hh
      (spectralLevelCellInterval_order N a) ≤ levelSpace κ h N q hκ hh := by
    cases a with
    | inl k =>
        simpa [I, spectralLevelCellInterval] using
          spectralCentralCellPolynomialSubmodule_le_levelSpace κ h N q k hκ hh
    | inr band =>
        simpa [I, spectralLevelCellInterval] using
          spectralCellPolynomialSubmodule_le_levelSpace κ h N q band.1.val
            (Nat.le_of_lt_succ band.1.isLt) band.2.1 band.2.2 hκ hh
  exact hsub hcell

/-- Cumulative nested spectral spaces with their explicit dimension bound. -/
def cumulativeLevelSpace (κ h : ℝ) (q N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) : Submodule ℝ (SpectralAxisL2 κ h) :=
  BrownianSharp.AlignmentPaperCumulativeFiltration.cumulativeFiltration
    (fun n => levelSpace κ h n q hκ hh) N

theorem cumulativeLevelSpace_nested (κ h : ℝ) (q N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    cumulativeLevelSpace κ h q N hκ hh ≤ cumulativeLevelSpace κ h q (N+1) hκ hh :=
  BrownianSharp.AlignmentPaperCumulativeFiltration.cumulativeFiltration_nested
    (fun n => levelSpace κ h n q hκ hh) N

theorem cumulativeLevelSpace_finiteDimensional (κ h : ℝ) (q N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    FiniteDimensional ℝ ↥(cumulativeLevelSpace κ h q N hκ hh) :=
  BrownianSharp.AlignmentPaperCumulativeFiltration.cumulativeFiltration_finiteDimensional
    (fun n => levelSpace κ h n q hκ hh)
    (fun n => levelSpace_finiteDimensional κ h n q hκ hh) N

/-- Finite dimensional cumulative Matérn spaces are complete, hence admit
orthogonal projection in the ambient Hilbert space. -/
instance cumulativeLevelSpace_hasOrthogonalProjection (κ h : ℝ) (q N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    (cumulativeLevelSpace κ h q N hκ hh).HasOrthogonalProjection := by
  letI : FiniteDimensional ℝ
      ↥(cumulativeLevelSpace κ h q N hκ hh) :=
    cumulativeLevelSpace_finiteDimensional κ h q N hκ hh
  letI : CompleteSpace ↥(cumulativeLevelSpace κ h q N hκ hh) :=
    FiniteDimensional.complete ℝ _
  infer_instance

/-- Normalizing the scalar feature preserves the level-N error up to its
fixed variance normalization. The cumulative orthogonal projection is no worse
than the actual level Taylor candidate. -/
theorem normalizedAxis_cumulative_residual_le_of_levelTaylorError
    (κ h t hdecay C0 : ℝ) (N q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (hdecay_pos : 0 < hdecay) (hC0 : 0 ≤ C0)
    (herr : ‖scalarFeature κ h t hκ hh -
      spectralLevelTaylorApproxL2 κ h t N q hκ hh‖ ≤
        C0 * (Real.rpow 2 (-hdecay)) ^ N) :
    ‖normalizedAxis κ h t hκ hh -
      (cumulativeLevelSpace κ h q N hκ hh).starProjection
        (normalizedAxis κ h t hκ hh)‖ ≤
      ‖scalarFeature κ h 0 hκ hh‖⁻¹ * C0 *
        (Real.rpow 2 (-hdecay)) ^ N := by
  let U := cumulativeLevelSpace κ h q N hκ hh
  let c : ℝ := ‖scalarFeature κ h 0 hκ hh‖⁻¹
  have hcpos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (scalarFeature_norm_pos κ h 0 hκ hh)
  have hproj : U.starProjection (normalizedAxis κ h t hκ hh) =
      c • U.starProjection (scalarFeature κ h t hκ hh) := by
    rw [normalizedAxis, map_smul]
  have hmemLevel := spectralLevelTaylorApproxL2_mem κ h t N q hκ hh
  have hmem : c • spectralLevelTaylorApproxL2 κ h t N q hκ hh ∈ U := by
    dsimp [U]
    apply BrownianSharp.AlignmentPaperCumulativeFiltration.cumulative_candidate_mem
    exact Submodule.smul_mem _ _ hmemLevel
  have hmin := BrownianSharp.AlignmentPaperCumulativeFiltration.projection_residual_le_of_candidate
    U N (normalizedAxis κ h t hκ hh)
    (c • spectralLevelTaylorApproxL2 κ h t N q hκ hh) hmem
  have hcandidate :
      ‖normalizedAxis κ h t hκ hh -
        c • spectralLevelTaylorApproxL2 κ h t N q hκ hh‖ =
        c * ‖scalarFeature κ h t hκ hh -
          spectralLevelTaylorApproxL2 κ h t N q hκ hh‖ := by
    rw [normalizedAxis, show ‖scalarFeature κ h 0 hκ hh‖⁻¹ = c by rfl,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  rw [show (c * C0) * (Real.rpow 2 (-hdecay)) ^ N =
      c * (C0 * (Real.rpow 2 (-hdecay)) ^ N) by ring]
  calc
    _ ≤ ‖normalizedAxis κ h t hκ hh -
          c • spectralLevelTaylorApproxL2 κ h t N q hκ hh‖ := by
          simpa [U, hproj] using hmin
    _ = c * ‖scalarFeature κ h t hκ hh -
          spectralLevelTaylorApproxL2 κ h t N q hκ hh‖ := hcandidate
    _ ≤ c * (C0 * (Real.rpow 2 (-hdecay)) ^ N) :=
      mul_le_mul_of_nonneg_left herr hcpos.le

theorem cumulativeLevelSpace_finrank_le (κ h : ℝ) (q N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    Module.finrank ℝ ↥(cumulativeLevelSpace κ h q N hκ hh) ≤ (18*q)*2^N := by
  have hcum :=
    BrownianSharp.AlignmentPaperCumulativeFiltration.cumulativeFiltration_finrank_le
      (fun n => levelSpace κ h n q hκ hh)
      (fun n => levelSpace_finiteDimensional κ h n q hκ hh)
      (D := 9*q) (fun n => levelSpace_finrank_le_dyadic κ h n q hκ hh) N
  calc
    Module.finrank ℝ ↥(cumulativeLevelSpace κ h q N hκ hh) ≤ 2*(9*q)*2^N := by
      change Module.finrank ℝ
        ↥(BrownianSharp.AlignmentPaperCumulativeFiltration.cumulativeFiltration
          (fun n => levelSpace κ h n q hκ hh) N) ≤ 2*(9*q)*2^N
      exact hcum
    _ = (18*q)*2^N := by ring

def cumulativeFiltrationFamily (κ h : ℝ) (q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) : ℕ → Submodule ℝ (SpectralAxisL2 κ h) :=
  fun N => cumulativeLevelSpace κ h q N hκ hh

theorem cumulativeGradedFrame_orthonormal (κ h : ℝ) (q N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    Orthonormal ℝ (gradedFrame (cumulativeFiltrationFamily κ h q hκ hh)
      (fun n => cumulativeLevelSpace_finiteDimensional κ h q n hκ hh) N) :=
  gradedFrame_orthonormal (cumulativeFiltrationFamily κ h q hκ hh)
    (fun n => cumulativeLevelSpace_finiteDimensional κ h q n hκ hh)
    (fun n => cumulativeLevelSpace_nested κ h q n hκ hh) N

theorem cumulativeGradeEnergy_le_of_projection_residual
    (κ h : ℝ) (q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    [∀ N, (cumulativeLevelSpace κ h q N hκ hh).HasOrthogonalProjection]
    {ι : Type*} (K : ι → SpectralAxisL2 κ h) (A C beta : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hfather : ∀ i, ‖K i‖^2 ≤ A)
    (hres : ∀ i N,
      ‖K i - (cumulativeLevelSpace κ h q N hκ hh).starProjection (K i)‖ ≤
        C * ((2:ℝ)^(-beta))^N) :
    ∀ i g,
      (∑ j : GradeIndex (cumulativeFiltrationFamily κ h q hκ hh) g,
        ⟪K i, gradeFamily (cumulativeFiltrationFamily κ h q hκ hh)
          (fun n => cumulativeLevelSpace_finiteDimensional κ h q n hκ hh) g j⟫^2) ≤
        (A + C^2/(((2:ℝ)^(-beta))^2)) * (((2:ℝ)^(-beta))^2)^g := by
  exact grade_energy_le_of_uniform_projection_residual
    (cumulativeFiltrationFamily κ h q hκ hh)
    (fun n => cumulativeLevelSpace_finiteDimensional κ h q n hκ hh)
    K A C ((2:ℝ)^(-beta)) hA hC
    (Real.rpow_pos_of_pos (by norm_num) _)
    hfather hres

end BrownianSharp.AlignmentPaperMaternSpectralFiltration
