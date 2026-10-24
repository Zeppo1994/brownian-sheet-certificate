import BrownianSharp.AlignmentIntegerFractionalApproximationLower
import BrownianSharp.AlignmentHilbertOrthogonalImages
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Selected orthogonal singular vectors in each dyadic sine block for the
actual second-order Riemann--Liouville operator. -/

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentIntegerTwoSelectedBlock

open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentOrdinaryIntegrationLower
open BrownianSharp.AlignmentHilbertOrthogonalImages

/-- The good-source range for the order-two sine block. -/
noncomputable def blockSource (K D : ℕ) : Submodule ℝ UnitL2 :=
  LinearMap.range ((sineSecondSourceMap K D).comp (sineJetKernel K D).subtype)

noncomputable def blockOperator (K D : ℕ) :
    blockSource K D →L[ℝ] UnitL2 := by
  let T : UnitL2 →L[ℝ] UnitL2 := profileToL2.comp integerTwoOperator
  exact T.comp (blockSource K D).subtypeL

/-- In every dyadic block there are exactly `2^s` orthonormal source vectors
whose actual order-two RL images are pairwise orthogonal in the target L²
space, with the stated common lower norm. -/
theorem integerTwoBlock_selected_orthogonal_frame (s : ℕ) :
    ∃ e : Fin (2^s) → UnitL2,
      Orthonormal ℝ e ∧
      (∀ i, e i ∈ blockSource (2^(s+1)) (2^(s+1))) ∧
      (∀ i j, i ≠ j →
        ⟪profileToL2 (integerTwoOperator (e i)),
          profileToL2 (integerTwoOperator (e j))⟫ = 0) ∧
      (∀ i, ((halfFrequency (2^(s+2)))^2)⁻¹ ≤
        ‖profileToL2 (integerTwoOperator (e i))‖) := by
  classical
  let K : ℕ := 2^(s+1)
  let D : ℕ := 2^(s+1)
  let E : Submodule ℝ UnitL2 := blockSource K D
  haveI : FiniteDimensional ℝ E := by
    dsimp [E, blockSource]
    exact Module.Finite.range _
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hdimLower : D - 1 ≤ Module.finrank ℝ E := by
    change D - 1 ≤ Module.finrank ℝ (sineJetGoodSource K D)
    exact sineJetGoodSource_finrank_lower K D
  have hselect : 2^s ≤ Module.finrank ℝ E := by
    have hpow : D = 2^s * 2 := by
      calc
        D = 2^(s+1) := by rfl
        _ = 2^s * 2 := by rw [pow_succ]
    have hlower' : 2^s * 2 - 1 ≤ Module.finrank ℝ E := by
      simpa [hpow] using hdimLower
    omega
  have hdim : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  let T : E →L[ℝ] UnitL2 := blockOperator K D
  let σ : ℝ := ((halfFrequency (K+D))^2)⁻¹
  have hσnonneg : 0 ≤ σ := by dsimp [σ]; positivity
  have hlower : ∀ v : E, ‖(v : UnitL2)‖ = 1 → σ ≤ ‖T v‖ := by
    intro v hv
    have hmem : (v : UnitL2) ∈ LinearMap.range
        ((sineSecondSourceMap K D).comp (sineJetKernel K D).subtype) := v.property
    obtain ⟨csub, hcsub⟩ := LinearMap.mem_range.mp hmem
    let c : Fin D → ℝ := csub.val
    have hc : c ∈ sineJetKernel K D := csub.property
    have hsource : sineSecondSourceMap K D c = (v : UnitL2) := by
      simpa [c, blockSource, E] using hcsub
    have hnorm : ‖sineSecondSourceMap K D c‖ = 1 := by
      simpa [hsource] using hv
    have henergy := integerTwoOperator_energy_lower_of_jet K D hDpos c hc hnorm
    have hnormsq : σ^2 ≤ ‖T v‖^2 := by
      have hIdent : T v = profileToL2 (integerTwoOperator (sineSecondSourceMap K D c)) := by
        simp [T, blockOperator, hsource]
      rw [hIdent]
      dsimp [σ]
      have hInt := integral_unitTargetMeasure
        (integerTwoOperator (sineSecondSourceMap K D c))
      rw [hInt] at henergy
      exact henergy
    have hTnonneg : 0 ≤ ‖T v‖ := norm_nonneg _
    nlinarith [sq_nonneg (σ - ‖T v‖)]
  obtain ⟨b, hborth, hbnorm⟩ := exists_orthogonal_image_basis_of_lower T σ hlower
  let emb : Fin (2^s) → Fin (Module.finrank ℝ E) := fun i => Fin.castLE hselect i
  let e : Fin (2^s) → UnitL2 := fun i => (b (emb i) : E)
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · apply b.orthonormal.comp emb
    intro i j hij
    apply Fin.ext
    simpa [emb] using congrArg Fin.val hij
  · intro i
    exact (b (emb i)).property
  · intro i j hij
    have h := hborth (emb i) (emb j) (by
      intro heq
      apply hij
      exact Fin.ext (by simpa [emb] using congrArg Fin.val heq))
    simpa [e, T, blockOperator] using h
  · intro i
    have h := hbnorm (emb i)
    have hfreq : K + D = 2^(s+2) := by
      dsimp [K, D]
      simp [pow_add, pow_succ]
      ring
    simpa [σ, T, blockOperator, K, D, e, hfreq] using h


/-- Source vectors in disjoint sine blocks are orthogonal before applying the
order-two operator as well. -/
theorem sineSecondSourceMap_disjoint_block_orthogonal
    (K D K' D' : ℕ) (c : Fin D → ℝ) (e : Fin D' → ℝ)
    (hdisj : ∀ i j : ℕ, i < D → j < D' → K+i ≠ K'+j) :
    ⟪sineSecondSourceMap K D c, sineSecondSourceMap K' D' e⟫ = 0 := by
  have hcross (i : Fin D) (j : Fin D') :
      ⟪shiftedSineMode K i.val, shiftedSineMode K' j.val⟫ = 0 := by
    have hs := sineSource_orthonormal
    have hneq := hdisj i.val j.val i.isLt j.isLt
    have hz := hs.inner_eq_zero hneq
    simpa [shiftedSineMode]
      using hz
  simp [sineSecondSourceMap, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, hcross]

/-- Any two source vectors supported in distinct dyadic blocks are orthogonal. -/
theorem integerTwoBlock_source_cross_orthogonal {s t : ℕ} (hst : s < t)
    (u v : UnitL2)
    (hu : u ∈ blockSource (2^(s+1)) (2^(s+1)))
    (hv : v ∈ blockSource (2^(t+1)) (2^(t+1))) :
    ⟪u, v⟫ = 0 := by
  classical
  let K := 2^(s+1)
  let D := 2^(s+1)
  let K' := 2^(t+1)
  let D' := 2^(t+1)
  obtain ⟨cs, hcs⟩ := LinearMap.mem_range.mp hu
  obtain ⟨ct, hct⟩ := LinearMap.mem_range.mp hv
  let c := cs.val
  let e := ct.val
  have hsour : sineSecondSourceMap K D c = u := by
    simpa [c, blockSource, K, D] using hcs
  have htour : sineSecondSourceMap K' D' e = v := by
    simpa [e, blockSource, K', D'] using hct
  have hsum : K + D = 2^(s+2) := by
    calc
      K + D = 2^(s+1) + 2^(s+1) := by simp [K, D]
      _ = 2^(s+1) * 2 := by ring
      _ = 2^(s+2) := by
        rw [show s+2 = (s+1)+1 by omega, pow_succ]
        rw [pow_succ]
        ring
  have hwindow : K + D ≤ K' := by
    have hexp : s+2 ≤ t+1 := by omega
    have hpow : 2^(s+2) ≤ 2^(t+1) := Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
    rw [hsum, show K' = 2^(t+1) by rfl]
    exact hpow
  have hdisj : ∀ a b : ℕ, a < D → b < D' → K+a ≠ K'+b := by
    intro a b ha hb heq
    have hleft : K+a < K+D := by omega
    have hright : K' ≤ K'+b := by omega
    omega
  rw [← hsour, ← htour]
  exact sineSecondSourceMap_disjoint_block_orthogonal K D K' D' c e hdisj

/-- Images selected from distinct dyadic sine blocks remain orthogonal because
`R₂` maps each block into its disjoint output-frequency window. -/
theorem integerTwoBlock_selected_cross_orthogonal {s t : ℕ} (hst : s < t)
    (es : Fin (2^s) → UnitL2) (et : Fin (2^t) → UnitL2)
    (hes : ∀ i, es i ∈ blockSource (2^(s+1)) (2^(s+1)))
    (het : ∀ j, et j ∈ blockSource (2^(t+1)) (2^(t+1)))
    (i : Fin (2^s)) (j : Fin (2^t)) :
    ⟪profileToL2 (integerTwoOperator (es i)),
      profileToL2 (integerTwoOperator (et j))⟫ = 0 := by
  classical
  let K := 2^(s+1)
  let D := 2^(s+1)
  let K' := 2^(t+1)
  let D' := 2^(t+1)
  obtain ⟨cs, hcs⟩ := LinearMap.mem_range.mp (hes i)
  obtain ⟨ct, hct⟩ := LinearMap.mem_range.mp (het j)
  let c := cs.val
  let e := ct.val
  have hc : c ∈ sineJetKernel K D := cs.property
  have he : e ∈ sineJetKernel K' D' := ct.property
  have hsour : sineSecondSourceMap K D c = es i := by
    simpa [c, blockSource, K, D] using hcs
  have htour : sineSecondSourceMap K' D' e = et j := by
    simpa [e, blockSource, K', D'] using hct
  have hsum : K + D = 2^(s+2) := by
    calc
      K + D = 2^(s+1) + 2^(s+1) := by simp [K, D]
      _ = 2^(s+1) * 2 := by ring
      _ = 2^(s+2) := by
        rw [show s+2 = (s+1)+1 by omega, pow_succ]
        rw [pow_succ]
        ring
  have hwindow : K + D ≤ K' := by
    have hpow : 2^(s+2) ≤ 2^(t+1) := by
      have hexp : s+2 ≤ t+1 := by omega
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
    rw [hsum, show K' = 2^(t+1) by rfl]
    exact hpow
  have hdisj : ∀ a b : ℕ, a < D → b < D' → K+a ≠ K'+b := by
    intro a b ha hb heq
    have hleft : K+a < K+D := by omega
    have hright : K' ≤ K'+b := by omega
    omega
  rw [← hsour, ← htour]
  exact integerTwoL2Operator_disjoint_block_orthogonal K D K' D' c e hc he hdisj


/-- A fixed choice of selected source frame in every dyadic frequency block. -/
noncomputable def selectedBlockFrame (s : ℕ) : Fin (2^s) → UnitL2 :=
  Classical.choose (integerTwoBlock_selected_orthogonal_frame s)

theorem selectedBlockFrame_orthonormal (s : ℕ) :
    Orthonormal ℝ (selectedBlockFrame s) :=
  (Classical.choose_spec (integerTwoBlock_selected_orthogonal_frame s)).1

theorem selectedBlockFrame_mem (s : ℕ) (i : Fin (2^s)) :
    selectedBlockFrame s i ∈ blockSource (2^(s+1)) (2^(s+1)) :=
  (Classical.choose_spec (integerTwoBlock_selected_orthogonal_frame s)).2.1 i

theorem selectedBlockFrame_image_pairwise (s : ℕ) (i j : Fin (2^s))
    (hij : i ≠ j) :
    ⟪profileToL2 (integerTwoOperator (selectedBlockFrame s i)),
      profileToL2 (integerTwoOperator (selectedBlockFrame s j))⟫ = 0 :=
  (Classical.choose_spec
    (integerTwoBlock_selected_orthogonal_frame s)).2.2.1 i j hij

theorem selectedBlockFrame_image_norm_lower (s : ℕ) (i : Fin (2^s)) :
    ((halfFrequency (2^(s+2)))^2)⁻¹ ≤
      ‖profileToL2 (integerTwoOperator (selectedBlockFrame s i))‖ :=
  (Classical.choose_spec (integerTwoBlock_selected_orthogonal_frame s)).2.2.2 i

theorem selectedBlockFrame_source_cross_orthogonal {s t : ℕ} (hst : s ≠ t)
    (i : Fin (2^s)) (j : Fin (2^t)) :
    ⟪selectedBlockFrame s i, selectedBlockFrame t j⟫ = 0 := by
  rcases lt_or_gt_of_ne hst with h | h
  · exact integerTwoBlock_source_cross_orthogonal h _ _
      (selectedBlockFrame_mem s i) (selectedBlockFrame_mem t j)
  · rw [real_inner_comm]
    exact integerTwoBlock_source_cross_orthogonal h _ _
      (selectedBlockFrame_mem t j) (selectedBlockFrame_mem s i)

theorem selectedBlockFrame_image_cross_orthogonal {s t : ℕ} (hst : s ≠ t)
    (i : Fin (2^s)) (j : Fin (2^t)) :
    ⟪profileToL2 (integerTwoOperator (selectedBlockFrame s i)),
      profileToL2 (integerTwoOperator (selectedBlockFrame t j))⟫ = 0 := by
  rcases lt_or_gt_of_ne hst with h | h
  · exact integerTwoBlock_selected_cross_orthogonal h
      (selectedBlockFrame s) (selectedBlockFrame t)
      (selectedBlockFrame_mem s) (selectedBlockFrame_mem t) i j
  · rw [real_inner_comm]
    exact integerTwoBlock_selected_cross_orthogonal h
      (selectedBlockFrame t) (selectedBlockFrame s)
      (selectedBlockFrame_mem t) (selectedBlockFrame_mem s) j i

end BrownianSharp.AlignmentIntegerTwoSelectedBlock
