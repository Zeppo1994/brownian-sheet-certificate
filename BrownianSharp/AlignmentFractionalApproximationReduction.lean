import BrownianSharp.AlignmentFractionalPaddingPermutation
import BrownianSharp.AlignmentApproximationNumberIdeal

/-! Bounded-operator reduction from anisotropic orders to their least-smooth coordinates. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal
namespace BrownianSharp.AlignmentFractionalApproximationReduction
open AlignmentFractionalTensorOperator AlignmentFractionalTensor AlignmentFractionalPadding
  AlignmentFractionalPaddingPermutation AlignmentFractionalApproximationNumbers
  AlignmentApproximationNumberIdeal

def activeSourceCLM (ν e : ℕ) :
    CameronMartin.UnitCubeL2 ν →L[ℝ] CameronMartin.UnitCubeL2 (ν+e) := by
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  exact (Lp.compMeasurePreservingₗᵢ ℝ (activeCoordinates ν e)
    (by simpa [CameronMartin.UnitCubeL2,intervalCubeMeasure,unitCube_measure_eq_pi]
      using activeCoordinates_measurePreserving ν e)).toContinuousLinearMap

@[simp] theorem activeSourceCLM_apply (ν e : ℕ) (g : CameronMartin.UnitCubeL2 ν) :
    activeSourceCLM ν e g = liftActiveSource ν e g := rfl

def reindexSourceCLM {d : ℕ} (e : Fin d ≃ Fin d) :
    CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d := by
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  exact (Lp.compMeasurePreservingₗᵢ ℝ (coordinateBackEquiv e)
    (reindexCoordinatesMP e)).toContinuousLinearMap

@[simp] theorem reindexSourceCLM_apply {d : ℕ} (e : Fin d ≃ Fin d)
    (g : CameronMartin.UnitCubeL2 d) :
    reindexSourceCLM e g = reindexSource e g := rfl

theorem fractionalTensorRL_reindex_operator {d : ℕ} (e : Fin d ≃ Fin d)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i) :
    fractionalTensorRL (reindexOrders e a) (fun i => ha (e i)) =
      (reindexOutput e).comp ((fractionalTensorRL a ha).comp (reindexSourceCLM e.symm)) := by
  ext g t
  have h := fractionalTensorRL_reindex_apply e.symm
    (reindexOrders e a) (fun i => ha (e i)) g (reindexAnchor e t)
  simpa [reindexOrders,reindexSourceCLM_apply] using h.symm

theorem fractionalTensorRL_padded_operator {ν e : ℕ} (r : ℝ)
    (hr : 1/2 < r) (b : Fin e → ℝ) (hb : ∀ i, 1/2 < b i) :
    ((inactivePaddingFactor b)⁻¹ • (paddedRestriction (ν:=ν) (e:=e))).comp
      ((fractionalTensorRL (paddedOrders (ν:=ν) (e:=e) r b) (paddedOrders_gt (ν:=ν) hr hb)).comp
        (activeSourceCLM ν e)) =
      fractionalTensorRL (fun _ : Fin ν => r) (fun _ => hr) := by
  have hc : inactivePaddingFactor b ≠ 0 := ne_of_gt (inactivePaddingFactor_pos b hb)
  ext g t
  change (inactivePaddingFactor b)⁻¹ *
    fractionalTensorRL (paddedOrders (ν:=ν) (e:=e) r b) (paddedOrders_gt (ν:=ν) hr hb)
      (liftActiveSource ν e g) (paddedAnchor t) = _
  rw [fractionalTensorRL_padding_apply r hr b hb]
  field_simp

theorem approximationNumber_comp_three_le
    {X Y Z W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (V : Z →L[ℝ] W) (T : Y →L[ℝ] Z) (U : X →L[ℝ] Y)
    {k : ℕ} (hk : 0 < k) :
    approximationNumber (V.comp (T.comp U)) k ≤
      ENNReal.ofReal (‖V‖*‖U‖) * approximationNumber T k := by
  calc
    _ ≤ ENNReal.ofReal ‖V‖ * approximationNumber (T.comp U) k :=
      approximationNumber_comp_le_left V (T.comp U) hk
    _ ≤ ENNReal.ofReal ‖V‖ * (approximationNumber T k * ENNReal.ofReal ‖U‖) := by
      gcongr
      exact approximationNumber_comp_le_right T U hk
    _ = _ := by
      rw [ENNReal.ofReal_mul (norm_nonneg _)]
      ac_rfl

/-- The actual isotropic minimum-order operator factors through the actual
padded anisotropic operator by bounded source and target maps. -/
theorem padded_approximationNumber_reduction {ν e : ℕ} (r : ℝ)
    (hr : 1/2 < r) (b : Fin e → ℝ) (hb : ∀ i, 1/2 < b i) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      approximationNumber (fractionalTensorRL (fun _ : Fin ν => r) (fun _ => hr)) k ≤
        ENNReal.ofReal C *
          approximationNumber (fractionalTensorRL (paddedOrders (ν:=ν) (e:=e) r b) (paddedOrders_gt (ν:=ν) hr hb)) k := by
  let V := (inactivePaddingFactor b)⁻¹ • (paddedRestriction (ν:=ν) (e:=e))
  let U := activeSourceCLM ν e
  let C := 1 + ‖V‖ * ‖U‖
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro k hk
  have h := approximationNumber_comp_three_le V
    (fractionalTensorRL (paddedOrders (ν:=ν) (e:=e) r b) (paddedOrders_gt (ν:=ν) hr hb)) U hk
  rw [show V.comp ((fractionalTensorRL (paddedOrders (ν:=ν) (e:=e) r b) (paddedOrders_gt (ν:=ν) hr hb)).comp U) =
      fractionalTensorRL (fun _ : Fin ν => r) (fun _ => hr) from
        fractionalTensorRL_padded_operator r hr b hb] at h
  refine h.trans ?_
  gcongr
  dsimp [C]
  linarith


/-- Minimum-multiplicity reduction, including coordinate permutations. -/
theorem minimum_approximationNumber_reduction {ν e : ℕ}
    (a : Fin (ν+e) → ℝ) (ha : ∀ i, 1/2 < a i) (r : ℝ)
    (hr : 1/2 < r) (hm : Latest.minimumMultiplicity a r ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      approximationNumber (fractionalTensorRL (fun _ : Fin ν => r) (fun _ => hr)) k ≤
        ENNReal.ofReal C * approximationNumber (fractionalTensorRL a ha) k := by
  classical
  let ep := minimumCoordinatePermutation a r hm.2
  let b : Fin e → ℝ := fun j => reindexOrders ep a (Fin.natAdd ν j)
  have hb : ∀ j, 1/2 < b j := fun j => ha (ep (Fin.natAdd ν j))
  have hp : reindexOrders ep a = paddedOrders (ν:=ν) r b :=
    reindexOrders_eq_paddedOrders a r hm.2
  obtain ⟨Cp,hCp,hpad⟩ := padded_approximationNumber_reduction (ν:=ν) r hr b hb
  let V := reindexOutput ep
  let U := reindexSourceCLM ep.symm
  let Cr := 1 + ‖V‖*‖U‖
  have hCr : 0 < Cr := by dsimp [Cr]; positivity
  refine ⟨Cp*Cr,mul_pos hCp hCr,?_⟩
  intro k hk
  have hp' : approximationNumber
      (fractionalTensorRL (fun _ : Fin ν => r) (fun _ => hr)) k ≤
      ENNReal.ofReal Cp * approximationNumber
        (fractionalTensorRL (reindexOrders ep a) (fun i => ha (ep i))) k := by
    simpa only [hp] using hpad k hk
  have hr' : approximationNumber
      (fractionalTensorRL (reindexOrders ep a) (fun i => ha (ep i))) k ≤
      ENNReal.ofReal Cr * approximationNumber (fractionalTensorRL a ha) k := by
    rw [fractionalTensorRL_reindex_operator ep a ha]
    refine (approximationNumber_comp_three_le V (fractionalTensorRL a ha) U hk).trans ?_
    gcongr
    dsimp [Cr]
    linarith
  calc
    _ ≤ ENNReal.ofReal Cp * approximationNumber
        (fractionalTensorRL (reindexOrders ep a) (fun i => ha (ep i))) k := hp'
    _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal Cr *
        approximationNumber (fractionalTensorRL a ha) k) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hCp.le]; ac_rfl

/-- Every anisotropic order vector reduces to the isotropic operator on the
coordinates attaining its minimum. The multiplier is fixed before the index. -/
theorem general_minimum_approximationNumber_reduction {d ν : ℕ}
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i) (r : ℝ)
    (hr : 1/2 < r) (hm : Latest.minimumMultiplicity a r ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      approximationNumber (fractionalTensorRL (fun _ : Fin ν => r) (fun _ => hr)) k ≤
        ENNReal.ofReal C * approximationNumber (fractionalTensorRL a ha) k := by
  have hνd : ν ≤ d := by
    have hh := Finset.card_le_card
      (Finset.filter_subset (s:=Finset.univ) (p:=fun i : Fin d => a i = r))
    simpa only [hm.2, Finset.card_univ,Fintype.card_fin] using hh
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le hνd
  exact minimum_approximationNumber_reduction a ha r hr hm

end BrownianSharp.AlignmentFractionalApproximationReduction
