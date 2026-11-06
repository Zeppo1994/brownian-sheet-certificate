import BrownianSharp.AlignmentPaperAnchoredLpFaceCoefficients
import BrownianSharp.AlignmentPaperFiniteReflectionAverage
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentPaperAnchoredLpParityFourier

open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpReflection
open BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
open BrownianSharp.AlignmentPaperAnchoredLpSourceFourier
open BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentFractionalTensor
open HaarQuarter

/-- Negating a circle point exchanges its half-open representatives. -/
theorem circleIcoRepresentative_neg_eq_one_sub_Ioc (x : UnitAddCircle) :
    circleIcoRepresentative (-x) = 1 - circleIocRepresentative x := by
  let r := circleIocRepresentative x
  have hr : r ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [r, circleIocRepresentative] using
      (AddCircle.equivIoc (1:ℝ) 0 x).property
  have hcoe : (r : UnitAddCircle) = x := by
    simp [r, circleIocRepresentative]
  have hneg : ((1-r : ℝ) : UnitAddCircle) = -x := by
    rw [← hcoe]
    simp [sub_eq_add_neg]
  have hr' : 1-r ∈ Set.Ico (0:ℝ) (0+1) := by
    constructor <;> dsimp [r] at hr ⊢ <;> linarith [hr.1, hr.2]
  have hrep : AddCircle.equivIco (1:ℝ) 0 (-x) = ⟨1-r, hr'⟩ := by
    rw [← hneg]
    exact (AddCircle.equivIco (1:ℝ) 0).right_inv ⟨1-r, hr'⟩
  have hv := congrArg Subtype.val hrep
  simpa [circleIcoRepresentative, r] using hv

/-- Away from zero, the two endpoint conventions give the same representative. -/
theorem circleIcoRepresentative_eq_Ioc_of_ne_zero
    (x : UnitAddCircle) (hx : x ≠ 0) :
    circleIcoRepresentative x = circleIocRepresentative x := by
  have hrco := circleIcoRepresentative_mem x
  have hpos : circleIcoRepresentative x ≠ 0 := by
    intro hz
    apply hx
    have hcoe : (circleIcoRepresentative x : UnitAddCircle) = x := by
      simp [circleIcoRepresentative]
    rw [hz] at hcoe
    simpa using hcoe.symm
  have hrIoc : circleIcoRepresentative x ∈ Set.Ioc (0:ℝ) (0+1) := by
    constructor
    · exact lt_of_le_of_ne hrco.1 (Ne.symm hpos)
    · simpa using hrco.2.le
  have hrio : circleIocRepresentative x ∈ Set.Ioc (0:ℝ) (0+1) := by
    simpa [circleIocRepresentative] using
      (AddCircle.equivIoc (1:ℝ) 0 x).property
  have hcoe₁ : (circleIcoRepresentative x : UnitAddCircle) = x := by
    simp [circleIcoRepresentative]
  have hcoe₂ : (circleIocRepresentative x : UnitAddCircle) = x := by
    simp [circleIocRepresentative]
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hrIoc hrio).mp
    (hcoe₁.trans hcoe₂.symm)

/-- The triangular fold is invariant under circle reflection away from the
representative endpoint; this is the form needed almost everywhere. -/
theorem triangleWave_neg_of_ne_zero (x : UnitAddCircle) (hx : x ≠ 0) :
    triangleWave (-x) = triangleWave x := by
  rw [triangleWave_eq_fold_representative, triangleWave_eq_fold_representative,
    circleIcoRepresentative_neg_eq_one_sub_Ioc]
  let r := circleIocRepresentative x
  have hA : 2 * (1-r) = 2-2*r := by ring
  have hB : 2-2*(1-r) = 2*r := by ring
  rw [hA]
  have hfold : foldUnitInterval (2-2*r) = foldUnitInterval (2*r) := by
    rw [foldUnitInterval, foldUnitInterval]
    have hC : 2-(2-2*r) = 2*r := by ring
    rw [hC, min_comm]
  rw [hfold]
  have hrio : circleIocRepresentative x ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [circleIocRepresentative] using
      (AddCircle.equivIoc (1:ℝ) 0 x).property
  have hrco := circleIcoRepresentative_mem x
  have hrco_pos : circleIcoRepresentative x ≠ 0 := by
    intro hz
    apply hx
    have hcoe : (circleIcoRepresentative x : UnitAddCircle) = x := by
      simp [circleIcoRepresentative]
    rw [hz] at hcoe
    simpa using hcoe.symm
  have hrIoc : circleIcoRepresentative x ∈ Set.Ioc (0:ℝ) 1 := by
    constructor
    · exact lt_of_le_of_ne hrco.1 (Ne.symm hrco_pos)
    · exact hrco.2.le
  have hrIoc' : circleIcoRepresentative x ∈ Set.Ioc (0:ℝ) (0+1) := by
    simpa using hrIoc
  have hrio' : circleIocRepresentative x ∈ Set.Ioc (0:ℝ) (0+1) := by
    simpa using hrio
  have hcoe₁ : (circleIcoRepresentative x : UnitAddCircle) = x := by
    simp [circleIcoRepresentative]
  have hcoe₂ : (circleIocRepresentative x : UnitAddCircle) = x := by
    simp [circleIocRepresentative]
  have hreps : circleIcoRepresentative x = circleIocRepresentative x :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ioc hrIoc' hrio').mp
      (hcoe₁.trans hcoe₂.symm)
  rw [hreps]

/-- The half-circle parity sign changes under reflection except at its two
boundary points. -/
def anchoredHalfSign (x : UnitAddCircle) : ℝ :=
  if circleIocRepresentative x ≤ 1/2 then 1 else -1

theorem anchoredHalfSign_neg_of_ne_boundary
    (x : UnitAddCircle) (hx0 : x ≠ 0)
    (hhalf : circleIocRepresentative x ≠ 1/2) :
    anchoredHalfSign (-x) = -anchoredHalfSign x := by
  have hneg : -x ≠ 0 := by
    intro h
    apply hx0
    have hh := congrArg Neg.neg h
    simpa using hh
  have hrep : circleIocRepresentative (-x) = 1 - circleIocRepresentative x := by
    calc
      circleIocRepresentative (-x) = circleIcoRepresentative (-x) :=
        (circleIcoRepresentative_eq_Ioc_of_ne_zero (-x) hneg).symm
      _ = 1 - circleIocRepresentative x := circleIcoRepresentative_neg_eq_one_sub_Ioc x
  unfold anchoredHalfSign
  rw [hrep]
  by_cases hr : circleIocRepresentative x ≤ 1/2
  · have hlt : circleIocRepresentative x < 1/2 := lt_of_le_of_ne hr hhalf
    have hgt : 1 - circleIocRepresentative x > 1/2 := by linarith
    have hr' : circleIocRepresentative x ≤ (2:ℝ)⁻¹ := by nlinarith [hr]
    have hnot : ¬ 1 ≤ (2:ℝ)⁻¹ + circleIocRepresentative x := by nlinarith
    simp [hnot, hr']
  · have hgt : circleIocRepresentative x > 1/2 := lt_of_not_ge hr
    have hlt : 1 - circleIocRepresentative x < 1/2 := by linarith
    have hr' : ¬ circleIocRepresentative x ≤ (2:ℝ)⁻¹ := by nlinarith
    have hyes : 1 ≤ (2:ℝ)⁻¹ + circleIocRepresentative x := by nlinarith
    simp [hyes, hr']

/-- Reflect an arbitrary finite set of torus coordinates. -/
def reflectFaceCoordinates {d : ℕ} (J : Finset (Fin d))
    (x : UnitAddTorus (Fin d)) : UnitAddTorus (Fin d) :=
  fun i => if i ∈ J then -x i else x i

/-- Coordinatewise circle reflections preserve product Haar measure. -/
theorem measurePreserving_reflectFaceCoordinates {d : ℕ}
    (J : Finset (Fin d)) :
    MeasurePreserving (reflectFaceCoordinates J)
      (volume : Measure (UnitAddTorus (Fin d)))
      (volume : Measure (UnitAddTorus (Fin d))) := by
  let μc : Measure UnitAddCircle := AddCircle.haarAddCircle
  have hneg : MeasurePreserving (fun x : UnitAddCircle => -x) μc μc :=
    Measure.measurePreserving_neg μc
  let f : Fin d → UnitAddCircle → UnitAddCircle :=
    fun i y => if i ∈ J then -y else y
  have hf : ∀ i, MeasurePreserving (f i) μc μc := by
    intro i
    by_cases hi : i ∈ J
    · simpa [f, hi] using hneg
    · have hid : MeasurePreserving (fun y : UnitAddCircle => y) μc μc := by
        convert MeasurePreserving.id μc using 1 <;> rfl
      simpa [f, hi] using hid
  have hpi : MeasurePreserving (reflectFaceCoordinates J)
      (Measure.pi (fun _ : Fin d => μc))
      (Measure.pi (fun _ : Fin d => μc)) := by
    change MeasurePreserving
      (fun a : Fin d → UnitAddCircle => fun i => if i ∈ J then -a i else a i)
      (Measure.pi (fun _ : Fin d => μc)) (Measure.pi (fun _ : Fin d => μc))
    exact measurePreserving_pi (fun _ : Fin d => μc) (fun _ : Fin d => μc) hf
  simpa [unitAddTorus_volume_eq_productHaar, unitAddCircle_volume_eq_haar] using hpi

/-- The vector of Ioc representatives transports torus Haar to the product
of restricted Lebesgue measures on the unit interval. -/
def faceIocCoordinates {d : ℕ} (x : UnitAddTorus (Fin d)) : Fin d → ℝ :=
  fun i => circleIocRepresentative (x i)

theorem measurePreserving_faceIocCoordinates {d : ℕ} :
    MeasurePreserving (faceIocCoordinates (d := d))
      (volume : Measure (UnitAddTorus (Fin d)))
      (Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioc (0:ℝ) 1))) := by
  let μIoc : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)
  have hcoord : MeasurePreserving circleIocRepresentative
      (volume : Measure UnitAddCircle) μIoc := by
    simpa [μIoc] using measurePreserving_circleIocRepresentative
  have hpi := measurePreserving_pi
      (fun _ : Fin d => (volume : Measure UnitAddCircle))
      (fun _ : Fin d => μIoc)
      (fun _ : Fin d => hcoord)
  change MeasurePreserving
      (fun x : Fin d → UnitAddCircle => fun i => circleIocRepresentative (x i))
      (volume : Measure (Fin d → UnitAddCircle))
      (Measure.pi (fun _ : Fin d => volume.restrict (Set.Ioc (0:ℝ) 1)))
  simpa [faceIocCoordinates, unitAddTorus_volume_eq_productHaar,
    unitAddCircle_volume_eq_haar, μIoc] using hpi

/-- The two reflection-boundary representatives are null in every torus
coordinate. -/
theorem ae_faceIocCoordinate_away_from_boundary {d : ℕ} (i : Fin d) :
    ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))),
      faceIocCoordinates x i ≠ 0 ∧ faceIocCoordinates x i ≠ 1/2 := by
  rw [ae_iff]
  have hneg : {x : UnitAddTorus (Fin d) |
      ¬ (faceIocCoordinates x i ≠ 0 ∧ faceIocCoordinates x i ≠ 1/2)} =
      {x | faceIocCoordinates x i = 0 ∨ faceIocCoordinates x i = 1/2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    tauto
  have hset : {x : UnitAddTorus (Fin d) |
      faceIocCoordinates x i = 0 ∨ faceIocCoordinates x i = 1/2} =
      (faceIocCoordinates (d := d)) ⁻¹'
        {v : Fin d → ℝ | v i = 0 ∨ v i = 1/2} := by
    rfl
  rw [hneg, hset, measurePreserving_faceIocCoordinates.measure_preimage
    ((by measurability : MeasurableSet
      {v : Fin d → ℝ | v i = 0 ∨ v i = 1/2}).nullMeasurableSet)]
  let t : Fin d → Set ℝ := fun j =>
    if j = i then ({0, (1/2 : ℝ)} : Set ℝ) else Set.univ
  have ht : {v : Fin d → ℝ | v i = 0 ∨ v i = 1/2} = Set.pi Set.univ t := by
    ext v
    simp [t]
  rw [ht, Measure.pi_pi]
  have hfinite : ({0, (1/2 : ℝ)} : Set ℝ) = {0} ∪ {1/2} := by
    ext z
    simp [or_comm]
  have hnull' : volume ({0, (1/2 : ℝ)} : Set ℝ) = 0 := by
    rw [hfinite]
    exact measure_union_null (measure_singleton (0:ℝ)) (measure_singleton (1/2:ℝ))
  have hnull : volume (({0, (1/2 : ℝ)} : Set ℝ) ∩ Set.Ioc (0:ℝ) 1) = 0 :=
    measure_mono_null Set.inter_subset_left hnull'
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [t] using hnull

/-- The Ioc representative of the identity point is the right endpoint, so
the coordinate identity itself is also an almost-everywhere exception. -/
theorem ae_faceCoordinate_ne_zero {d : ℕ} (i : Fin d) :
    ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), x i ≠ 0 := by
  rw [ae_iff]
  have hset : {x : UnitAddTorus (Fin d) | x i = 0} =
      (faceIocCoordinates (d := d)) ⁻¹' {v : Fin d → ℝ | v i = 1} := by
    ext x
    constructor
    · intro hx
      change x i = 0 at hx
      have hcoe : (circleIocRepresentative (x i) : UnitAddCircle) = x i := by
        simp [circleIocRepresentative]
      have hcoe1 : ((1:ℝ) : UnitAddCircle) = x i := by
        rw [hx]
        exact AddCircle.coe_period (p := (1:ℝ))
      have hIoc : circleIocRepresentative (x i) ∈ Set.Ioc (0:ℝ) (0+1) := by
        simpa [circleIocRepresentative] using (AddCircle.equivIoc (1:ℝ) 0 (x i)).property
      have h1 : (1:ℝ) ∈ Set.Ioc (0:ℝ) (0+1) := by norm_num
      have := (AddCircle.coe_eq_coe_iff_of_mem_Ioc
        (a := (0:ℝ)) (p := (1:ℝ)) hIoc h1).mp (hcoe.trans hcoe1.symm)
      simpa [faceIocCoordinates] using this
    · intro hx
      have hx' : circleIocRepresentative (x i) = 1 := by
        simpa [faceIocCoordinates] using hx
      have hcoe : (circleIocRepresentative (x i) : UnitAddCircle) = x i := by
        simp [circleIocRepresentative]
      have hxone : x i = ((1:ℝ):UnitAddCircle) :=
        hcoe.symm.trans (congrArg (fun y : ℝ => (y : UnitAddCircle)) hx')
      rw [AddCircle.coe_period] at hxone
      exact hxone
  rw [show {x : UnitAddTorus (Fin d) | ¬x i ≠ 0} =
      {x : UnitAddTorus (Fin d) | x i = 0} by ext x; simp]
  rw [hset, measurePreserving_faceIocCoordinates.measure_preimage
    ((by measurability : MeasurableSet {v : Fin d → ℝ | v i = 1}).nullMeasurableSet)]
  let t : Fin d → Set ℝ := fun j => if j = i then ({1} : Set ℝ) else Set.univ
  have ht : {v : Fin d → ℝ | v i = 1} = Set.pi Set.univ t := by
    ext v
    simp [t]
  rw [ht, Measure.pi_pi]
  have hnull : volume (({1} : Set ℝ) ∩ Set.Ioc (0:ℝ) 1) = 0 :=
    measure_mono_null Set.inter_subset_left (measure_singleton (1:ℝ))
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [t] using hnull

/-- The parity face source is integrable whenever the actual source has
finite `p>1` norm. -/
theorem integrable_anchoredFaceSource {d : ℕ} {p : ℝ}
    (hp : 1 < p) (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    Integrable (fun x =>
      ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℝ) : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
  let fold : UnitAddTorus (Fin d) → (Fin d → ℝ) :=
    fun x i => triangleWave (x i)
  let sign : UnitAddTorus (Fin d) → ℝ := fun x =>
    ∏ i ∈ J, anchoredFaceSignCoordinate x i
  let wt : UnitAddTorus (Fin d) → ℝ := fun x =>
    ∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i))
  let c : ℝ := (2:ℝ)^J.card
  have hfold : MeasurePreserving fold (volume : Measure (UnitAddTorus (Fin d)))
      (cubeMeasure d) := by
    simpa [fold, cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi,
      unitIntervalMeasure] using measurePreserving_foldCoordinates d
  have hgfold : MemLp (((g : (Fin d → ℝ) → ℝ) ∘ fold))
      (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) :=
    (Lp.memLp g).comp_measurePreserving hfold
  have hsignMeas : Measurable sign := by
    classical
    dsimp [sign]
    apply Finset.measurable_prod
    intro i hi
    exact measurable_anchoredFaceSignCoordinate i
  have hwtMeas : Measurable wt := by
    simpa [wt] using measurable_anchoredFaceWeight J
  have hsm : AEStronglyMeasurable
      (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    have hs : AEStronglyMeasurable sign (volume : Measure (UnitAddTorus (Fin d))) :=
      hsignMeas.aestronglyMeasurable
    have hw : AEStronglyMeasurable wt (volume : Measure (UnitAddTorus (Fin d))) :=
      hwtMeas.aestronglyMeasurable
    have hgComp : AEStronglyMeasurable
        (((g : (Fin d → ℝ) → ℝ) ∘ fold)) (volume : Measure (UnitAddTorus (Fin d))) :=
      (Lp.stronglyMeasurable g).aestronglyMeasurable.comp_measurePreserving hfold
    have hrepr : anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) =
        fun x => c * sign x * ((((g : (Fin d → ℝ) → ℝ) ∘ fold) x) * wt x) := by
      funext x
      simp [anchoredFaceSource, sign, wt, c, fold, Function.comp_apply]
    rw [hrepr]
    have hmul := (measurable_const : Measurable
      (fun _ : UnitAddTorus (Fin d) => c)).aestronglyMeasurable.mul
        (hs.mul (hgComp.mul hw))
    convert hmul using 1
    ext x
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint : ∀ x, ‖anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x‖ ≤
      ‖c * ((g : (Fin d → ℝ) → ℝ) ∘ fold) x‖ := by
    intro x
    rw [show anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x =
      c * sign x * ((((g : (Fin d → ℝ) → ℝ) ∘ fold) x) * wt x) by
        simp [anchoredFaceSource, sign, wt, c, fold]]
    have hsign : ‖sign x‖ = 1 := by
      dsimp [sign]
      rw [Finset.abs_prod]
      apply Finset.prod_eq_one
      intro i hi
      simpa only [Real.norm_eq_abs] using anchoredFaceSignCoordinate_norm x i
    have hwt : ‖wt x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (anchoredFaceWeight_bounds J x).1]
      exact (anchoredFaceWeight_bounds J x).2
    rw [norm_mul, norm_mul, norm_mul, hsign]
    have hineq : c * (‖((g : (Fin d → ℝ) → ℝ) (fold x))‖ * ‖wt x‖) ≤
        c * ‖((g : (Fin d → ℝ) → ℝ) (fold x))‖ := by
      calc
        c * (‖((g : (Fin d → ℝ) → ℝ) (fold x))‖ * ‖wt x‖) ≤
            c * (‖((g : (Fin d → ℝ) → ℝ) (fold x))‖ * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hwt (norm_nonneg _)) hc
        _ = c * ‖((g : (Fin d → ℝ) → ℝ) (fold x))‖ := by ring
    simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc] using hineq
  have hmajor : MemLp (c • ((g : (Fin d → ℝ) → ℝ) ∘ fold))
      (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) :=
    hgfold.const_smul c
  have hpoint' : ∀ x, ‖anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x‖ ≤
      ‖(c • ((g : (Fin d → ℝ) → ℝ) ∘ fold)) x‖ := by
    intro x
    simpa [Pi.smul_apply, smul_eq_mul] using hpoint x
  have hmem : MemLp (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ))
      (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := by
    apply hmajor.of_le hsm
    filter_upwards [] with x
    exact hpoint' x
  have hp1 : (1:ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  exact Complex.ofRealCLM.integrable_comp (hmem.integrable hp1)

/-! ## Parity under coordinate reflection -/

/-- Reflecting any subset of the active coordinates preserves the folded
density and changes the parity source by the corresponding sign. -/
theorem anchoredFaceSource_reflect_ae {d : ℕ} (J K : Finset (Fin d))
    (hK : K ⊆ J) (g : (Fin d → ℝ) → ℝ) :
    (fun x : UnitAddTorus (Fin d) =>
      anchoredFaceSource J g (reflectFaceCoordinates K x)) =ᵐ[volume]
      fun x => (-1 : ℝ)^K.card * anchoredFaceSource J g x := by
  classical
  have hgood : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))),
      ∀ i, x i ≠ 0 ∧ circleIocRepresentative (x i) ≠ 1/2 := by
    rw [ae_all_iff]
    intro i
    have ha := ae_faceIocCoordinate_away_from_boundary i
    have hzero : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))), x i ≠ 0 := by
      exact ae_faceCoordinate_ne_zero i
    filter_upwards [hzero, ha] with x hx0 hx
    exact ⟨hx0, hx.2⟩
  filter_upwards [hgood] with x hx
  have hfold (i : Fin d) (hi : i ∈ K) :
      triangleWave ((reflectFaceCoordinates K x) i) = triangleWave (x i) := by
    simp only [reflectFaceCoordinates]
    rw [if_pos hi]
    exact triangleWave_neg_of_ne_zero (x i) (hx i).1
  have hsign (i : Fin d) (hi : i ∈ K) :
      anchoredFaceSignCoordinate (reflectFaceCoordinates K x) i =
        -anchoredFaceSignCoordinate x i := by
    change anchoredHalfSign (if i ∈ K then -(x i) else x i) =
      -anchoredHalfSign (x i)
    rw [if_pos hi]
    exact anchoredHalfSign_neg_of_ne_boundary (x i) (hx i).1 (hx i).2
  have hsignprod :
      (∏ i ∈ J, anchoredFaceSignCoordinate (reflectFaceCoordinates K x) i) =
        (-1 : ℝ)^K.card * ∏ i ∈ J, anchoredFaceSignCoordinate x i := by
    rw [← Finset.prod_sdiff hK, ← Finset.prod_sdiff hK]
    have hactive :
        (∏ i ∈ K, anchoredFaceSignCoordinate (reflectFaceCoordinates K x) i) =
          (-1 : ℝ)^K.card * ∏ i ∈ K, anchoredFaceSignCoordinate x i := by
      rw [Finset.prod_congr rfl (fun i hi => hsign i hi)]
      calc
        (∏ i ∈ K, -anchoredFaceSignCoordinate x i) =
            (∏ i ∈ K, (-1 : ℝ)) * ∏ i ∈ K, anchoredFaceSignCoordinate x i := by
              rw [← Finset.prod_mul_distrib]
              apply Finset.prod_congr rfl
              intro i hi
              ring
        _ = (-1 : ℝ)^K.card * ∏ i ∈ K, anchoredFaceSignCoordinate x i := by
              simp
    have hrest : (∏ i ∈ J \ K, anchoredFaceSignCoordinate (reflectFaceCoordinates K x) i) =
        ∏ i ∈ J \ K, anchoredFaceSignCoordinate x i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hiK : i ∉ K := (Finset.mem_sdiff.mp hi).2
      simp [reflectFaceCoordinates, anchoredFaceSignCoordinate, hiK]
    rw [hrest]
    rw [hactive]
    ring
  have hwt :
      (∏ i ∈ Finset.univ \ J, (1 - triangleWave ((reflectFaceCoordinates K x) i))) =
        ∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiK : i ∉ K := by
      intro hk
      have hiJ : i ∉ J := (Finset.mem_sdiff.mp hi).2
      exact hiJ (hK hk)
    simp [reflectFaceCoordinates, hiK]
  have hg : g (fun i => triangleWave ((reflectFaceCoordinates K x) i)) =
      g (fun i => triangleWave (x i)) := by
    congr 1
    funext i
    by_cases hi : i ∈ K
    · exact hfold i hi
    · simp [reflectFaceCoordinates, hi]
  unfold anchoredFaceSource
  rw [hg, hwt, hsignprod]
  ring

/-- Expanding independently the two choices in each active coordinate. -/
theorem sum_powerset_prod_split {ι R : Type*} [DecidableEq ι] [CommRing R] (s : Finset ι)
    (a b : ι → R) :
    (∑ t ∈ s.powerset,
      (∏ i ∈ t, a i) * (∏ i ∈ s \ t, b i)) =
      ∏ i ∈ s, (a i + b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_powerset_insert hi]
      have hleft :
          (∑ t ∈ s.powerset,
            (∏ j ∈ t, a j) * (∏ j ∈ insert i s \ t, b j)) =
            b i * ∑ t ∈ s.powerset,
              (∏ j ∈ t, a j) * (∏ j ∈ s \ t, b j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hit : i ∉ t := by
          intro hit
          exact hi ((Finset.mem_powerset.mp ht) hit)
        rw [show insert i s \ t = insert i (s \ t) by
          ext j
          by_cases hji : j = i
          · subst j
            simp [hit]
          · simp [hji]]
        simp [Finset.prod_insert, hi]
        ring
      have hright :
          (∑ t ∈ s.powerset,
            (∏ j ∈ insert i t, a j) * (∏ j ∈ insert i s \ insert i t, b j)) =
            a i * ∑ t ∈ s.powerset,
              (∏ j ∈ t, a j) * (∏ j ∈ s \ t, b j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hit : i ∉ t := by
          intro hit
          exact hi ((Finset.mem_powerset.mp ht) hit)
        rw [show insert i s \ insert i t = s \ t by
          ext j
          by_cases hji : j = i
          · subst j
            simp [hi]
          · simp [hji]]
        simp [Finset.prod_insert, hi, hit]
        ring
      rw [hleft, hright, ← add_mul, ih]
      simp [Finset.prod_insert, hi, add_comm]

/-- A circle Fourier character reverses its integer frequency under group
reflection of its argument. -/
theorem circleFourier_negArg (n : ℤ) (x : UnitAddCircle) :
    fourier n (-x) = fourier (-n) x := by
  rw [fourier_apply, fourier_apply]
  congr 1
  rw [zsmul_neg, neg_smul]

/-- Product character under an arbitrary finite coordinate reflection. -/
theorem mFourier_neg_reflect {d : ℕ} (k : Fin d → ℤ)
    (K : Finset (Fin d)) (x : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier (-k) (reflectFaceCoordinates K x) =
      (∏ i ∈ K, fourier (k i) (x i)) *
        ∏ i ∈ Finset.univ \ K, fourier (-k i) (x i) := by
  classical
  have hpoint : ∀ i : Fin d,
      fourier (-k i) (reflectFaceCoordinates K x i) =
        if i ∈ K then fourier (k i) (x i)
          else fourier (-k i) (x i) := by
    intro i
    by_cases hi : i ∈ K
    · simp [reflectFaceCoordinates, hi, circleFourier_negArg]
    · simp [reflectFaceCoordinates, hi]
  change (∏ i : Fin d, fourier (-k i) (reflectFaceCoordinates K x i)) = _
  have hprod :
      (∏ i : Fin d, fourier (-k i) (reflectFaceCoordinates K x i)) =
        ∏ i : Fin d, if i ∈ K then fourier (k i) (x i)
          else fourier (-k i) (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hpoint i
  rw [hprod]
  calc
    (∏ i : Fin d, if i ∈ K then fourier (k i) (x i)
      else fourier (-k i) (x i)) =
        (∏ i ∈ Finset.univ \ K, if i ∈ K then fourier (k i) (x i)
          else fourier (-k i) (x i)) *
        ∏ i ∈ K, if i ∈ K then fourier (k i) (x i)
          else fourier (-k i) (x i) := by
            rw [← Finset.prod_sdiff (Finset.subset_univ K)]
    _ = (∏ i ∈ Finset.univ \ K, fourier (-k i) (x i)) *
        ∏ i ∈ K, fourier (k i) (x i) := by
          have hrest :
              (∏ i ∈ Finset.univ \ K,
                if i ∈ K then fourier (k i) (x i) else fourier (-k i) (x i)) =
              ∏ i ∈ Finset.univ \ K, fourier (-k i) (x i) := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [(Finset.mem_sdiff.mp hi).2]
          have hactive :
              (∏ i ∈ K, if i ∈ K then fourier (k i) (x i)
                else fourier (-k i) (x i)) = ∏ i ∈ K, fourier (k i) (x i) := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [hi]
          rw [hrest, hactive]
    _ = (∏ i ∈ K, fourier (k i) (x i)) *
        ∏ i ∈ Finset.univ \ K, fourier (-k i) (x i) := by ac_rfl

/-- Averaging the reflected torus characters over every active face produces
the product of the active character differences. -/
theorem sum_reflectedFourierCharacters {d : ℕ} (k : Fin d → ℤ)
    (J : Finset (Fin d)) (hJ : ∀ i, i ∈ J ↔ k i ≠ 0)
    (x : UnitAddTorus (Fin d)) :
    (∑ K ∈ J.powerset,
      (-1 : ℂ)^K.card * UnitAddTorus.mFourier (-k)
        (reflectFaceCoordinates K x)) =
      ∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i)) := by
  classical
  have hsplit (K : Finset (Fin d)) (hK : K ⊆ J) :
      Finset.univ \ K = (J \ K) ∪ (Finset.univ \ J) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hi
      by_cases hiJ : i ∈ J
      · exact Or.inl ⟨hiJ, hi⟩
      · exact Or.inr hiJ
    · rintro (⟨hiJ, hiK⟩ | hiJ)
      · exact hiK
      · intro hiK
        exact hiJ (hK hiK)
  have hdisj (K : Finset (Fin d)) (hK : K ⊆ J) :
      Disjoint (J \ K) (Finset.univ \ J) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_sdiff.mp hi2).2 ((Finset.mem_sdiff.mp hi1).1)
  have hterm (K : Finset (Fin d)) (hK : K ⊆ J) :
      (-1 : ℂ)^K.card * UnitAddTorus.mFourier (-k)
          (reflectFaceCoordinates K x) =
        ((∏ i ∈ K, -fourier (k i) (x i)) *
          (∏ i ∈ J \ K, fourier (-k i) (x i))) := by
    rw [mFourier_neg_reflect]
    rw [hsplit K hK, Finset.prod_union (hdisj K hK)]
    have hout : ∏ i ∈ Finset.univ \ J, fourier (-k i) (x i) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hki : k i = 0 := by
        by_contra hn
        exact (Finset.mem_sdiff.mp hi).2 ((hJ i).2 hn)
      simp [hki]
    rw [hout, mul_one]
    have hsignprod :
        (-1 : ℂ)^K.card * ∏ i ∈ K, fourier (k i) (x i) =
          ∏ i ∈ K, -fourier (k i) (x i) := by
      calc
        (-1 : ℂ)^K.card * ∏ i ∈ K, fourier (k i) (x i) =
            (∏ i ∈ K, (-1 : ℂ)) * ∏ i ∈ K, fourier (k i) (x i) := by simp
        _ = ∏ i ∈ K, -fourier (k i) (x i) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro i hi
            ring
    calc
      (-1 : ℂ)^K.card *
          ((∏ i ∈ K, fourier (k i) (x i)) *
            (∏ i ∈ J \ K, fourier (-k i) (x i))) =
          ((-1 : ℂ)^K.card * (∏ i ∈ K, fourier (k i) (x i))) *
            (∏ i ∈ J \ K, fourier (-k i) (x i)) := by ring
      _ = (∏ i ∈ K, -fourier (k i) (x i)) *
            (∏ i ∈ J \ K, fourier (-k i) (x i)) := by rw [hsignprod]
  have hsum :
      (∑ K ∈ J.powerset,
        (-1 : ℂ)^K.card * UnitAddTorus.mFourier (-k)
          (reflectFaceCoordinates K x)) =
        ∑ K ∈ J.powerset,
          (∏ i ∈ K, -fourier (k i) (x i)) *
            ∏ i ∈ J \ K, fourier (-k i) (x i) := by
    apply Finset.sum_congr rfl
    intro K hKmem
    rw [hterm K (Finset.mem_powerset.mp hKmem)]
  rw [hsum]
  simpa [sub_eq_add_neg, add_comm] using
    (sum_powerset_prod_split J
      (fun i => -fourier (k i) (x i))
      (fun i => fourier (-k i) (x i)))

/-- The parity sign converts the circle sine phase to the triangular-fold
coordinate. -/
theorem circleIocRepresentative_zero :
    circleIocRepresentative (0 : UnitAddCircle) = 1 := by
  have hcoe : (circleIocRepresentative (0 : UnitAddCircle) : UnitAddCircle) = 0 := by
    simp [circleIocRepresentative]
  have hcoe1 : ((1:ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period (p := (1:ℝ))
  have hr : circleIocRepresentative (0 : UnitAddCircle) ∈ Set.Ioc (0:ℝ) (0+1) := by
    simpa [circleIocRepresentative] using
      (AddCircle.equivIoc (1:ℝ) 0 (0:UnitAddCircle)).property
  have h1 : (1:ℝ) ∈ Set.Ioc (0:ℝ) (0+1) := by norm_num
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
    (a := (0:ℝ)) (p := (1:ℝ)) hr h1).mp (hcoe.trans hcoe1.symm)

theorem circleIcoRepresentative_zero :
    circleIcoRepresentative (0 : UnitAddCircle) = 0 := by
  have hcoe : (circleIcoRepresentative (0 : UnitAddCircle) : UnitAddCircle) = 0 := by
    simp [circleIcoRepresentative]
  have hr : circleIcoRepresentative (0 : UnitAddCircle) ∈ Set.Ico (0:ℝ) (0+1) := by
    simpa [circleIcoRepresentative] using
      (AddCircle.equivIco (1:ℝ) 0 (0:UnitAddCircle)).property
  have h0 : (0:ℝ) ∈ Set.Ico (0:ℝ) (0+1) := by norm_num
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (0:ℝ)) (p := (1:ℝ)) hr h0).mp hcoe

theorem anchoredHalfSign_mul_sin_fold (n : ℤ) (x : UnitAddCircle) :
    anchoredHalfSign x *
        Real.sin (2 * Real.pi * (n : ℝ) * circleIocRepresentative x) =
      Real.sin (Real.pi * (n : ℝ) * triangleWave x) := by
  let r := circleIocRepresentative x
  have hr : r ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [r, circleIocRepresentative] using (AddCircle.equivIoc (1:ℝ) 0 x).property
  rw [triangleWave_eq_fold_representative]
  by_cases hx0 : x = 0
  · have hIoc : r = 1 := by simpa [r, hx0] using circleIocRepresentative_zero
    have hIco : circleIcoRepresentative x = 0 := by simpa [hx0] using circleIcoRepresentative_zero
    rw [hIco]
    have hs : Real.sin (2 * Real.pi * (n:ℝ)) = 0 := by
      have hh := Real.sin_int_mul_pi (n * 2)
      convert hh using 1 <;> push_cast <;> ring
    have hrx : circleIocRepresentative x = 1 := by simpa [r] using hIoc
    rw [hrx]
    simp [anchoredHalfSign, hs, foldUnitInterval]
  · have hrep : circleIcoRepresentative x = r := by
      exact (circleIcoRepresentative_eq_Ioc_of_ne_zero x hx0)
    rw [hrep]
    by_cases hhalf : r ≤ 1/2
    · have hfold : foldUnitInterval (2*r) = 2*r := by
        rw [foldUnitInterval, min_eq_left]
        linarith
      rw [hfold]
      have hrdef : circleIocRepresentative x = r := rfl
      have hhalf' : circleIocRepresentative x ≤ 1/2 := by simpa [r] using hhalf
      simp only [anchoredHalfSign, if_pos hhalf']
      rw [hrdef]
      ring_nf
    · have hfold : foldUnitInterval (2*r) = 2-2*r := by
        rw [foldUnitInterval, min_eq_right]
        linarith
      have harg : Real.pi * (n:ℝ) * (2-2*r) =
          (n:ℝ) * (2*Real.pi) - 2*Real.pi*(n:ℝ)*r := by ring
      rw [hfold, harg, Real.sin_int_mul_two_pi_sub]
      have hnot : ¬ circleIocRepresentative x ≤ 1/2 := by simpa [r] using hhalf
      have hrdef : circleIocRepresentative x = r := rfl
      simp only [anchoredHalfSign, if_neg hnot]
      rw [hrdef]
      simp

/-- The active Fourier character difference is the sine phase at the Ioc
representative. -/
theorem circleFourier_difference_eq_sin (n : ℤ) (x : UnitAddCircle) :
    fourier (-n) x - fourier n x =
      -2 * Complex.I *
        (Real.sin (2 * Real.pi * (n : ℝ) * circleIocRepresentative x) : ℂ) := by
  let r := circleIocRepresentative x
  let θ : ℝ := 2 * Real.pi * (n : ℝ) * r
  have hcoe : (r : UnitAddCircle) = x := by simp [r, circleIocRepresentative]
  have hneg : fourier (-n) (r : UnitAddCircle) = Complex.exp ((-θ : ℝ) * Complex.I) := by
    rw [fourier_coe_apply]
    dsimp [θ, r]
    push_cast
    norm_num
    ring
  have hpos : fourier n (r : UnitAddCircle) = Complex.exp ((θ : ℝ) * Complex.I) := by
    rw [fourier_coe_apply]
    dsimp [θ, r]
    push_cast
    norm_num
    ring
  have hnegx : fourier (-n) x = Complex.exp ((-θ : ℝ) * Complex.I) := by
    rw [← hcoe, hneg]
  have hposx : fourier n x = Complex.exp ((θ : ℝ) * Complex.I) := by
    rw [← hcoe, hpos]
  rw [hnegx, hposx, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  have hθ : θ = 2 * Real.pi * (n : ℝ) * circleIocRepresentative x := rfl
  rw [← hθ]
  rw [Real.sin_neg, Real.cos_neg]
  push_cast
  ring

/-- The active character differences, multiplied by the parity signs, give
exactly the folded sine factors coordinatewise and after taking products. -/
theorem anchoredFaceSign_characterProduct {d : ℕ} (J : Finset (Fin d))
    (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    (∏ i ∈ J, ((anchoredFaceSignCoordinate x i : ℝ) : ℂ)) *
        (∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i))) =
      ∏ i ∈ J, (-2 * Complex.I *
        (Real.sin (Real.pi * (k i : ℝ) * triangleWave (x i)) : ℂ)) := by
  classical
  have hfactor (i : Fin d) :
      ((anchoredFaceSignCoordinate x i : ℝ) : ℂ) *
          (fourier (-k i) (x i) - fourier (k i) (x i)) =
        -2 * Complex.I *
          (Real.sin (Real.pi * (k i : ℝ) * triangleWave (x i)) : ℂ) := by
    have hs := anchoredHalfSign_mul_sin_fold (k i) (x i)
    rw [circleFourier_difference_eq_sin]
    change (anchoredHalfSign (x i) : ℂ) *
        (-2 * Complex.I *
          (Real.sin (2 * Real.pi * (k i : ℝ) * circleIocRepresentative (x i)) : ℂ)) = _
    calc
      (anchoredHalfSign (x i) : ℂ) *
          (-2 * Complex.I *
            (Real.sin (2 * Real.pi * (k i : ℝ) * circleIocRepresentative (x i)) : ℂ)) =
          (-2 * Complex.I) *
            ((anchoredHalfSign (x i) : ℝ) *
              Real.sin (2 * Real.pi * (k i : ℝ) * circleIocRepresentative (x i)) : ℂ) := by ring
      _ = -2 * Complex.I *
            (Real.sin (Real.pi * (k i : ℝ) * triangleWave (x i)) : ℂ) := by
          rw [← Complex.ofReal_mul, hs]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hfactor i

/-- The active source coefficient factors into its sine multipliers and
inactive-coordinate weights without imposing regularity on the source. -/
theorem anchoredFaceSource_characterProduct {d : ℕ} (J : Finset (Fin d))
    (k : Fin d → ℤ) (g : (Fin d → ℝ) → ℝ) (x : UnitAddTorus (Fin d)) :
    ((anchoredFaceSource J g x : ℝ) : ℂ) *
        (∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i))) =
      ((2 : ℝ)^J.card : ℂ) *
        ((g (fun i => triangleWave (x i)) : ℂ) *
          ∏ i ∈ Finset.univ \ J, (1 - (triangleWave (x i) : ℂ))) *
        (∏ i ∈ J, (-2 * Complex.I *
          (Real.sin (Real.pi * (k i : ℝ) * triangleWave (x i)) : ℂ))) := by
  classical
  have hsourcecast :
      ((anchoredFaceSource J g x : ℝ) : ℂ) =
        ((2 : ℝ)^J.card : ℂ) *
          (∏ i ∈ J, ((anchoredFaceSignCoordinate x i : ℝ) : ℂ)) *
          ((g (fun i => triangleWave (x i)) : ℂ) *
            ∏ i ∈ Finset.univ \ J, (1 - (triangleWave (x i) : ℂ))) := by
    simp only [anchoredFaceSource, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_prod, Complex.ofReal_ofNat, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hsourcecast]
  calc
    _ = ((2 : ℝ)^J.card : ℂ) *
          (((∏ i ∈ J, ((anchoredFaceSignCoordinate x i : ℝ) : ℂ)) *
            ∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i))) *
            ((g (fun i => triangleWave (x i)) : ℂ) *
              ∏ i ∈ Finset.univ \ J, (1 - (triangleWave (x i) : ℂ)))) := by ring
    _ = ((2 : ℝ)^J.card : ℂ) *
          ((g (fun i => triangleWave (x i)) : ℂ) *
            ∏ i ∈ Finset.univ \ J, (1 - (triangleWave (x i) : ℂ))) *
          (∏ i ∈ J, (-2 * Complex.I *
            (Real.sin (Real.pi * (k i : ℝ) * triangleWave (x i)) : ℂ))) := by
          rw [anchoredFaceSign_characterProduct]
          ring

/-- The actual Fourier coefficient of the parity face source reduces, by
finite reflection averaging, to its active character-difference integral. -/
theorem anchoredFaceSource_fourierCoeff_average {d : ℕ} {p : ℝ}
    (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (k : Fin d → ℤ) (J : Finset (Fin d))
    (hJ : ∀ i, i ∈ J ↔ k i ≠ 0) :
    (∫ x : UnitAddTorus (Fin d),
      ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℝ) : ℂ) *
        UnitAddTorus.mFourier (-k) x ∂(volume : Measure (UnitAddTorus (Fin d)))) =
      (J.powerset.card : ℂ)⁻¹ *
        ∫ x : UnitAddTorus (Fin d),
          ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℝ) : ℂ) *
            (∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i)))
          ∂(volume : Measure (UnitAddTorus (Fin d))) := by
  classical
  let A := J.powerset
  let σ : Finset (Fin d) → UnitAddTorus (Fin d) → UnitAddTorus (Fin d) :=
    fun K => reflectFaceCoordinates K
  let χ : Finset (Fin d) → ℂ := fun K => (-1 : ℂ)^K.card
  let F : UnitAddTorus (Fin d) → ℂ := fun x =>
    ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x : ℝ) : ℂ)
  let phase : UnitAddTorus (Fin d) → ℂ := UnitAddTorus.mFourier (-k)
  have hA : A.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [A]
  have hMP : ∀ K ∈ A, MeasurePreserving (σ K)
      (volume : Measure (UnitAddTorus (Fin d)))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    intro K hK
    exact measurePreserving_reflectFaceCoordinates K
  have hparity : ∀ K ∈ A,
      (fun x => F (σ K x)) =ᵐ[volume] fun x => χ K * F x := by
    intro K hK
    have hsub : K ⊆ J := Finset.mem_powerset.mp (by simpa [A] using hK)
    filter_upwards [anchoredFaceSource_reflect_ae J K hsub
        (g : (Fin d → ℝ) → ℝ)] with x hx
    change ((anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) (σ K x) : ℝ) : ℂ) = _
    rw [hx]
    simp [F, χ, Complex.ofReal_mul]
  have hIntF : Integrable F (volume : Measure (UnitAddTorus (Fin d))) := by
    simpa [F] using integrable_anchoredFaceSource hp J g
  have hphase : ∀ x, ‖phase x‖ = 1 := by
    intro x
    simp [phase, UnitAddTorus.mFourier]
  have hphaseMeas : AEStronglyMeasurable phase
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
  have hphaseBound : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))),
      ‖phase x‖ ≤ 1 := by
    filter_upwards [] with x
    rw [hphase x]
  have hInt : Integrable (fun x => F x * phase x)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    simpa [mul_comm] using hIntF.bdd_mul hphaseMeas hphaseBound
  have hIntRef : ∀ K ∈ A, Integrable (fun x => F x * phase (σ K x))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    intro K hK
    have hpm : AEStronglyMeasurable (fun x => phase (σ K x))
        (volume : Measure (UnitAddTorus (Fin d))) := by
      exact (((UnitAddTorus.mFourier (-k)).continuous.measurable.comp
        (hMP K hK).measurable).aestronglyMeasurable)
    have hpb : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))),
        ‖phase (σ K x)‖ ≤ 1 := by
      filter_upwards [] with x
      rw [hphase (σ K x)]
    simpa [mul_comm] using hIntF.bdd_mul hpm hpb
  have havg := BrownianSharp.AlignmentPaperFiniteReflectionAverage.integral_eq_finite_reflection_average
    (volume : Measure (UnitAddTorus (Fin d))) A hA σ χ F phase hMP hparity hInt hIntRef
  have hsum (x : UnitAddTorus (Fin d)) :
      (∑ K ∈ A, χ K * phase (σ K x)) =
        ∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i)) := by
    simpa [A, χ, phase, σ] using sum_reflectedFourierCharacters k J hJ x
  have hIntegrand :
      (fun x : UnitAddTorus (Fin d) => F x *
        (∑ K ∈ A, χ K * phase (σ K x))) =
      fun x => F x * ∏ i ∈ J, (fourier (-k i) (x i) - fourier (k i) (x i)) := by
    funext x
    rw [hsum x]
  rw [hIntegrand] at havg
  simpa [A, F, phase] using havg

end BrownianSharp.AlignmentPaperAnchoredLpParityFourier
