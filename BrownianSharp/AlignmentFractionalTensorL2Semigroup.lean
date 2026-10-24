import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalL2OperatorSemigroup
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

namespace BrownianSharp.AlignmentFractionalTensorL2Semigroup
open AlignmentFractionalTensorOperator AlignmentL2TensorProduct
  AlignmentFractionalTensor
  AlignmentFractionalL2 AlignmentFractionalTranslation
  AlignmentFractionalDensity AlignmentFractionalL2Semigroup

abbrev CubeAmbientL2 (d : ℕ) := CameronMartin.UnitCubeL2 d

def clipCube {d : ℕ} : C((Fin d → ℝ), BrownianCubeAnchor d) where
  toFun x := ⟨fun i => AlignmentFractionalL2.clipUnit (x i), by
    intro i
    exact (AlignmentFractionalL2.clipUnit (x i)).property⟩
  continuous_toFun := by
    have hc : Continuous (fun x : Fin d → ℝ =>
        fun i => (AlignmentFractionalL2.clipUnit (x i)).val) :=
      continuous_pi fun i =>
        (continuous_subtype_val.comp (AlignmentFractionalL2.clipUnit_continuous.comp
          (continuous_apply i)))
    change Continuous (fun x : Fin d → ℝ =>
      (⟨fun i => AlignmentFractionalL2.clipUnit (x i), fun i =>
        (AlignmentFractionalL2.clipUnit (x i)).property⟩ : BrownianCubeAnchor d))
    exact Continuous.subtype_mk hc _

def extendCubeProfile {d : ℕ} (f : C(BrownianCubeAnchor d, ℝ)) :
    (Fin d → ℝ) →ᵇ ℝ :=
  ⟨⟨fun x => f (clipCube x), f.continuous.comp clipCube.continuous⟩,
    ⟨2 * ‖f‖, fun x y => by
      calc
        dist (f (clipCube x)) (f (clipCube y)) ≤
            ‖f (clipCube x)‖ + ‖f (clipCube y)‖ := dist_le_norm_add_norm _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring⟩⟩

def cubeProfileToL2 {d : ℕ} :
    C(BrownianCubeAnchor d, ℝ) →L[ℝ] CubeAmbientL2 d := by
  let μ : Measure (Fin d → ℝ) :=
    (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d)
  haveI : IsFiniteMeasure μ := by
    rw [show μ = (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d) from rfl, AlignmentFractionalTensor.unitCube_measure_eq_pi]
    infer_instance
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  let L : C(BrownianCubeAnchor d, ℝ) →ₗ[ℝ] (Fin d → ℝ) →ᵇ ℝ := {
    toFun := extendCubeProfile
    map_add' := by intro f g; ext x; rfl
    map_smul' := by intro c f; ext x; rfl }
  let E : ((Fin d → ℝ) →ᵇ ℝ) →L[ℝ] Lp ℝ 2 μ :=
    BoundedContinuousFunction.toLp (E:=ℝ) (𝕜:=ℝ) (p:=2) μ
  exact E.comp (L.mkContinuous 1 (by
    intro f
    calc
      ‖L f‖ ≤ ‖f‖ := by
        rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
        intro x
        exact f.norm_coe_le_norm (clipCube x)
      _ = 1 * ‖f‖ := by ring))

theorem cubeProfileToL2_coe {d : ℕ} (f : C(BrownianCubeAnchor d, ℝ)) :
    cubeProfileToL2 f =ᵐ[((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d))] fun x => f (clipCube x) := by
  let μ : Measure (Fin d → ℝ) :=
    (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d)
  haveI : IsFiniteMeasure μ := by
    rw [show μ = (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d) from rfl, AlignmentFractionalTensor.unitCube_measure_eq_pi]
    infer_instance
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  change BoundedContinuousFunction.toLp (E:=ℝ) (p:=2) μ ℝ (extendCubeProfile f) =ᵐ[μ] _
  simpa [extendCubeProfile] using
    (BoundedContinuousFunction.coeFn_toLp (E:=ℝ) (p:=2) μ ℝ (extendCubeProfile f))

def cubeProductProfile {d : ℕ} (F : Fin d → C(UnitInterval, ℝ)) :
    C(BrownianCubeAnchor d, ℝ) where
  toFun t := ∏ i, F i (cubeCoordinate i t)
  continuous_toFun := by
    apply continuous_finset_prod
    intro i hi
    exact (F i).continuous.comp (cubeCoordinate i).continuous

def cubeMonomial {d : ℕ} (m : Fin d → ℕ) : C(BrownianCubeAnchor d, ℝ) where
  toFun t := ∏ i, t.val i ^ (m i)
  continuous_toFun := by
    apply continuous_finset_prod
    intro i hi
    exact (continuous_apply i).comp continuous_subtype_val |>.pow (m i)

def cubeMonomialSpan {d : ℕ} : Submodule ℝ C(BrownianCubeAnchor d, ℝ) :=
  Submodule.span ℝ (Set.range (@cubeMonomial d))

theorem cubeMonomial_mul {d : ℕ} (m n : Fin d → ℕ) :
    cubeMonomial m * cubeMonomial n = cubeMonomial (m+n) := by
  ext t
  simp [cubeMonomial, Finset.prod_mul_distrib, pow_add]

theorem cubeMonomial_mul_mem_span {d : ℕ} (m : Fin d → ℕ)
    {g : C(BrownianCubeAnchor d, ℝ)} (hg : g ∈ cubeMonomialSpan (d:=d)) :
    cubeMonomial m * g ∈ cubeMonomialSpan (d:=d) := by
  classical
  change cubeMonomial m * g ∈ Submodule.span ℝ (Set.range (@cubeMonomial d))
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · intro z hz
    rcases hz with ⟨n, rfl⟩
    rw [cubeMonomial_mul]
    exact Submodule.subset_span ⟨m+n, rfl⟩
  · simpa using Submodule.zero_mem (Submodule.span ℝ (Set.range (@cubeMonomial d)))
  · intro x y hx hy hpx hpy
    simpa [mul_add] using Submodule.add_mem
      (Submodule.span ℝ (Set.range (@cubeMonomial d))) hpx hpy
  · intro c x hx hcx
    rw [mul_smul_comm]
    exact Submodule.smul_mem (Submodule.span ℝ (Set.range (@cubeMonomial d))) c hcx

def cubeMonomialAlgebra {d : ℕ} : Subalgebra ℝ C(BrownianCubeAnchor d, ℝ) where
  carrier := ((cubeMonomialSpan (d:=d)) : Set C(BrownianCubeAnchor d, ℝ))
  add_mem' := by
    intro a b ha hb
    exact Submodule.add_mem (Submodule.span ℝ (Set.range (@cubeMonomial d))) ha hb
  mul_mem' := by
    intro f g hf hg
    classical
    change f*g ∈ Submodule.span ℝ (Set.range (@cubeMonomial d))
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro m hm
      rcases hm with ⟨m, rfl⟩
      exact cubeMonomial_mul_mem_span m hg
    · simpa using Submodule.zero_mem (Submodule.span ℝ (Set.range (@cubeMonomial d)))
    · intro x y hx hy hxy hxy'
      simpa [add_mul] using Submodule.add_mem
        (Submodule.span ℝ (Set.range (@cubeMonomial d))) hxy hxy'
    · intro c x hx hcx
      rw [smul_mul_assoc]
      exact Submodule.smul_mem (Submodule.span ℝ (Set.range (@cubeMonomial d))) c hcx
  algebraMap_mem' := by
    intro c
    have h0 : cubeMonomial (fun _ : Fin d => 0) = 1 := by
      ext t
      simp [cubeMonomial]
    rw [Algebra.algebraMap_eq_smul_one, ← h0]
    exact Submodule.smul_mem (Submodule.span ℝ (Set.range (@cubeMonomial d))) c
      (Submodule.subset_span ⟨_, rfl⟩)

theorem cubeMonomialAlgebra_separates {d : ℕ} :
    (cubeMonomialAlgebra (d:=d)).SeparatesPoints := by
  intro x y hxy
  have hneq : x.val ≠ y.val := by
    intro h
    apply hxy
    exact Subtype.ext h
  have hcoord : ∃ i, x.val i ≠ y.val i := by
    by_contra h
    push_neg at h
    apply hneq
    funext i
    exact h i
  rcases hcoord with ⟨i, hi⟩
  let m : Fin d → ℕ := fun j => if j=i then 1 else 0
  have hm : cubeMonomial m ∈ cubeMonomialAlgebra (d:=d) := by
    change cubeMonomial m ∈ cubeMonomialSpan (d:=d)
    exact Submodule.subset_span ⟨m, rfl⟩
  have hm' : (cubeMonomial m : BrownianCubeAnchor d → ℝ) ∈
      (fun f : C(BrownianCubeAnchor d, ℝ) => (f : BrownianCubeAnchor d → ℝ)) ''
        (cubeMonomialAlgebra (d:=d) : Set C(BrownianCubeAnchor d, ℝ)) :=
    ⟨cubeMonomial m, hm, rfl⟩
  refine ⟨(cubeMonomial m : BrownianCubeAnchor d → ℝ), hm', ?_⟩
  simpa [cubeMonomial, m, hi]

theorem cubeMonomialSpan_dense {d : ℕ} :
    Dense ((cubeMonomialSpan (d:=d)) : Set C(BrownianCubeAnchor d, ℝ)) := by
  have htop := congrArg (fun s : Subalgebra ℝ C(BrownianCubeAnchor d, ℝ) =>
    (s : Set C(BrownianCubeAnchor d, ℝ)))
    (ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
      (cubeMonomialAlgebra (d:=d)) (cubeMonomialAlgebra_separates (d:=d)))
  have htop' : closure ((cubeMonomialSpan (d:=d)) : Set C(BrownianCubeAnchor d, ℝ)) =
      Set.univ := by
    change closure ((cubeMonomialSpan (d:=d)) : Set C(BrownianCubeAnchor d, ℝ)) =
      Set.univ at htop
    exact htop
  apply dense_iff_closure_eq.2
  exact htop'

theorem cubeProfileToL2_cubeProduct {d : ℕ} (F : Fin d → C(UnitInterval, ℝ)) :
    cubeProfileToL2 (cubeProductProfile F) =
      productToCube d (productVector (fun i => profileToL2 (F i))) := by
  apply Lp.ext
  have hleft := cubeProfileToL2_coe (cubeProductProfile F)
  have hright := cube_productVector_ae (fun i => profileToL2 (F i))
  have hp : (fun x : Fin d → ℝ => fun i : Fin d => profileToL2 (F i) (x i)) =ᵐ[
      Measure.pi (fun _ : Fin d => (volume.restrict (Set.Icc (0:ℝ) 1)))]
      (fun x i => F i (AlignmentFractionalL2.clipUnit (x i))) :=
    Measure.ae_eq_pi (fun i => profileToL2_coe (F i))
  have hpCube : (fun x : Fin d → ℝ => fun i : Fin d => profileToL2 (F i) (x i)) =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)]
      (fun x i => F i (AlignmentFractionalL2.clipUnit (x i))) := by
    rw [AlignmentFractionalTensor.unitCube_measure_eq_pi]
    exact hp
  filter_upwards [hleft, hright, ae_restrict_mem (CameronMartin.measurableSet_unitCubeSet d),
    hpCube] with x hl hr hx hpx
  have hp' : ∀ i, profileToL2 (F i) (x i) = F i (AlignmentFractionalL2.clipUnit (x i)) := by
    exact fun i => congrFun (hpx) i
  rw [hl, hr]
  change (∏ i, F i (cubeCoordinate i (clipCube x))) =
    ∏ i, profileToL2 (F i) (x i)
  apply Finset.prod_congr rfl
  intro i hi
  rw [hp' i]
  congr 1

theorem cubeProfileToL2_denseRange {d : ℕ} : DenseRange (@cubeProfileToL2 d) := by
  let μ : Measure (Fin d → ℝ) :=
    (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d)
  haveI : IsFiniteMeasure μ := by
    rw [show μ = (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d) from rfl, AlignmentFractionalTensor.unitCube_measure_eq_pi]
    infer_instance
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  have hd := BoundedContinuousFunction.toLp_denseRange
    (E:=ℝ) (p:=2) μ ℝ (by norm_num : (2:ENNReal)≠⊤)
  apply hd.mono
  rintro g ⟨F,rfl⟩
  let f : C(BrownianCubeAnchor d, ℝ) :=
    ⟨fun t => F t.1, F.continuous.comp continuous_subtype_val⟩
  refine ⟨f, ?_⟩
  apply Lp.ext
  have hf := cubeProfileToL2_coe f
  have hF := BoundedContinuousFunction.coeFn_toLp (E:=ℝ) (p:=2) μ ℝ F
  filter_upwards [hf, hF, ae_restrict_mem (CameronMartin.measurableSet_unitCubeSet d)]
    with x hxF hF hx
  rw [hxF, hF]
  change F (clipCube x).val = F x
  congr 1
  funext i
  simp [clipCube, AlignmentFractionalL2.clipUnit,
    (Set.mem_pi.mp hx i (Set.mem_univ i)).1,
    (Set.mem_pi.mp hx i (Set.mem_univ i)).2]

def sourceMonomialSpan {d : ℕ} : Submodule ℝ (CubeAmbientL2 d) :=
  Submodule.span ℝ (Set.range (fun m : Fin d → ℕ => cubeProfileToL2 (cubeMonomial m)))

theorem sourceMonomialSpan_dense {d : ℕ} :
    Dense (sourceMonomialSpan (d:=d) : Set (CubeAmbientL2 d)) := by
  have hsub : DenseRange (fun f : cubeMonomialSpan (d:=d) =>
      (f : C(BrownianCubeAnchor d,ℝ))) :=
    denseRange_subtype_val.2 (cubeMonomialSpan_dense (d:=d))
  have hdense := (cubeProfileToL2_denseRange (d:=d)).comp hsub cubeProfileToL2.continuous
  have hmap : ∀ f : C(BrownianCubeAnchor d,ℝ), f ∈ cubeMonomialSpan (d:=d) →
      cubeProfileToL2 f ∈ sourceMonomialSpan (d:=d) := by
    intro f hf
    change f ∈ Submodule.span ℝ (Set.range (@cubeMonomial d)) at hf
    change cubeProfileToL2 f ∈ Submodule.span ℝ
      (Set.range (fun m : Fin d → ℕ => cubeProfileToL2 (cubeMonomial m)))
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro q ⟨m,rfl⟩
      exact Submodule.subset_span ⟨m,rfl⟩
    · simp
    · intro a b ha hb hpa hpb
      simpa using Submodule.add_mem
        (Submodule.span ℝ (Set.range (fun m : Fin d → ℕ =>
          cubeProfileToL2 (cubeMonomial m)))) hpa hpb
    · intro c a ha hpa
      simpa using Submodule.smul_mem
        (Submodule.span ℝ (Set.range (fun m : Fin d → ℕ =>
          cubeProfileToL2 (cubeMonomial m)))) c hpa
  apply hdense.mono
  rintro g ⟨f,rfl⟩
  exact hmap f.1 f.2

def fractionalTensorRLToL2 {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i, 1/2<a i) :
    CubeAmbientL2 d →L[ℝ] CubeAmbientL2 d :=
  (cubeProfileToL2 (d:=d)).comp (fractionalTensorRL a ha)

theorem cubeMonomial_eq_tensorProfile {d : ℕ} (m : Fin d → ℕ) :
    cubeMonomial m = cubeProductProfile (fun i => monomialProfile (m i)) := by
  ext t
  change (∏ i, t.val i ^ (m i)) =
    ∏ i, monomialProfile (m i) (cubeCoordinate i t)
  apply Finset.prod_congr rfl
  intro i hi
  simp [monomialProfile, Polynomial.toContinuousMapOn, cubeCoordinate]

theorem fractionalTensorRL_semigroup_on_cubeMonomial {d : ℕ} {r b : ℝ}
    (hr : 1/2<r) (hb : 1/2<b) (m : Fin d → ℕ) :
    fractionalTensorRL (fun _ => r+b) (fun _ => by linarith)
      (cubeProfileToL2 (cubeMonomial m)) =
      (fractionalTensorRL (fun _ => r) (fun _ => hr)).comp
        (fractionalTensorRLToL2 (fun _ => b) (fun _ => hb))
        (cubeProfileToL2 (cubeMonomial m)) := by
  let v : Fin d → UnitL2 := fun i => profileToL2 (monomialProfile (m i))
  have hsource : cubeProfileToL2 (cubeMonomial m) = productToCube d (productVector v) := by
    rw [cubeMonomial_eq_tensorProfile, cubeProfileToL2_cubeProduct]
  let F : Fin d → C(UnitInterval,ℝ) := fun i => fractionalOnC b hb (monomialProfile (m i))
  have hmiddle : fractionalTensorRL (fun _ => b) (fun _ => hb)
      (cubeProfileToL2 (cubeMonomial m)) = cubeProductProfile F := by
    ext t
    rw [hsource, fractionalTensorRL_product]
    rfl
  ext t
  change fractionalTensorRL (fun _ => r+b) (fun _ => by linarith)
      (cubeProfileToL2 (cubeMonomial m)) t = _
  rw [hsource, fractionalTensorRL_product]
  change (∏ i, fractionalRL (r+b) (by linarith) (v i) (cubeCoordinate i t)) =
    fractionalTensorRL (fun _ => r) (fun _ => hr)
      (cubeProfileToL2 (fractionalTensorRL (fun _ => b) (fun _ => hb)
        (productToCube d (productVector v)))) t
  rw [← hsource, hmiddle, cubeProfileToL2_cubeProduct, fractionalTensorRL_product]
  apply Finset.prod_congr rfl
  intro i hi
  have hs := fractionalRL_semigroup (a:=r) (b:=b) hr hb
  have hsi := congrArg (fun L : UnitL2 →L[ℝ] C(UnitInterval,ℝ) =>
    L (profileToL2 (monomialProfile (m i)))) hs
  have hsi' : fractionalRL (r+b) (by linarith) (v i) =
      fractionalRL r hr (profileToL2 (F i)) := by
    simpa [v, F, fractionalOnC, ContinuousLinearMap.comp_apply] using hsi.symm
  exact congrArg (fun f : C(UnitInterval,ℝ) => f (cubeCoordinate i t)) hsi'

theorem fractionalTensorRL_semigroup {d : ℕ} {r b : ℝ}
    (hr : 1/2<r) (hb : 1/2<b) :
    fractionalTensorRL (d:=d) (fun _ : Fin d => r+b)
        (fun _ : Fin d => by linarith) =
      (fractionalTensorRL (d:=d) (fun _ : Fin d => r)
        (fun _ : Fin d => hr)).comp
        (fractionalTensorRLToL2 (d:=d) (fun _ : Fin d => b)
          (fun _ : Fin d => hb)) := by
  apply ContinuousLinearMap.ext_on (sourceMonomialSpan_dense (d:=d))
  intro g hg
  rcases hg with ⟨m, rfl⟩
  exact fractionalTensorRL_semigroup_on_cubeMonomial hr hb m

end BrownianSharp.AlignmentFractionalTensorL2Semigroup
