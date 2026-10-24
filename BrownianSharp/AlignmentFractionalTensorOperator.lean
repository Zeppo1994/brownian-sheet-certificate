import BrownianSharp.AlignmentL2TensorProduct
import BrownianSharp.AlignmentFractionalTranslation
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalTensorOperator
open AlignmentFractionalTensor AlignmentL2TensorProduct AlignmentFractionalL2
  AlignmentFractionalTranslation

abbrev ProductCubeL2 (d : ℕ) :=
  Lp ℝ 2 (Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1)))

def productToCube (d : ℕ) : ProductCubeL2 d →L[ℝ] CameronMartin.UnitCubeL2 d :=
  Lp.LpToLpOfMeasureLeSMul (p:=2) (c:=1) (by simp)
    (by rw [unitCube_measure_eq_pi]; simp)

theorem productToCube_ae {d : ℕ} (g : ProductCubeL2 d) :
    productToCube d g =ᵐ[(Measure.pi (fun _ : Fin d => (volume:Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d)] g :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (p:=2) (c:=1) (by simp)
    (by rw [unitCube_measure_eq_pi]; simp) g

def cubeCoordinate {d : ℕ} (i : Fin d) : C(BrownianCubeAnchor d, UnitInterval) where
  toFun t := ⟨t.val i, t.property i⟩
  continuous_toFun := ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

def productKernelFamily {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i,1/2<a i) :
    C(BrownianCubeAnchor d, ProductCubeL2 d) where
  toFun t := tensorContinuous (μ:=fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))
    (fun i => translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i t))
  continuous_toFun := tensorContinuous.cont.comp (continuous_pi fun i =>
    (translatedUnitKernelFamily (a i) (ha i)).continuous.comp (cubeCoordinate i).continuous)

theorem productKernelFamily_ae {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i,1/2<a i)
    (t : BrownianCubeAnchor d) :
    productKernelFamily a ha t =ᵐ[Measure.pi
      (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))]
      Latest.fractionalTensorKernel a t := by
  let v : Fin d → UnitL2 := fun i =>
    translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i t)
  have hfactor : ∀ i, v i =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      causalKernel (a i) (t.val i) := by
    intro i
    dsimp [v, cubeCoordinate]
    rw [translatedUnitKernelFamily_eq_kernelVector (a i) (t.val i) (ha i)
      (t.property i).1 (t.property i).2]
    exact (causalKernel_memLp_unit (ha i) (t.property i).1 (t.property i).2).coeFn_toLp
  have hprod := Measure.ae_eq_pi hfactor
  change productVector v =ᵐ[_] _
  filter_upwards [productVector_ae v, hprod] with u h1 h2
  rw [h1]
  unfold Latest.fractionalTensorKernel
  apply Finset.prod_congr rfl
  intro i hi
  exact congrFun h2 i

/-- A continuous L²-valued feature realization of the actual tensor RL
kernel, including nonintegral coordinate orders above one half. -/
def tensorKernelFamily {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i,1/2<a i) :
    C(BrownianCubeAnchor d, CameronMartin.UnitCubeL2 d) :=
  ⟨fun t => productToCube d (productKernelFamily a ha t),
    (productToCube d).continuous.comp (productKernelFamily a ha).continuous⟩

theorem tensorKernelFamily_ae {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i,1/2<a i)
    (t : BrownianCubeAnchor d) :
    tensorKernelFamily a ha t =ᵐ[(Measure.pi
      (fun _ : Fin d => (volume:Measure ℝ))).restrict (CameronMartin.unitCubeSet d)]
      Latest.fractionalTensorKernel a t := by
  have hp : productKernelFamily a ha t =ᵐ[(Measure.pi
      (fun _ : Fin d => (volume:Measure ℝ))).restrict (CameronMartin.unitCubeSet d)]
      Latest.fractionalTensorKernel a t := by
    rw [unitCube_measure_eq_pi]
    exact productKernelFamily_ae a ha t
  exact (productToCube_ae (productKernelFamily a ha t)).trans hp

/-- The manuscript's Gamma-normalized tensor integration map is a genuine
bounded linear operator into continuous functions. -/
def fractionalTensorRL {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i,1/2<a i) :
    CameronMartin.UnitCubeL2 d →L[ℝ] C(BrownianCubeAnchor d, ℝ) := by
  let K := tensorKernelFamily a ha
  let L : CameronMartin.UnitCubeL2 d →ₗ[ℝ] C(BrownianCubeAnchor d, ℝ) :=
    { toFun := fun g => ⟨fun t => ⟪K t,g⟫, K.continuous.inner continuous_const⟩
      map_add' := by intro g h; ext t; simp [inner_add_right]
      map_smul' := by intro c g; ext t; simp [inner_smul_right] }
  exact L.mkContinuous ‖K‖ (by
    intro g
    apply (ContinuousMap.norm_le _ (by positivity : 0≤‖K‖*‖g‖)).2
    intro t
    exact (norm_inner_le_norm (K t) g).trans
      (mul_le_mul_of_nonneg_right (K.norm_coe_le_norm t) (norm_nonneg g)))

theorem fractionalTensorRL_apply {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i,1/2<a i)
    (g : CameronMartin.UnitCubeL2 d) (t : BrownianCubeAnchor d) :
    fractionalTensorRL a ha g t = Latest.fractionalIntegrationValue a g t := by
  change inner ℝ (tensorKernelFamily a ha t) g = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorKernelFamily_ae a ha t] with u hu
  change g u * tensorKernelFamily a ha t u = Latest.fractionalTensorKernel a t u * g u
  rw [hu]
  ring

theorem fractionalIntegrationBall_eq_operator_image {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) :
    Latest.fractionalIntegrationBall a =
      fractionalTensorRL a ha '' {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1} := by
  ext f
  constructor
  · rintro ⟨g,hg,heq⟩
    refine ⟨g,hg,?_⟩
    ext t
    rw [fractionalTensorRL_apply]
    exact heq t
  · rintro ⟨g,hg,rfl⟩
    refine ⟨g,hg,?_⟩
    intro t
    exact (fractionalTensorRL_apply a ha g t).symm

theorem productToCube_norm_le (d : ℕ) (g : ProductCubeL2 d) :
    ‖productToCube d g‖ ≤ ‖g‖ := by
  have hnorm : ‖productToCube d‖ ≤ 1 := by
    exact le_trans (Lp.norm_LpToLpOfMeasureLeSMul_le (p:=2) (c:=1) (by simp)
      (by rw [unitCube_measure_eq_pi]; simp)) (by norm_num)
  exact ((productToCube d).le_opNorm g).trans
    (by simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg g))

theorem cube_productVector_ae {d : ℕ} (v : Fin d → UnitL2) :
    productToCube d (productVector v) =ᵐ[(Measure.pi
      (fun _ : Fin d => (volume:Measure ℝ))).restrict (CameronMartin.unitCubeSet d)]
      (fun u => ∏ i, v i (u i)) := by
  apply (productToCube_ae (productVector v)).trans
  rw [unitCube_measure_eq_pi]
  exact productVector_ae v

/-- Tensor integration on a product source factors into the one-dimensional
RL operators, in the manuscript's actual source space. -/
theorem fractionalTensorRL_product {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) (v : Fin d → UnitL2) (t : BrownianCubeAnchor d) :
    fractionalTensorRL a ha (productToCube d (productVector v)) t =
      ∏ i, fractionalRL (a i) (ha i) (v i) (cubeCoordinate i t) := by
  rw [fractionalTensorRL_apply]
  unfold Latest.fractionalIntegrationValue
  have hae := cube_productVector_ae v
  rw [integral_congr_ae (hae.mono fun u hu => by rw [hu])]
  have hfun : (fun u => Latest.fractionalTensorKernel a t u * ∏ i, v i (u i)) =
      (fun u => ∏ i, causalKernel (a i) (t.val i) (u i) * v i (u i)) := by
    funext u
    unfold Latest.fractionalTensorKernel
    rw [← Finset.prod_mul_distrib]
    rfl
  rw [hfun, unitCube_measure_eq_pi, integral_fintype_prod_eq_prod
    (fun i u => causalKernel (a i) (t.val i) u * v i u)]
  apply Finset.prod_congr rfl
  intro i hi
  exact (fractionalRL_apply (a i) (ha i) (v i) (t.val i)
    (t.property i).1 (t.property i).2).symm

theorem cube_productVector_norm_le {d : ℕ} (v : Fin d → UnitL2) :
    ‖productToCube d (productVector v)‖ ≤ ∏ i, ‖v i‖ := by
  exact (productToCube_norm_le d _).trans_eq (productVector_norm v)

/-- Coordinate preimages tensorize without a dimension-dependent loss in
the source norm. -/
theorem tensor_preimage_of_coordinate_preimages {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i,1/2<a i) (F : Fin d → C(UnitInterval, ℝ))
    (v : Fin d → UnitL2) (hv : ∀ i, fractionalRL (a i) (ha i) (v i) = F i) :
    ∃ g : CameronMartin.UnitCubeL2 d, ‖g‖ ≤ ∏ i, ‖v i‖ ∧
      ∀ t, fractionalTensorRL a ha g t = ∏ i, F i (cubeCoordinate i t) := by
  refine ⟨productToCube d (productVector v), cube_productVector_norm_le v, ?_⟩
  intro t
  rw [fractionalTensorRL_product]
  simp_rw [hv]

end BrownianSharp.AlignmentFractionalTensorOperator
