import BrownianSharp.AlignmentPaperQuantization
import BrownianSharp.AlignmentPaperGaussianFeatureBridge
import BrownianSharp.BrownianGaussianL2Closure
import BrownianSharp.AlignmentPaperCovarianceCombination
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Fernique
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Constructions.SumProd

/-! Path-space moment bridge for centered continuous Gaussian processes.
The proof compares the original pair of independent copies with its orthogonal
rotation through finite-dimensional Gaussian laws and continuous-path law
uniqueness, then applies the pinned Fernique theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open BrownianSharp.AlignmentPaperCovarianceCombination
open Filter
open scoped Topology

namespace BrownianSharp.AlignmentPaperContinuousGaussianFernique

theorem copySumProcess_isGaussian
    {α Ω : Type*} [TopologicalSpace α] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P) :
    IsGaussianProcess
      (fun i : α ⊕ α => fun z : Ω × Ω =>
        Sum.elim (fun x => F z.1 x) (fun x => F z.2 x) i)
      (P.prod P) := by
  classical
  let R : Measure (Ω × Ω) := P.prod P
  refine ⟨?_⟩
  intro I
  let j : α ⊕ α → α := Sum.elim id id
  let J : Finset α := I.image j
  let A : Ω → (J → ℝ) := fun ω k => F ω k.1
  let B : Ω → (J → ℝ) := fun ω k => F ω k.1
  have hAmeas : Measurable A := by
    apply measurable_pi_iff.mpr
    intro k
    exact (ContinuousMap.measurable_eval k.1).comp hF
  have hBmeas : Measurable B := by
    apply measurable_pi_iff.mpr
    intro k
    exact (ContinuousMap.measurable_eval k.1).comp hF
  have hA : HasGaussianLaw A P := by
    convert hX.hasGaussianLaw J using 1 <;> ext ω k <;> rfl
  have hB : HasGaussianLaw B P := hA
  have hAcopy : HasGaussianLaw (fun z : Ω × Ω => A z.1) R := by
    refine ⟨(hAmeas.comp measurable_fst).aemeasurable, ?_⟩
    have hmap : R.map (fun z : Ω × Ω => A z.1) = P.map A := by
      dsimp [R]
      change (P.prod P).map (A ∘ Prod.fst) = P.map A
      rw [← Measure.map_map hAmeas measurable_fst, Measure.map_fst_prod,
        measure_univ, one_smul]
    rw [hmap]
    exact hA.isGaussian_map
  have hBcopy : HasGaussianLaw (fun z : Ω × Ω => B z.2) R := by
    refine ⟨(hBmeas.comp measurable_snd).aemeasurable, ?_⟩
    have hmap : R.map (fun z : Ω × Ω => B z.2) = P.map B := by
      dsimp [R]
      change (P.prod P).map (B ∘ Prod.snd) = P.map B
      rw [← Measure.map_map hBmeas measurable_snd, Measure.map_snd_prod,
        measure_univ, one_smul]
    rw [hmap]
    exact hB.isGaussian_map
  have hAB : IndepFun (fun z : Ω × Ω => A z.1) (fun z => B z.2) R := by
    exact indepFun_prod hAmeas hBmeas
  have hpair : HasGaussianLaw (fun z => (A z.1, B z.2)) R :=
    hAB.hasGaussianLaw hAcopy hBcopy
  let memJ (i : I) : J := ⟨j i.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
  let L₀ : ((J → ℝ) × (J → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun v i => match i.1 with
        | Sum.inl _ => v.1 (memJ i)
        | Sum.inr _ => v.2 (memJ i)
      map_add' := by
        intro x y
        ext i
        cases hi : i.1 with
        | inl _ => simp [memJ, hi]
        | inr _ => simp [memJ, hi]
      map_smul' := by
        intro c x
        ext i
        cases hi : i.1 with
        | inl _ => simp [memJ, hi]
        | inr _ => simp [memJ, hi] }
  let L : ((J → ℝ) × (J → ℝ)) →L[ℝ] (I → ℝ) :=
    ⟨L₀, L₀.continuous_of_finiteDimensional⟩
  have hmap := hpair.map L
  have hEq (z : Ω × Ω) : L (A z.1, B z.2) =
      fun i => Sum.elim (fun x => F z.1 x) (fun x => F z.2 x) i.1 := by
    funext i
    cases hi : i.1 with
    | inl _ => simp [L, L₀, memJ, A, j, hi]
    | inr _ => simp [L, L₀, memJ, B, j, hi]
  exact hmap.congr (Eventually.of_forall hEq)

/-- The orthogonally rotated pair of independent copies remains a Gaussian
process on the disjoint-union index. -/
theorem rotatedCopySumProcess_isGaussian
    {α Ω : Type*} [TopologicalSpace α] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P) :
    IsGaussianProcess
      (fun i : α ⊕ α => fun z : Ω × Ω =>
        match i with
        | Sum.inl x => (Real.sqrt 2)⁻¹ * (F z.1 x - F z.2 x)
        | Sum.inr x => (Real.sqrt 2)⁻¹ * (F z.1 x + F z.2 x))
      (P.prod P) := by
  classical
  let U : α ⊕ α → Ω × Ω → ℝ := fun i z =>
    Sum.elim (fun x => F z.1 x) (fun x => F z.2 x) i
  have hU := copySumProcess_isGaussian F hF hX
  refine hU.of_isGaussianProcess ?_
  intro i
  cases i with
  | inl x =>
      let S : Finset (α ⊕ α) := {Sum.inl x, Sum.inr x}
      let L₀ : (S → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun v => (Real.sqrt 2)⁻¹ *
            (v ⟨Sum.inl x, by simp [S]⟩ - v ⟨Sum.inr x, by simp [S]⟩)
          map_add' := by intro a b; simp [mul_add] <;> ring
          map_smul' := by intro c a; simp <;> ring }
      let L : (S → ℝ) →L[ℝ] ℝ := ⟨L₀, L₀.continuous_of_finiteDimensional⟩
      refine ⟨S, L, ?_⟩
      intro z
      simp [L, L₀, U, S]
  | inr x =>
      let S : Finset (α ⊕ α) := {Sum.inl x, Sum.inr x}
      let L₀ : (S → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun v => (Real.sqrt 2)⁻¹ *
            (v ⟨Sum.inl x, by simp [S]⟩ + v ⟨Sum.inr x, by simp [S]⟩)
          map_add' := by intro a b; simp [mul_add] <;> ring
          map_smul' := by intro c a; simp <;> ring }
      let L : (S → ℝ) →L[ℝ] ℝ := ⟨L₀, L₀.continuous_of_finiteDimensional⟩
      refine ⟨S, L, ?_⟩
      intro z
      simp [L, L₀, U, S]

private def encodePair {α : Type*} [TopologicalSpace α]
    (f g : C(α, ℝ)) : C(α ⊕ α, ℝ) :=
  ⟨Sum.elim f g, continuous_sumElim.2 ⟨f.continuous, g.continuous⟩⟩

/-- The actual path law of two independent centered Gaussian copies is
invariant under the quarter-turn rotation. This is obtained from finite
Gaussian restrictions on `α ⊕ α` and continuous-path law uniqueness. -/
theorem centeredGaussian_pathPair_rotation_invariant
    {α Ω : Type*} [TopologicalSpace α] [CompactSpace α] [SecondCountableTopology α]
    [LocallyCompactSpace α] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0) :
    ((P.map F).prod (P.map F)).map
      (ContinuousLinearMap.rotation (-(Real.pi / 4))) =
        (P.map F).prod (P.map F) := by
  classical
  letI : LocallyCompactSpace (α ⊕ α) := by
    refine ⟨?_⟩
    intro i n hn
    cases i with
    | inl a =>
        have hn' : Sum.inl ⁻¹' n ∈ 𝓝 a := by
          simpa [nhds_inl] using hn
        obtain ⟨s, hs, hsub, hcompact⟩ :=
          LocallyCompactSpace.local_compact_nhds a (Sum.inl ⁻¹' n) hn'
        refine ⟨Sum.inl '' s, ?_, ?_, hcompact.image continuous_inl⟩
        · have hpre : (Sum.inl : α → α ⊕ α) ⁻¹'
              ((Sum.inl : α → α ⊕ α) '' s) = s := by
            ext x
            simp
          simpa [nhds_inl, hpre] using hs
        · rintro _ ⟨x, hx, rfl⟩
          exact hsub hx
    | inr a =>
        have hn' : Sum.inr ⁻¹' n ∈ 𝓝 a := by
          simpa [nhds_inr] using hn
        obtain ⟨s, hs, hsub, hcompact⟩ :=
          LocallyCompactSpace.local_compact_nhds a (Sum.inr ⁻¹' n) hn'
        refine ⟨Sum.inr '' s, ?_, ?_, hcompact.image continuous_inr⟩
        · have hpre : (Sum.inr : α → α ⊕ α) ⁻¹'
              ((Sum.inr : α → α ⊕ α) '' s) = s := by
            ext x
            simp
          simpa [nhds_inr, hpre] using hs
        · rintro _ ⟨x, hx, rfl⟩
          exact hsub hx
  let R : Measure (Ω × Ω) := P.prod P
  let H : Ω × Ω → C(α ⊕ α, ℝ) := fun z => encodePair (F z.1) (F z.2)
  let G : Ω × Ω → C(α ⊕ α, ℝ) := fun z =>
    encodePair ((Real.sqrt 2)⁻¹ • (F z.1 - F z.2))
      ((Real.sqrt 2)⁻¹ • (F z.1 + F z.2))
  have hHmeas : Measurable H := by
    apply ContinuousMap.measurable_iff_eval.2
    intro i
    cases i with
    | inl x => exact (ContinuousMap.measurable_eval x).comp (hF.comp measurable_fst)
    | inr x => exact (ContinuousMap.measurable_eval x).comp (hF.comp measurable_snd)
  have hGmeas : Measurable G := by
    apply ContinuousMap.measurable_iff_eval.2
    intro i
    cases i with
    | inl x =>
        exact (((ContinuousMap.measurable_eval x).comp (hF.comp measurable_fst)).sub
          ((ContinuousMap.measurable_eval x).comp (hF.comp measurable_snd))).const_mul _
    | inr x =>
        exact (((ContinuousMap.measurable_eval x).comp (hF.comp measurable_fst)).add
          ((ContinuousMap.measurable_eval x).comp (hF.comp measurable_snd))).const_mul _
  have hHproc : IsGaussianProcess (fun i z => H z i) R := by
    simpa [H, encodePair, R] using copySumProcess_isGaussian F hF hX
  have hGproc : IsGaussianProcess (fun i z => G z i) R := by
    convert rotatedCopySumProcess_isGaussian F hF hX using 1
    funext i z
    cases i with
    | inl x => simp [G, encodePair, ContinuousMap.smul_apply, smul_eq_mul]
    | inr x =>
        simp only [G, encodePair, Sum.elim_inr, ContinuousMap.coe_mk,
          ContinuousMap.smul_apply, ContinuousMap.add_apply]
        ring
  have hmeanA (x : α) : ∫ z, F z.1 x ∂R = 0 := by
    have hfx : Measurable (fun ω => F ω x) :=
      (ContinuousMap.measurable_eval x).comp hF
    have hInt : Integrable (fun z : Ω × Ω => F z.1 x) R := by
      exact ((hX.hasGaussianLaw_eval x).memLp_two.comp_fst P).integrable (by norm_num)
    calc
      ∫ z : Ω × Ω, F z.1 x ∂R = ∫ ω, F ω x ∂R.map Prod.fst := by
        simpa using (integral_map measurable_fst.aemeasurable
          (by simpa [R] using hfx.aestronglyMeasurable)).symm
      _ = ∫ ω, F ω x ∂P := by simp [R]
      _ = 0 := hmean x
  have hmeanB (x : α) : ∫ z, F z.2 x ∂R = 0 := by
    have hfx : Measurable (fun ω => F ω x) :=
      (ContinuousMap.measurable_eval x).comp hF
    have hInt : Integrable (fun z : Ω × Ω => F z.2 x) R := by
      exact ((hX.hasGaussianLaw_eval x).memLp_two.comp_snd P).integrable (by norm_num)
    calc
      ∫ z : Ω × Ω, F z.2 x ∂R = ∫ ω, F ω x ∂R.map Prod.snd := by
        simpa using (integral_map measurable_snd.aemeasurable
          (by simpa [R] using hfx.aestronglyMeasurable)).symm
      _ = ∫ ω, F ω x ∂P := by simp [R]
      _ = 0 := hmean x
  have hmeanH : ∀ i, ∫ z, H z i ∂R = 0 := by
    intro i
    cases i with
    | inl x => simpa [H, encodePair] using hmeanA x
    | inr x => simpa [H, encodePair] using hmeanB x
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hc : c ^ 2 = (1 / 2 : ℝ) := by
    dsimp [c]
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith
  have hmeanG : ∀ i, ∫ z, G z i ∂R = 0 := by
    intro i
    cases i with
    | inl x =>
        have hfirst : Integrable (fun z : Ω × Ω => F z.1 x) R :=
          ((hX.hasGaussianLaw_eval x).memLp_two.comp_fst P).integrable (by norm_num)
        have hsecond : Integrable (fun z : Ω × Ω => F z.2 x) R :=
          ((hX.hasGaussianLaw_eval x).memLp_two.comp_snd P).integrable (by norm_num)
        simp only [G, encodePair, Sum.elim_inl, ContinuousMap.coe_mk,
          ContinuousMap.smul_apply, ContinuousMap.sub_apply, c]
        rw [integral_smul, integral_sub hfirst hsecond, hmeanA x, hmeanB x]
        simp
    | inr x =>
        have hfirst : Integrable (fun z : Ω × Ω => F z.1 x) R :=
          ((hX.hasGaussianLaw_eval x).memLp_two.comp_fst P).integrable (by norm_num)
        have hsecond : Integrable (fun z : Ω × Ω => F z.2 x) R :=
          ((hX.hasGaussianLaw_eval x).memLp_two.comp_snd P).integrable (by norm_num)
        simp only [G, encodePair, Sum.elim_inr, ContinuousMap.coe_mk,
          ContinuousMap.smul_apply, ContinuousMap.add_apply, c]
        rw [integral_smul, integral_add hfirst hsecond, hmeanA x, hmeanB x]
        simp
  have hcoordMem (x : α) (b : Bool) : MemLp
      (fun z : Ω × Ω => if b then F z.1 x else F z.2 x) 2 R := by
    cases b
    · exact (hX.hasGaussianLaw_eval x).memLp_two.comp_snd P
    · exact (hX.hasGaussianLaw_eval x).memLp_two.comp_fst P
  have hAA (x y : α) : cov[fun z : Ω × Ω => F z.1 x,
      fun z => F z.1 y; R] = cov[fun ω => F ω x, fun ω => F ω y; P] := by
    have hx : MemLp (fun ω => F ω x) 2 P := (hX.hasGaussianLaw_eval x).memLp_two
    have hy : MemLp (fun ω => F ω y) 2 P := (hX.hasGaussianLaw_eval y).memLp_two
    calc
      _ = cov[fun ω => F ω x, fun ω => F ω y; (P.prod P).map Prod.fst] :=
        (covariance_map (by simpa [R] using hx.aestronglyMeasurable)
          (by simpa [R] using hy.aestronglyMeasurable) measurable_fst.aemeasurable).symm
      _ = _ := by simp [R]
  have hBB (x y : α) : cov[fun z : Ω × Ω => F z.2 x,
      fun z => F z.2 y; R] = cov[fun ω => F ω x, fun ω => F ω y; P] := by
    have hx : MemLp (fun ω => F ω x) 2 P := (hX.hasGaussianLaw_eval x).memLp_two
    have hy : MemLp (fun ω => F ω y) 2 P := (hX.hasGaussianLaw_eval y).memLp_two
    calc
      _ = cov[fun ω => F ω x, fun ω => F ω y; (P.prod P).map Prod.snd] :=
        (covariance_map (by simpa [R] using hx.aestronglyMeasurable)
          (by simpa [R] using hy.aestronglyMeasurable) measurable_snd.aemeasurable).symm
      _ = _ := by simp [R]
  have hABcov (x y : α) : cov[fun z : Ω × Ω => F z.1 x,
      fun z => F z.2 y; R] = 0 := by
    exact covariance_fst_snd_prod
      ((hX.hasGaussianLaw_eval x).memLp_two) ((hX.hasGaussianLaw_eval y).memLp_two)
  have hBAcov (x y : α) : cov[fun z : Ω × Ω => F z.2 x,
      fun z => F z.1 y; R] = 0 := by
    rw [covariance_comm]
    exact hABcov y x
  have hcov : ∀ i j, cov[fun z => H z i, fun z => H z j; R] =
      cov[fun z => G z i, fun z => G z j; R] := by
    intro i j
    simp only [H, G, encodePair, Sum.elim_inl, Sum.elim_inr,
      ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      ContinuousMap.sub_apply, ContinuousMap.add_apply]
    cases i with
    | inl x =>
      cases j with
      | inl y =>
        simp only [Sum.elim_inl, Sum.elim_inr]
        let X : Ω × Ω → ℝ := fun z => F z.1 x
        let Y : Ω × Ω → ℝ := fun z => F z.2 x
        let U : Ω × Ω → ℝ := fun z => F z.1 y
        let V : Ω × Ω → ℝ := fun z => F z.2 y
        have hX' : MemLp X 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_fst P
        have hY' : MemLp Y 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_snd P
        have hU' : MemLp U 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_fst P
        have hV' : MemLp V 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_snd P
        have hlin := covariance_linear_combination hX' hY' hU' hV' c (-c) c (-c)
        have hleft : (fun z => c * X z + (-c) * Y z) = (fun z => c * (X z - Y z)) := by
          funext z
          ring
        have hright : (fun z => c * U z + (-c) * V z) = (fun z => c * (U z - V z)) := by
          funext z
          ring
        rw [hleft, hright] at hlin
        change covariance X U R = covariance
          (fun z => c * (X z - Y z)) (fun z => c * (U z - V z)) R
        rw [hlin]
        rw [hAA x y, hBB x y, hABcov x y, hBAcov x y]
        have hcc : c * c = (1 / 2 : ℝ) := by nlinarith [hc]
        simp only [mul_neg, neg_mul, neg_neg, hcc]
        ring
      | inr y =>
        simp only [Sum.elim_inl, Sum.elim_inr]
        let X : Ω × Ω → ℝ := fun z => F z.1 x
        let Y : Ω × Ω → ℝ := fun z => F z.2 x
        let U : Ω × Ω → ℝ := fun z => F z.1 y
        let V : Ω × Ω → ℝ := fun z => F z.2 y
        have hX' : MemLp X 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_fst P
        have hY' : MemLp Y 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_snd P
        have hU' : MemLp U 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_fst P
        have hV' : MemLp V 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_snd P
        have hlin := covariance_linear_combination hX' hY' hU' hV' c (-c) c c
        have hleft : (fun z => c * X z + (-c) * Y z) = (fun z => c * (X z - Y z)) := by
          funext z
          ring
        have hright : (fun z => c * U z + c * V z) = (fun z => c * (U z + V z)) := by
          funext z
          ring
        rw [hleft, hright] at hlin
        change covariance X V R = covariance
          (fun z => c * (X z - Y z)) (fun z => c * (U z + V z)) R
        rw [hlin]
        rw [hAA x y, hBB x y, hABcov x y, hBAcov x y]
        have hcc : c * c = (1 / 2 : ℝ) := by nlinarith [hc]
        simp only [mul_neg, neg_mul, neg_neg, hcc]
        ring
    | inr x =>
      cases j with
      | inl y =>
        simp only [Sum.elim_inl, Sum.elim_inr]
        let X : Ω × Ω → ℝ := fun z => F z.1 x
        let Y : Ω × Ω → ℝ := fun z => F z.2 x
        let U : Ω × Ω → ℝ := fun z => F z.1 y
        let V : Ω × Ω → ℝ := fun z => F z.2 y
        have hX' : MemLp X 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_fst P
        have hY' : MemLp Y 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_snd P
        have hU' : MemLp U 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_fst P
        have hV' : MemLp V 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_snd P
        have hlin := covariance_linear_combination hX' hY' hU' hV' c c c (-c)
        have hleft : (fun z => c * X z + c * Y z) = (fun z => c * (X z + Y z)) := by
          funext z
          ring
        have hright : (fun z => c * U z + (-c) * V z) = (fun z => c * (U z - V z)) := by
          funext z
          ring
        rw [hleft, hright] at hlin
        change covariance Y U R = covariance
          (fun z => c * (X z + Y z)) (fun z => c * (U z - V z)) R
        rw [hlin]
        rw [hAA x y, hBB x y, hABcov x y, hBAcov x y]
        have hcc : c * c = (1 / 2 : ℝ) := by nlinarith [hc]
        simp only [mul_neg, neg_mul, neg_neg, hcc]
        ring
      | inr y =>
        simp only [Sum.elim_inl, Sum.elim_inr]
        let X : Ω × Ω → ℝ := fun z => F z.1 x
        let Y : Ω × Ω → ℝ := fun z => F z.2 x
        let U : Ω × Ω → ℝ := fun z => F z.1 y
        let V : Ω × Ω → ℝ := fun z => F z.2 y
        have hX' : MemLp X 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_fst P
        have hY' : MemLp Y 2 R := (hX.hasGaussianLaw_eval x).memLp_two.comp_snd P
        have hU' : MemLp U 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_fst P
        have hV' : MemLp V 2 R := (hX.hasGaussianLaw_eval y).memLp_two.comp_snd P
        have hlin := covariance_linear_combination hX' hY' hU' hV' c c c c
        have hleft : (fun z => c * X z + c * Y z) = (fun z => c * (X z + Y z)) := by
          funext z
          ring
        have hright : (fun z => c * U z + c * V z) = (fun z => c * (U z + V z)) := by
          funext z
          ring
        rw [hleft, hright] at hlin
        change covariance Y V R = covariance
          (fun z => c * (X z + Y z)) (fun z => c * (U z + V z)) R
        rw [hlin]
        rw [hAA x y, hBB x y, hABcov x y, hBAcov x y]
        have hcc : c * c = (1 / 2 : ℝ) := by nlinarith [hc]
        simp only [mul_neg, neg_mul, neg_neg, hcc]
        ring
  have hpath := AlignmentPaperGaussianFeatureBridge.continuous_path_law_eq_of_same_covariance
    H G hHmeas hGmeas hHproc hGproc hmeanH hmeanG hcov
  let μ : Measure C(α, ℝ) := P.map F
  have hpairMap : R.map (fun z : Ω × Ω => (F z.1, F z.2)) = μ.prod μ := by
    change (P.prod P).map (Prod.map F F) = (P.map F).prod (P.map F)
    exact (Measure.map_prod_map P P hF hF).symm
  have hrot : (μ.prod μ).map (ContinuousLinearMap.rotation (-(Real.pi / 4))) =
      μ.prod μ := by
    let il : C(α, α ⊕ α) := ⟨Sum.inl, continuous_inl⟩
    let ir : C(α, α ⊕ α) := ⟨Sum.inr, continuous_inr⟩
    have hcoeff : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith
    let D : C(α ⊕ α, ℝ) → C(α, ℝ) × C(α, ℝ) := fun f =>
      (f.comp il, f.comp ir)
    have hDmeas : Measurable D := by
      apply (ContinuousMap.measurable_iff_eval.2 ?_).prodMk
        (ContinuousMap.measurable_iff_eval.2 ?_)
      · intro x
        exact ContinuousMap.measurable_eval (Sum.inl x)
      · intro x
        exact ContinuousMap.measurable_eval (Sum.inr x)
    have hDH : (fun z => D (H z)) = (fun z : Ω × Ω => (F z.1, F z.2)) := by
      funext z
      apply Prod.ext <;> ext x <;>
        simp [D, H, encodePair, il, ir, ContinuousMap.comp_apply]
    have hDG : (fun z => D (G z)) = (fun z : Ω × Ω =>
        ContinuousLinearMap.rotation (-(Real.pi / 4)) (F z.1, F z.2)) := by
      funext z
      apply Prod.ext <;> ext x <;>
        simp [D, G, encodePair, il, ir, ContinuousMap.comp_apply,
          ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.sin_neg,
          Real.cos_pi_div_four, Real.sin_pi_div_four, smul_eq_mul]
      all_goals rw [hcoeff]
      all_goals ring
    have hDH' : D ∘ H = (fun z : Ω × Ω => (F z.1, F z.2)) := by
      funext z
      exact congrFun hDH z
    have hDG' : D ∘ G = (fun z : Ω × Ω =>
        ContinuousLinearMap.rotation (-(Real.pi / 4)) (F z.1, F z.2)) := by
      funext z
      exact congrFun hDG z
    have hpush : R.map (fun z : Ω × Ω => (F z.1, F z.2)) =
        R.map (fun z : Ω × Ω =>
          ContinuousLinearMap.rotation (-(Real.pi / 4)) (F z.1, F z.2)) := by
      have := congrArg (Measure.map D) hpath
      rw [Measure.map_map hDmeas hHmeas, Measure.map_map hDmeas hGmeas] at this
      rw [hDH', hDG'] at this
      exact this
    calc
      (μ.prod μ).map (ContinuousLinearMap.rotation (-(Real.pi / 4))) =
          (R.map (fun z : Ω × Ω => (F z.1, F z.2))).map
            (ContinuousLinearMap.rotation (-(Real.pi / 4))) := by rw [hpairMap]
      _ = R.map (fun z : Ω × Ω =>
          ContinuousLinearMap.rotation (-(Real.pi / 4)) (F z.1, F z.2)) := by
            rw [Measure.map_map (by fun_prop)
              (by fun_prop : Measurable (fun z : Ω × Ω => (F z.1, F z.2)))]
            rfl
      _ = R.map (fun z : Ω × Ω => (F z.1, F z.2)) := hpush.symm
      _ = μ.prod μ := hpairMap
  simpa [μ] using hrot

/-- Centered continuous Gaussian paths have a finite fourth norm moment. The
proof uses the actual path-law rotation identity above and the pinned Fernique
integrability theorem, then pulls the moment back along the path map. -/
theorem centeredGaussian_path_memLp_fourth
    {α Ω : Type*} [TopologicalSpace α] [CompactSpace α] [T2Space α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0) :
    MemLp F 4 P := by
  let μ : Measure C(α, ℝ) := P.map F
  have hrot := centeredGaussian_pathPair_rotation_invariant F hF hX hmean
  obtain ⟨C, hCpos, hExp⟩ :=
    exists_integrable_exp_sq_of_map_rotation_eq_self (μ := μ) hrot
  have hExpNeg : Integrable (fun x : C(α, ℝ) => Real.exp (-C * ‖x‖ ^ 2)) μ := by
    refine integrable_of_le_of_le (g₁ := 0) (g₂ := 1) (by fun_prop)
      (ae_of_all _ fun _ => by positivity) ?_ (integrable_const _) (integrable_const _)
    filter_upwards with x
    simp only [neg_mul, Pi.one_apply, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity
  have hsubset : Set.Ioo (-C) C ⊆
      interior (integrableExpSet (fun x : C(α, ℝ) => ‖x‖ ^ 2) μ) := by
    rw [IsOpen.subset_interior_iff isOpen_Ioo]
    exact fun v hv => integrable_exp_mul_of_le_of_le hExpNeg hExp hv.1.le hv.2.le
  have hzero : (0 : ℝ) ∈
      interior (integrableExpSet (fun x : C(α, ℝ) => ‖x‖ ^ 2) μ) :=
    hsubset ⟨by linarith, hCpos⟩
  have hsq : MemLp (fun x : C(α, ℝ) => ‖x‖ ^ 2) (2 : NNReal) μ :=
    memLp_of_mem_interior_integrableExpSet hzero 2
  have hid : MemLp id (4 : ENNReal) μ := by
    rw [← memLp_norm_rpow_iff (q := 2) (by fun_prop) (by simp) (by simp)]
    have hp : (4 : ENNReal) / 2 = 2 := by
      rw [show (4 : ENNReal) = 2 * 2 by norm_num, div_eq_mul_inv, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    rw [hp]
    simpa using hsq
  have hpull := hid.comp_of_map hF.aemeasurable
  simpa [μ] using hpull

/-- Explicit finite fourth tail integral for the actual continuous path law. -/
theorem centeredGaussian_path_fourth_lintegral_finite
    {α Ω : Type*} [TopologicalSpace α] [CompactSpace α] [T2Space α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0) :
    ∃ M_fourth, M_fourth ≠ (⊤ : ENNReal) ∧
      MeasureTheory.lintegral (P.map F) (fun f : C(α, ℝ) => edist f 0 ^ (4 : ℕ)) ≤ M_fourth := by
  have hF4 := centeredGaussian_path_memLp_fourth F hF hX hmean
  have hid : MemLp id (4 : ENNReal) (P.map F) := by
    rw [memLp_map_measure_iff (by fun_prop) hF.aemeasurable]
    simpa using hF4
  have hfinite : (MeasureTheory.lintegral (P.map F)
      (fun f : C(α, ℝ) => ‖f‖ₑ ^ (4 : ℝ))) < (⊤ : ENNReal) := by
    simpa using (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (4 : ENNReal) ≠ 0)
      (by norm_num : (4 : ENNReal) ≠ (⊤ : ENNReal)) (by fun_prop)).mp
        hid.eLpNorm_lt_top
  refine ⟨MeasureTheory.lintegral (P.map F)
    (fun f : C(α, ℝ) => edist f 0 ^ (4 : ℕ)), ?_, le_rfl⟩
  have heq : (fun f : C(α, ℝ) => edist f 0 ^ (4 : ℕ)) =
      (fun f => ‖f‖ₑ ^ (4 : ℝ)) := by
    funext f
    simp
  rw [heq]
  exact ne_of_lt hfinite

end BrownianSharp.AlignmentPaperContinuousGaussianFernique
