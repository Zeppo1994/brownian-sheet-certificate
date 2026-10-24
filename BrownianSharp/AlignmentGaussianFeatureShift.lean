import BrownianSharp.BrownianCriticalResidual
import BrownianSharp.AlignmentGaussianShift
import BrownianSharp.AlignmentGaussianFiniteSourceModel
import BrownianSharp.AlignmentAuditGaussianShift
import BrownianSharp.AlignmentIsonormalReindex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory InnerProductSpace HaarQuarter
open scoped RealInnerProductSpace BigOperators
open BrownianSharp.AlignmentGaussianFiniteSourceModel
open BrownianSharp.AlignmentGaussianShift

namespace BrownianSharp.AlignmentGaussianFeatureShift

private def featureSynthesis {H ι η : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : ι → H) (f : η → H) (z : ι → ℝ) : η → ℝ :=
  fun j => ∑ i, ⟪b i, f j⟫ * z i

private theorem isonormal_eval_memLp {H Ω κ : Type*} [Fintype κ] [Nonempty κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : IsonormalGaussianFamily H Ω κ P) (f : H) :
    MemLp (fun ω => W.eval f ω) 2 P := by
  classical
  let i₀ : κ := Classical.choice ‹Nonempty κ›
  have h := W.jointlyGaussian (fun i : κ => if i = i₀ then f else 0)
  have hi := (h.eval i₀).memLp_two
  convert hi using 1 <;> simp [i₀]

private noncomputable def isonormalEvalToLp {H Ω κ : Type*} [Fintype κ]
    [Nonempty κ] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : IsonormalGaussianFamily H Ω κ P) :
    H →ₗᵢ[ℝ] Lp ℝ 2 P := by
  let Tmem := fun f : H => isonormal_eval_memLp W f
  refine {
    toLinearMap := {
      toFun := fun f => (Tmem f).toLp (fun ω => W.eval f ω)
      map_add' := ?_
      map_smul' := ?_ }
    norm_map' := ?_ }
  · intro f g
    rw [← MemLp.toLp_add (Tmem f) (Tmem g)]
    exact MemLp.toLp_congr (Tmem (f + g)) ((Tmem f).add (Tmem g))
      (isonormal_eval_add_ae W f g)
  · intro c f
    exact MemLp.toLp_congr (Tmem (c • f)) ((Tmem f).const_smul c)
      (isonormal_eval_smul_ae W f c)
  · intro f
    have hmem := Tmem f
    have hmeas : Measurable (fun ω => W.eval f ω) := W.measurable_eval f
    have hmean : ∫ ω, W.eval f ω ∂P = 0 := W.mean_zero f
    have hmoment : ∫ ω, (W.eval f ω) ^ 2 ∂P = ‖f‖ ^ 2 := by
      calc
        ∫ ω, (W.eval f ω) ^ 2 ∂P = variance (fun ω => W.eval f ω) P := by
          symm
          exact variance_of_integral_eq_zero hmeas.aemeasurable hmean
        _ = covariance (fun ω => W.eval f ω) (fun ω => W.eval f ω) P := by
          rw [← covariance_self hmeas.aemeasurable]
        _ = ‖f‖ ^ 2 := by
          rw [W.covariance_eq_inner, real_inner_self_eq_norm_sq]
    have hnorm : ‖hmem.toLp (fun ω => W.eval f ω)‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      calc
        ∫ ω, ⟪hmem.toLp (fun ω => W.eval f ω) ω,
            hmem.toLp (fun ω => W.eval f ω) ω⟫ ∂P =
            ∫ ω, (W.eval f ω) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp hmem] with ω hω
          rw [hω]
          simp [real_inner_self_eq_norm_sq, pow_two]
        _ = ‖f‖ ^ 2 := hmoment
    change ‖hmem.toLp (fun ω => W.eval f ω)‖ = ‖f‖
    nlinarith [norm_nonneg (hmem.toLp (fun ω => W.eval f ω)), norm_nonneg f]

private theorem isonormalEvalToLp_ae {H Ω κ : Type*} [Fintype κ]
    [Nonempty κ] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : IsonormalGaussianFamily H Ω κ P) :
    ∀ f, W.eval f =ᵐ[P] fun ω => isonormalEvalToLp W f ω := by
  intro f
  exact ((isonormal_eval_memLp W f).coeFn_toLp).symm

/-- A centered finite Gaussian vector whose covariance is a feature Gram
matrix obeys the Cameron--Martin lower shift inequality.  A nonempty
orthonormal source frame is supplied only to invoke the finite-source model;
the final shift is projected onto the span of the evaluation features, so its
energy never exceeds the original source energy. -/
theorem finiteGaussian_gram_shift_lower
    {Ω I J H : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Nonempty I] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (X : Ω → J → ℝ) (e : I → H) (v : J → H)
    (hX : HasGaussianLaw (fun ω j => X ω j) P)
    (hmean : ∀ j, ∫ ω, X ω j ∂P = 0)
    (hcov : ∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P = ⟪v i, v j⟫)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0)
    (g : H) (ε : ℝ) :
    P {ω | ∀ j, |X ω j - ⟪v j, g⟫| ≤ ε} ≥
      ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) *
        P {ω | ∀ j, |X ω j| ≤ ε} := by
  classical
  let S := finiteFeatureSpan (Sum.elim e v)
  let Q : Measure S := ProbabilityTheory.stdGaussian S
  let vb : J → S := fun j =>
    ⟨v j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩
  obtain ⟨W₀, hLaw₀, _, _, _⟩ := exists_finiteFeatureSourceModel X e v hX hmean hcov he
  have hcard : Fintype.card (Fin (Module.finrank ℝ S)) ≤ Fintype.card (Sum I J) := by
    simp only [Fintype.card_fin]
    change (Set.range (Sum.elim e v)).finrank ℝ ≤ _
    exact finrank_range_le_card (Sum.elim e v)
  obtain ⟨W, hEval⟩ :=
    BrownianSharp.AlignmentIsonormalReindex.exists_reindexed_isonormal W₀ hcard
  have hLaw : Measure.map (gridVector X) P =
      Measure.map (gridVector (fun ω j => W.eval (vb j) ω)) Q := by
    rw [hLaw₀]
    congr 1
    funext ω
    apply congrArg (fun f : J → ℝ => (EuclideanSpace.equiv J ℝ).symm f)
    funext j
    change W₀.eval (vb j) ω = W.eval (vb j) ω
    exact (congrFun (congrFun hEval (vb j)) ω).symm
  have hdim : 0 < Module.finrank ℝ S := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := S)).2
    let i : I := Classical.choice ‹Nonempty I›
    refine ⟨⟨e i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩, ?_⟩
    intro hezero
    have hnorm : ‖e i‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, he i i]
      simp
    have : e i = 0 := congrArg Subtype.val hezero
    simp [this] at hnorm
  letI : Nonempty (Fin (Module.finrank ℝ S)) := Fin.pos_iff_nonempty.mp hdim
  let T := isonormalEvalToLp W
  have hWT : ∀ f, W.eval f =ᵐ[Q] fun ω => T f ω :=
    isonormalEvalToLp_ae W
  let bV : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S :=
    stdOrthonormalBasis ℝ S
  let b : Fin (Module.finrank ℝ S) → S := fun i => bV i
  have hb : Orthonormal ℝ b := by
    constructor
    · intro i
      change ‖bV i‖ = 1
      exact bV.orthonormal.1 i
    · intro i j hij
      change ⟪bV i, bV j⟫ = 0
      exact bV.orthonormal.2 hij
  have hf : ∀ j, vb j = ∑ i, ⟪b i, vb j⟫ • b i := by
    intro j
    exact (bV.sum_repr' (vb j)).symm
  let gS : S := S.orthogonalProjectionOnto g
  have hgcoord (j : J) : ⟪vb j, gS⟫ = ⟪v j, g⟫ := by
    simpa [vb, gS] using S.inner_orthogonalProjectionOnto_eq_of_mem_left
      (vb j) g
  have hgNorm : ‖gS‖ ≤ ‖g‖ := S.norm_orthogonalProjectionOnto_apply_le g
  have hfinite := isonormal_finite_feature_shift_lower W T hWT b hb vb hf gS ε
  let E₀ : Set (EuclideanSpace ℝ J) :=
    {z | ∀ j, |(EuclideanSpace.equiv J ℝ z) j| ≤ ε}
  let E₁ : Set (EuclideanSpace ℝ J) :=
    {z | ∀ j, |(EuclideanSpace.equiv J ℝ z) j - ⟪v j, g⟫| ≤ ε}
  have hE₀ : MeasurableSet E₀ := by
    rw [show E₀ = ⋂ j, {z | |(EuclideanSpace.equiv J ℝ) z j| ≤ ε} by
      ext z
      simp [E₀]]
    exact MeasurableSet.iInter fun j =>
      isClosed_Iic.measurableSet.preimage
        (continuous_abs.measurable.comp
          (((continuous_apply j).comp (EuclideanSpace.equiv J ℝ).continuous).measurable))
  have hE₁ : MeasurableSet E₁ := by
    rw [show E₁ = ⋂ j, {z | |(EuclideanSpace.equiv J ℝ) z j - ⟪v j, g⟫| ≤ ε} by
      ext z
      simp [E₁]]
    exact MeasurableSet.iInter fun j =>
      isClosed_Iic.measurableSet.preimage
        (continuous_abs.measurable.comp
          ((((continuous_apply j).comp (EuclideanSpace.equiv J ℝ).continuous).sub
            continuous_const).measurable))
  let F : Ω → EuclideanSpace ℝ J := gridVector X
  let G : S → EuclideanSpace ℝ J := fun ω =>
    gridVector (fun ω j => W.eval (vb j) ω) ω
  have hFmeas : AEMeasurable F P := by
    change AEMeasurable ((EuclideanSpace.equiv J ℝ).symm ∘ (fun ω j => X ω j)) P
    exact ((EuclideanSpace.equiv J ℝ).symm.continuous.measurable.aemeasurable
      (μ := P.map (fun ω j => X ω j))).comp_aemeasurable hX.aemeasurable
  have hGmeas : Measurable G := by
    change Measurable ((EuclideanSpace.equiv J ℝ).symm ∘
      (fun ω j => W.eval (vb j) ω))
    exact (EuclideanSpace.equiv J ℝ).symm.continuous.measurable.comp
      (Measurable.of_eval (fun j => W.measurable_eval (vb j)))
  have hcenterF : P {ω | ∀ j, |X ω j| ≤ ε} = (P.map F) E₀ := by
    rw [Measure.map_apply_of_aemeasurable hFmeas hE₀]
    apply congrArg P
    ext ω
    simp [F, E₀, gridVector]
  have hshiftF : P {ω | ∀ j, |X ω j - ⟪v j, g⟫| ≤ ε} = (P.map F) E₁ := by
    rw [Measure.map_apply_of_aemeasurable hFmeas hE₁]
    apply congrArg P
    ext ω
    simp [F, E₁, gridVector]
  have hcenterG : Q {ω | ∀ j, |W.eval (vb j) ω| ≤ ε} = (Q.map G) E₀ := by
    rw [Measure.map_apply hGmeas hE₀]
    apply congrArg Q
    ext ω
    simp [G, E₀, gridVector]
  have hshiftG : Q {ω | ∀ j, |W.eval (vb j) ω - ⟪v j, g⟫| ≤ ε} = (Q.map G) E₁ := by
    rw [Measure.map_apply hGmeas hE₁]
    apply congrArg Q
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iInter]
    constructor
    · intro hh j
      simpa [G, E₁, gridVector, hgcoord j] using hh j
    · intro hh j
      simpa [G, E₁, gridVector, hgcoord j] using hh j
  calc
    P {ω | ∀ j, |X ω j - ⟪v j, g⟫| ≤ ε} = (P.map F) E₁ := hshiftF
    _ = (Q.map G) E₁ := by rw [hLaw]
    _ = Q {ω | ∀ j, |W.eval (vb j) ω - ⟪v j, g⟫| ≤ ε} := hshiftG.symm
    _ ≥ ENNReal.ofReal (Real.exp (-‖gS‖ ^ 2 / 2)) *
        Q {ω | ∀ j, |W.eval (vb j) ω| ≤ ε} := by
      simpa [hgcoord] using hfinite
    _ ≥ ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) *
        Q {ω | ∀ j, |W.eval (vb j) ω| ≤ ε} := by
      apply mul_le_mul_of_nonneg_right
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hprod := mul_nonneg (sub_nonneg.mpr hgNorm)
        (add_nonneg (norm_nonneg g) (norm_nonneg gS))
      nlinarith [hprod]
      positivity
    _ = ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) *
        P {ω | ∀ j, |X ω j| ≤ ε} := by rw [hcenterG, ← hLaw, ← hcenterF]

end BrownianSharp.AlignmentGaussianFeatureShift
