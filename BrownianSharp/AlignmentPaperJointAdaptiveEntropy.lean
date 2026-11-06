import BrownianSharp.AlignmentPaperJointDictionary
import BrownianSharp.AlignmentPaperSparseHead
import BrownianSharp.AlignmentPaperNonlinearEntropyCover
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.Fintype.Powerset

/-! Adaptive sparse-head and KGG approximation chains for the actual finite
common-grid dictionary. -/

noncomputable section
open scoped BigOperators ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

namespace BrownianSharp.AlignmentPaperJointAdaptiveEntropy

open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperLpJointDvp

/-- With a fixed KGG subspace, one input-dependent sparse-head approximation
for the actual finite-dimensional `ℓᵖ` image. -/
theorem joint_lpball_head_kgg_approximation_of_dictionary {d n m : ℕ}
    {p B : ℝ} (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (s : ℕ) (hs : 1 ≤ s)
    (hslo : (m : ℝ) / (400 * (Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1)) ≤ (s : ℝ))
    (V : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)))
    (hVrank : Module.rank ℝ V ≤ (m : Cardinal))
    (happrox : ∀ z : EuclideanSpace ℝ (Fin (JointSampleDimension d n)), ‖z‖ ≤ 1 →
      ∃ y ∈ V, ‖featureMap (d := d) (n := n) z - y‖ ≤
        2 * (Real.sqrt 50 *
          (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
            ((25 / 4 : ℝ) ^ d)) + 1) / Real.sqrt (s : ℝ)))
    (x : Fin (JointSampleDimension d n) → ℝ)
    (hx : (∑ i, |x i| ^ p) ≤ B ^ p) (hmpos : 0 < m) :
    ∃ A : Finset (Fin (JointSampleDimension d n)), A.card ≤ m ∧
      ∃ y ∈ V,
            ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
              featureMap (d := d) (n := n)
                (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) - y‖ ≤
              2 * Real.sqrt 50 *
                (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
                  ((25 / 4 : ℝ) ^ d)) + 1) /
                Real.sqrt (s : ℝ) *
                Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) := by
  classical
  obtain ⟨A, hA, _, htail⟩ :=
    BrownianSharp.AlignmentPaperSparseHead.exists_threshold_head_tail
      hp hp2 hB x hx hmpos
  let tail : Fin (JointSampleDimension d n) → ℝ :=
    BrownianSharp.AlignmentPaperSparseHead.thresholdTail A x
  let ztail : EuclideanSpace ℝ (Fin (JointSampleDimension d n)) := WithLp.toLp 2 tail
  let T : ℝ := Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p)
  have hrad : 0 < (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p := by positivity
  have hT : 0 < T := by dsimp [T]; exact Real.sqrt_pos.2 hrad
  have htail' : (∑ i, |tail i| ^ 2) ≤ T ^ 2 := by
    have hT2 : T ^ 2 = (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p := by
      dsimp [T]
      exact Real.sq_sqrt hrad.le
    rw [hT2]
    exact htail
  have hnormsq : ‖ztail‖ ^ 2 ≤ T ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [ztail, tail, sq_abs] using htail'
  have htailnorm : ‖ztail‖ ≤ T := by
    have hnorm0 := norm_nonneg ztail
    have hT0 := hT.le
    nlinarith
  have hxsplitFun : x =
      BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x + tail := by
    funext i
    by_cases hi : i ∈ A <;>
      simp [tail, BrownianSharp.AlignmentPaperSparseHead.thresholdHead,
        BrownianSharp.AlignmentPaperSparseHead.thresholdTail, hi]
  have hxsplit : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (JointSampleDimension d n))) =
      WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x) + ztail := by
    change WithLp.toLp 2 x =
      WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x) +
        WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdTail A x)
    rw [← WithLp.toLp_add]
    congr 1
  let u : EuclideanSpace ℝ (Fin (JointSampleDimension d n)) := T⁻¹ • ztail
  have hu : ‖u‖ ≤ 1 := by
    change ‖T⁻¹ • ztail‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hT.le)]
    exact (inv_mul_le_iff₀ hT).2 (by simpa using htailnorm)
  obtain ⟨y₀, hy₀, hyerr⟩ := happrox u hu
  let y : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) := T • y₀
  have hy : y ∈ V := V.smul_mem _ hy₀
  have huEq : ztail = T • u := by
    change ztail = T • (T⁻¹ • ztail)
    rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  have hF : featureMap (d := d) (n := n) ztail =
      T • featureMap (d := d) (n := n) u := by
    calc
      featureMap (d := d) (n := n) ztail =
          featureMap (d := d) (n := n) (T • u) := by rw [huEq]
      _ = T • featureMap (d := d) (n := n) u := map_smul _ _ _
  have hδ : 0 ≤ 2 * Real.sqrt 50 *
      (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d)) + 1) / Real.sqrt (s : ℝ) := by
    have hspos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hs)
    have hconstant : 0 < 2 * Real.sqrt 50 := by
      exact mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num))
    have hrowradius : 0 < Real.sqrt
        ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
          ((25 / 4 : ℝ) ^ d)) + 1 := by
      have hsqrt : 0 ≤ Real.sqrt
          ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
            ((25 / 4 : ℝ) ^ d)) := Real.sqrt_nonneg _
      linarith
    exact (div_pos (mul_pos hconstant hrowradius) (Real.sqrt_pos.2 hspos)).le
  have hyerr' : ‖featureMap (d := d) (n := n) u - y₀‖ ≤
      2 * Real.sqrt 50 *
        (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
          ((25 / 4 : ℝ) ^ d)) + 1) / Real.sqrt (s : ℝ) := by
    convert hyerr using 1 <;> ring
  have hdiff : featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
      featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) - y =
      T • (featureMap (d := d) (n := n) u - y₀) := by
    rw [hxsplit, map_add, hF]
    simp only [y]
    change featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) +
        T • featureMap (d := d) (n := n) u -
        featureMap (d := d) (n := n)
          (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) -
        T • y₀ = _
    abel
    simp [smul_add, smul_smul]
  refine ⟨A, hA, y, hy, ?_⟩
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT.le]
  have hscale := mul_le_mul_of_nonneg_left hyerr' hT.le
  nlinarith

/-- Extension by zero from a finite support label to the full Euclidean sample
space. -/
def supportExtensionMap {d n : ℕ} (A : Finset (Fin (JointSampleDimension d n))) :
    (A → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (JointSampleDimension d n)) where
  toFun v := WithLp.toLp 2 fun i => if hi : i ∈ A then v ⟨i, hi⟩ else 0
  map_add' v w := by
    ext i
    by_cases hi : i ∈ A <;> simp [hi]
  map_smul' c v := by
    ext i
    by_cases hi : i ∈ A <;> simp [hi]

/-- The target subspace generated by features of sample vectors supported on
one labelled finite set. -/
def supportHeadImage {d n : ℕ}
    (A : Finset (Fin (JointSampleDimension d n))) :
    Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) :=
  LinearMap.range ((featureMap (d := d) (n := n)).toLinearMap.comp
    (supportExtensionMap (d := d) (n := n) A))

theorem supportHeadImage_finrank_le {d n : ℕ}
    (A : Finset (Fin (JointSampleDimension d n))) :
    Module.finrank ℝ (supportHeadImage (d := d) (n := n) A) ≤ A.card := by
  calc
    Module.finrank ℝ (supportHeadImage (d := d) (n := n) A) ≤
        Module.finrank ℝ (A → ℝ) := LinearMap.finrank_range_le _
    _ = A.card := by simp [Module.finrank_pi_fintype]

theorem thresholdHead_feature_mem_supportHeadImage {d n : ℕ}
    (A : Finset (Fin (JointSampleDimension d n)))
    (x : Fin (JointSampleDimension d n) → ℝ) :
    featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) ∈
      supportHeadImage (d := d) (n := n) A := by
  refine ⟨fun a : A => x a.1, ?_⟩
  change featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) =
    featureMap (d := d) (n := n)
      (supportExtensionMap (d := d) (n := n) A (fun a : A => x a.1))
  congr 1

/-- A labelled increment space for two adjacent adaptive stages. -/
def labelledIncrementSubspace {d n : ℕ}
    (A B : Finset (Fin (JointSampleDimension d n)))
    (V W : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))) :
    Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) :=
  supportHeadImage (d := d) (n := n) A ⊔
    supportHeadImage (d := d) (n := n) B ⊔ V ⊔ W

theorem labelledIncrement_mem_of_stage_outputs {d n : ℕ}
    (A B : Finset (Fin (JointSampleDimension d n)))
    (V W : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)))
    (x : Fin (JointSampleDimension d n) → ℝ)
    (y z : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))
    (hy : y ∈ V) (hz : z ∈ W)
    (hA : featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) ∈
        supportHeadImage (d := d) (n := n) A)
    (hB : featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) ∈
        supportHeadImage (d := d) (n := n) B) :
    (featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z) ∈
      labelledIncrementSubspace (d := d) (n := n) A B V W := by
  let HA := supportHeadImage (d := d) (n := n) A
  let HB := supportHeadImage (d := d) (n := n) B
  let U := labelledIncrementSubspace (d := d) (n := n) A B V W
  have hHA : HA ≤ U := by
    dsimp [U, labelledIncrementSubspace, HA]
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_left))
  have hHB : HB ≤ U := by
    dsimp [U, labelledIncrementSubspace, HB]
    exact le_sup_of_le_left (le_sup_of_le_left (le_sup_right))
  have hV : V ≤ U := by
    dsimp [U, labelledIncrementSubspace]
    exact le_sup_of_le_left (le_sup_right)
  have hW : W ≤ U := by
    dsimp [U, labelledIncrementSubspace]
    exact le_sup_right
  have h1 : featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y ∈ U :=
    U.add_mem (hHA hA) (hV hy)
  have h2 : -(featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z) ∈ U :=
    U.neg_mem (U.add_mem (hHB hB) (hW hz))
  exact U.add_mem h1 h2

/-- A finite label for an input-dependent support of size at most r. -/
def SupportLabel {D r : ℕ} := {A : Finset (Fin D) // A.card ≤ r}

noncomputable instance supportLabelFintype {D r : ℕ} :
    Fintype (SupportLabel (D := D) (r := r)) := by
  classical
  letI : Fintype (Finset (Fin D)) := inferInstance
  exact Fintype.subtype
    (Finset.univ.filter fun A : Finset (Fin D) => A.card ≤ r)
    (by intro A; simp)

/-- The family of all possible adjacent-stage increment spaces, with both
sparse supports retained as explicit labels. -/
def supportPairIncrementFamily {d n r₁ r₂ : ℕ}
    (V W : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))) :
    Fin (Fintype.card (SupportLabel (D := JointSampleDimension d n) (r := r₁) ×
      SupportLabel (D := JointSampleDimension d n) (r := r₂))) →
      Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) := by
  let L₁ := SupportLabel (D := JointSampleDimension d n) (r := r₁)
  let L₂ := SupportLabel (D := JointSampleDimension d n) (r := r₂)
  let e := Fintype.equivFin (L₁ × L₂)
  exact fun i => labelledIncrementSubspace (d := d) (n := n)
    (e.symm i).1.1 (e.symm i).2.1 V W

theorem supportPairIncrementFamily_finrank_le {d n r₁ r₂ : ℕ}
    (V W : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)))
    (hV : Module.finrank ℝ V ≤ r₁) (hW : Module.finrank ℝ W ≤ r₂)
    (i : Fin (Fintype.card (SupportLabel (D := JointSampleDimension d n) (r := r₁) ×
      SupportLabel (D := JointSampleDimension d n) (r := r₂)))) :
    Module.finrank ℝ (supportPairIncrementFamily (d := d) (n := n)
      (r₁ := r₁) (r₂ := r₂) V W i) ≤ r₁ + r₁ + r₂ + r₂ := by
  classical
  let L₁ := SupportLabel (D := JointSampleDimension d n) (r := r₁)
  let L₂ := SupportLabel (D := JointSampleDimension d n) (r := r₂)
  let P : Type := L₁ × L₂
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let A : Finset (Fin (JointSampleDimension d n)) := (e.symm i).1.1
  let B : Finset (Fin (JointSampleDimension d n)) := (e.symm i).2.1
  let HA : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) :=
    supportHeadImage (d := d) (n := n) A
  let HB : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) :=
    supportHeadImage (d := d) (n := n) B
  have hA : Module.finrank ℝ HA ≤ r₁ :=
    (supportHeadImage_finrank_le (d := d) (n := n) A).trans (e.symm i).1.2
  have hB : Module.finrank ℝ HB ≤ r₂ :=
    (supportHeadImage_finrank_le (d := d) (n := n) B).trans (e.symm i).2.2
  have hs₁ : Module.finrank ℝ ↥(HA ⊔ HB) ≤ r₁ + r₂ := by
    exact (Submodule.finrank_add_le_finrank_add_finrank HA HB).trans (Nat.add_le_add hA hB)
  have hs₂ : Module.finrank ℝ ↥(HA ⊔ HB ⊔ V) ≤ r₁ + r₁ + r₂ := by
    calc
      _ ≤ Module.finrank ℝ ↥(HA ⊔ HB) + Module.finrank ℝ V :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ _ := by omega
  have hs₃ : Module.finrank ℝ ↥(HA ⊔ HB ⊔ V ⊔ W) ≤ r₁ + r₁ + r₂ + r₂ := by
    calc
      _ ≤ Module.finrank ℝ ↥(HA ⊔ HB ⊔ V) + Module.finrank ℝ W :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ _ := Nat.add_le_add hs₂ hW
  change Module.finrank ℝ ↥(HA ⊔ HB ⊔ V ⊔ W) ≤ r₁ + r₁ + r₂ + r₂
  exact hs₃

/-- Volumetric cover of every support-labelled adjacent-stage increment ball.
The finite family count remains explicit for the later binomial estimate. -/
theorem exists_supportPair_increment_piece {d n r₁ r₂ : ℕ}
    (V W : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)))
    (hV : Module.finrank ℝ V ≤ r₁) (hW : Module.finrank ℝ W ≤ r₂)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ p : Carl.CoverPiece
        (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)),
      p.source = AlignmentPaperNonlinearEntropyCover.familyBallSource
        (supportPairIncrementFamily (d := d) (n := n) (r₁ := r₁) (r₂ := r₂) V W) R ∧
      p.radius = NNReal.mk ε hε.le ∧
      p.centers.encard ≤
        (Fintype.card (SupportLabel (D := JointSampleDimension d n) (r := r₁) ×
          SupportLabel (D := JointSampleDimension d n) (r := r₂)) : ℕ∞) *
        ↑(Nat.ceil ((1 + 2 * R / ε) ^ (r₁ + r₁ + r₂ + r₂))) := by
  classical
  let Q := Fintype.card (SupportLabel (D := JointSampleDimension d n) (r := r₁) ×
    SupportLabel (D := JointSampleDimension d n) (r := r₂))
  let V' := supportPairIncrementFamily (d := d) (n := n)
    (r₁ := r₁) (r₂ := r₂) V W
  haveI : ∀ i : Fin Q, FiniteDimensional ℝ (V' i) := by
    intro i
    infer_instance
  haveI : ∀ i : Fin Q, CompleteSpace (V' i) := by
    intro i
    infer_instance
  obtain ⟨piece, hp, hr, hc⟩ :=
    AlignmentPaperNonlinearEntropyCover.exists_family_submodule_ball_piece
      Q V' hR hε
  refine ⟨piece, hp, hr, ?_⟩
  have hdim : Finset.univ.sup (fun i : Fin Q => Module.finrank ℝ (V' i)) ≤
      r₁ + r₁ + r₂ + r₂ := by
    apply Finset.sup_le
    intro i hi
    exact supportPairIncrementFamily_finrank_le V W hV hW i
  calc
    piece.centers.encard ≤ (Q : ℕ∞) *
        ↑(Nat.ceil ((1 + 2 * R / ε) ^
          Finset.univ.sup (fun i : Fin Q => Module.finrank ℝ (V' i)))) := hc
    _ ≤ (Q : ℕ∞) * ↑(Nat.ceil ((1 + 2 * R / ε) ^
          (r₁ + r₁ + r₂ + r₂))) := by
      have hbase : 1 ≤ 1 + 2 * R / ε := by
        have hdiv : 0 ≤ 2 * R / ε := div_nonneg (by positivity) hε.le
        linarith
      have hexp : (1 + 2 * R / ε) ^
          Finset.univ.sup (fun i : Fin Q => Module.finrank ℝ (V' i)) ≤
          (1 + 2 * R / ε) ^ (r₁ + r₁ + r₂ + r₂) :=
        pow_le_pow_right₀ hbase hdim
      have hceil := Nat.ceil_mono hexp
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hceil
      · exact zero_le

theorem jointStage_increment_norm_le {d n : ℕ}
    (x : Fin (JointSampleDimension d n) → ℝ)
    (A B : Finset (Fin (JointSampleDimension d n)))
    (y z : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))
    {δ₁ δ₂ : ℝ}
    (hA : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤ δ₁)
    (hB : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)‖ ≤ δ₂) :
    ‖(featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)‖ ≤
      δ₁ + δ₂ := by
  have hiden :
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y) -
        (featureMap (d := d) (n := n)
          (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z) =
        (featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)) -
        (featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)) := by
    abel
  rw [hiden]
  calc
    _ ≤ ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
        (featureMap (d := d) (n := n)
          (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)‖ +
        ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ :=
          norm_sub_le _ _
    _ ≤ δ₂ + δ₁ := add_le_add hB hA
    _ = δ₁ + δ₂ := by ring

end BrownianSharp.AlignmentPaperJointAdaptiveEntropy
