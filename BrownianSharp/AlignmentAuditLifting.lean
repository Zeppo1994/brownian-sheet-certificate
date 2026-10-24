import BrownianSharp.AlignmentAuditCoding
import BrownianSharp.CameronMartin
import BrownianSharp.EntropyCoverInversion
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open scoped ENNReal NNReal
open HaarQuarter

namespace BrownianSharp.AlignmentAuditLifting

variable {K : Type*} [MetricSpace K]
variable {n : ℕ}

/-- A finite pointwise maximum, with zero included as the empty-family value. -/
def finiteMax (l : List (Fin n)) (g : Fin n → K → ℝ) : K → ℝ :=
  l.foldr (fun i acc x => max (g i x) (acc x)) 0

lemma finiteMax_lipschitz (l : List (Fin n)) (g : Fin n → K → ℝ)
    (hg : ∀ i ∈ l, LipschitzWith 1 (g i)) :
    LipschitzWith 1 (finiteMax l g) := by
  induction l with
  | nil =>
      change LipschitzWith 1 (fun _ : K => (0 : ℝ))
      exact LipschitzWith.of_le_add (fun _ _ => by simp)
  | cons i l ih =>
    have hi : LipschitzWith 1 (g i) := hg i (by simp)
    have htail : LipschitzWith 1 (fun x : K => finiteMax l g x) := by
      apply ih
      intro j hj
      exact hg j (by simp [hj])
    simpa [finiteMax] using hi.max htail

lemma bump_lipschitz (δ : ℝ) (c : K) :
    LipschitzWith 1 (fun x : K => max (δ - dist x c) 0) := by
  have hraw : LipschitzWith 1 (fun x : K => δ - dist x c) := by
    refine LipschitzWith.of_le_add fun x y => ?_
    have hxy : dist y c ≤ dist x c + dist x y := by
      calc
        dist y c ≤ dist y x + dist x c := dist_triangle y x c
        _ = dist x c + dist x y := by rw [dist_comm y x, add_comm]
    linarith
  exact hraw.max_const 0

lemma finiteMax_le (l : List (Fin n)) (g : Fin n → K → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hg : ∀ i ∈ l, ∀ x, g i x ≤ δ) :
    ∀ x, finiteMax l g x ≤ δ := by
  induction l with
  | nil => intro x; simp [finiteMax]; exact hδ
  | cons i l ih =>
      intro x
      simp only [finiteMax, List.foldr]
      apply max_le
      · exact hg i (by simp) x
      · apply ih
        intro j hj y
        exact hg j (by simp [hj]) y

lemma finiteMax_le_at (l : List (Fin n)) (g : Fin n → K → ℝ) (δ : ℝ)
    (x : K) (hδ : 0 ≤ δ) (hg : ∀ i ∈ l, g i x ≤ δ) :
    finiteMax l g x ≤ δ := by
  induction l with
  | nil => simp [finiteMax, hδ]
  | cons i l ih =>
      simp only [finiteMax, List.foldr]
      apply max_le
      · exact hg i (by simp)
      · apply ih
        intro j hj
        exact hg j (by simp [hj])

lemma finiteMax_nonneg (l : List (Fin n)) (g : Fin n → K → ℝ)
    (hg : ∀ i ∈ l, ∀ x, 0 ≤ g i x) :
    ∀ x, 0 ≤ finiteMax l g x := by
  induction l with
  | nil => intro x; simp [finiteMax]
  | cons i l ih =>
      intro x
      simp only [finiteMax, List.foldr]
      apply le_max_of_le_right
      apply ih
      intro j hj y
      exact hg j (by simp [hj]) y

lemma finiteMax_ge_mem (l : List (Fin n)) (g : Fin n → K → ℝ) (i : Fin n)
    (hi : i ∈ l) : ∀ x, g i x ≤ finiteMax l g x := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
      intro x
      simp only [finiteMax, List.foldr]
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact le_max_left _ _
      · exact le_trans (ih hi x) (le_max_right _ _)

/-- The finite bump superposition associated to a binary labeling of finitely
many centers. -/
def bitBump (δ : ℝ) (centers : Fin n → K) (bits : Fin n → Bool) : K → ℝ :=
  finiteMax (List.finRange n) (fun i x =>
    if bits i then max (δ - dist x (centers i)) 0 else 0)

lemma bitBump_lipschitz (δ : ℝ) (centers : Fin n → K) (bits : Fin n → Bool) :
    LipschitzWith 1 (bitBump δ centers bits) := by
  apply finiteMax_lipschitz
  intro i hi
  by_cases hb : bits i
  · simpa [bitBump, hb] using bump_lipschitz δ (centers i)
  · simpa [bitBump, hb] using
      (LipschitzWith.of_le_add (fun _ _ => by simp) : LipschitzWith 1 (fun _ : K => (0 : ℝ)))

lemma bitBump_center (δ : ℝ) (hδ : 0 ≤ δ) (centers : Fin n → K)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (centers i) (centers j))
    (bits : Fin n → Bool) (i : Fin n) :
    bitBump δ centers bits (centers i) = if bits i then δ else 0 := by
  classical
  let g : Fin n → K → ℝ := fun j x =>
    if bits j then max (δ - dist x (centers j)) 0 else 0
  have hterm0 : ∀ j ∈ List.finRange n, ∀ x, 0 ≤ g j x := by
    intro j hj x
    dsimp [g]
    split_ifs <;> positivity
  have htermδ : ∀ j ∈ List.finRange n, ∀ x, g j x ≤ δ := by
    intro j hj x
    dsimp [g]
    split_ifs with hb
    · have hd : 0 ≤ dist x (centers j) := dist_nonneg
      exact max_le (by nlinarith [hd]) hδ
    · exact hδ
  have hmax_nonneg : 0 ≤ finiteMax (List.finRange n) g (centers i) :=
    finiteMax_nonneg _ _ hterm0 (centers i)
  have hmax_le : finiteMax (List.finRange n) g (centers i) ≤ δ :=
    finiteMax_le _ _ _ hδ htermδ (centers i)
  have hiMem : i ∈ List.finRange n := List.mem_finRange i
  have hown : g i (centers i) = if bits i then δ else 0 := by
    dsimp [g]
    split_ifs with hb
    · simp [dist_self, hδ]
    · rfl
  have hmax_ge : g i (centers i) ≤ finiteMax (List.finRange n) g (centers i) :=
    finiteMax_ge_mem _ _ i hiMem (centers i)
  unfold bitBump
  change finiteMax (List.finRange n) g (centers i) = if bits i then δ else 0
  by_cases hb : bits i
  · simpa [hown, hb] using le_antisymm hmax_le (by simpa [hown, hb] using hmax_ge)
  · have htermz : ∀ j ∈ List.finRange n, g j (centers i) ≤ 0 := by
      intro j hj
      by_cases hji : j = i
      · subst j
        simp [g, hb]
      · have hd : δ ≤ dist (centers i) (centers j) := hsep i j (Ne.symm hji)
        dsimp [g]
        split_ifs with hbj
        · exact max_le (by linarith) (by norm_num)
        · norm_num
    have hzero : finiteMax (List.finRange n) g (centers i) = 0 := by
      apply le_antisymm
      · exact finiteMax_le_at _ _ _ (centers i) (le_rfl : (0:ℝ) ≤ 0) htermz
      · exact hmax_nonneg
    simpa [hb, hzero]

/-- The bump superposition viewed as a bounded continuous function on a
compact metric space. -/
noncomputable def bitBumpBCF [CompactSpace K] (δ : ℝ) (centers : Fin n → K)
    (bits : Fin n → Bool) : BoundedContinuousFunction K ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨bitBump δ centers bits, (bitBump_lipschitz δ centers bits).continuous⟩

@[simp] lemma bitBumpBCF_apply [CompactSpace K] (δ : ℝ) (centers : Fin n → K)
    (bits : Fin n → Bool) (x : K) : bitBumpBCF δ centers bits x = bitBump δ centers bits x := rfl

/-- The bounded 1-Lipschitz function class with values in `[-1,1]`. -/
def boundedLipschitzClass (K : Type*) [PseudoMetricSpace K] :=
  {f : BoundedContinuousFunction K ℝ | (∀ x, -1 ≤ f x ∧ f x ≤ 1) ∧ LipschitzWith 1 (fun x => f x)}

lemma bitBumpBCF_mem_class [CompactSpace K] (δ : ℝ) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (centers : Fin n → K) (bits : Fin n → Bool) :
    bitBumpBCF δ centers bits ∈ boundedLipschitzClass K := by
  constructor
  · intro x
    rw [bitBumpBCF_apply]
    let g : Fin n → K → ℝ := fun i y =>
      if bits i then max (δ - dist y (centers i)) 0 else 0
    have hnonneg : 0 ≤ finiteMax (List.finRange n) g x :=
      finiteMax_nonneg _ _ (by
        intro i hi y
        dsimp [g]
        split_ifs <;> positivity) x
    have hle : finiteMax (List.finRange n) g x ≤ δ := by
      apply finiteMax_le _ _ _ hδ
      intro i hi y
      dsimp [g]
      by_cases hb : bits i = true
      · rw [if_pos hb]
        have hd : 0 ≤ dist y (centers i) := dist_nonneg
        exact max_le (by nlinarith [hd]) hδ
      · rw [if_neg hb]
        exact hδ
    have hnonneg' : 0 ≤ bitBump δ centers bits x := by simpa [bitBump, g] using hnonneg
    have hle' : bitBump δ centers bits x ≤ δ := by simpa [bitBump, g] using hle
    constructor <;> linarith
  · change LipschitzWith 1 (bitBump δ centers bits)
    exact bitBump_lipschitz δ centers bits

lemma bitBumpBCF_injective [CompactSpace K] (δ : ℝ) (hδ : 0 < δ)
    (centers : Fin n → K)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (centers i) (centers j)) :
    Function.Injective (bitBumpBCF δ centers) := by
  intro bits bits' heq
  funext i
  by_contra hbits
  have hvals : bitBump δ centers bits (centers i) = bitBump δ centers bits' (centers i) :=
    congrFun (congrArg (fun f : BoundedContinuousFunction K ℝ => (f : K → ℝ)) heq) (centers i)
  rw [bitBump_center δ hδ.le centers hsep bits i,
    bitBump_center δ hδ.le centers hsep bits' i] at hvals
  by_cases hb : bits i
  · have hb' : bits' i = false := by
      cases h : bits' i <;> simp_all
    simp [hb, hb'] at hvals
    linarith
  · have hb' : bits' i = true := by
      cases h : bits' i <;> simp_all
    simp [hb, hb'] at hvals
    linarith

lemma bitBumpBCF_image_isSeparated [CompactSpace K] (δ r : ℝ) (hδ : 0 < δ)
    (hr : 0 ≤ r) (hrδ : r < δ)
    (centers : Fin n → K)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (centers i) (centers j)) :
    Metric.IsSeparated (ENNReal.ofReal r)
      (Set.range (bitBumpBCF δ centers) : Set (BoundedContinuousFunction K ℝ)) := by
  intro f hf g hg hfg
  rcases hf with ⟨bits, rfl⟩
  rcases hg with ⟨bits', rfl⟩
  have hbits : bits ≠ bits' := by
    intro heq
    exact hfg (congrArg (bitBumpBCF δ centers) heq)
  -- find a coordinate where the two labels differ
  have hdiff : ∃ i, bits i ≠ bits' i := by
    by_contra h
    apply hbits
    funext i
    exact not_ne_iff.mp (fun hi => h ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hdiff
  have hv := bitBump_center δ hδ.le centers hsep bits i
  have hv' := bitBump_center δ hδ.le centers hsep bits' i
  have heval : dist (bitBumpBCF δ centers bits) (bitBumpBCF δ centers bits') ≥ δ := by
    have hpoint := BoundedContinuousFunction.dist_coe_le_dist
      (f := bitBumpBCF δ centers bits) (g := bitBumpBCF δ centers bits') (x := centers i)
    rw [bitBumpBCF_apply, bitBumpBCF_apply, hv, hv'] at hpoint
    cases hi' : bits i <;> cases hj' : bits' i <;> simp_all [abs_of_pos hδ]
  rw [edist_dist]
  have hpositive : 0 < dist (bitBumpBCF δ centers bits) (bitBumpBCF δ centers bits') :=
    lt_of_lt_of_le hδ heval
  rw [ENNReal.ofReal_lt_ofReal_iff hpositive]
  exact lt_of_lt_of_le hrδ heval

/-- An `n`-point `δ`-packing in the domain yields at least `2^n` external
covering centers for the bounded 1-Lipschitz function class, at every radius
`ε` with `2ε < δ`. Covering centers are unrestricted ambient BCF elements. -/
theorem externalCoveringNumber_ge_two_pow_of_domain_packing
    [CompactSpace K] (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (centers : Fin n → K)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (centers i) (centers j))
    (ε : ℝ≥0) (hε : 2 * (ε : ℝ) < δ) :
    ((2 ^ n : ℕ) : ℕ∞) ≤
      Metric.externalCoveringNumber ε (boundedLipschitzClass K) := by
  classical
  let S : Finset (BoundedContinuousFunction K ℝ) :=
    Finset.univ.image (bitBumpBCF δ centers)
  have hinj : Function.Injective (bitBumpBCF δ centers) :=
    bitBumpBCF_injective δ hδ centers hsep
  have hcard : S.card = 2 ^ n := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj]
    simp [Fintype.card_fun]
  have hSK : (↑S : Set (BoundedContinuousFunction K ℝ)) ⊆ boundedLipschitzClass K := by
    intro f hf
    rcases Finset.mem_image.mp hf with ⟨bits, hbits, rfl⟩
    exact bitBumpBCF_mem_class δ hδ.le hδ1 centers bits
  have hsepRange := bitBumpBCF_image_isSeparated δ (2 * (ε : ℝ)) hδ
    (by positivity) hε centers hsep
  have hsepS : Metric.IsSeparated ((2 * ε : ℝ≥0) : ℝ≥0∞)
      (↑S : Set (BoundedContinuousFunction K ℝ)) := by
    have hsep' : Metric.IsSeparated (ENNReal.ofReal (2 * (ε : ℝ)))
        (↑S : Set (BoundedContinuousFunction K ℝ)) := hsepRange.mono (by
          intro f hf
          rcases Finset.mem_image.mp hf with ⟨bits, hb, rfl⟩
          exact ⟨bits, rfl⟩)
    simpa using hsep'
  have hpack : (↑S : Set (BoundedContinuousFunction K ℝ)).encard ≤
      Metric.packingNumber (2 * ε) (boundedLipschitzClass K) :=
    hsepS.encard_le_packingNumber hSK
  have hcmp := Metric.packingNumber_two_mul_le_externalCoveringNumber ε
    (boundedLipschitzClass K)
  have hSencard : (↑S : Set (BoundedContinuousFunction K ℝ)).encard =
      ((2 ^ n : ℕ) : ℕ∞) := by simp [hcard]
  rw [← hSencard]
  exact hpack.trans hcmp

/-- The packing lift is a worst-case bit lower bound for arbitrary ambient
decoder outputs, not only decoders constrained to the Lipschitz class. -/
theorem operatorLearning_bitCount_lower_of_domain_packing
    [CompactSpace K] (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (centers : Fin n → K)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (centers i) (centers j))
    (ε : ℝ≥0) (hε : 2 * (ε : ℝ) < δ) (B : ℕ)
    (hcode : BrownianSharp.AlignmentAuditCoding.UniformCode
      (boundedLipschitzClass K) ε (Fin (2 ^ B))) : n ≤ B := by
  apply BrownianSharp.AlignmentAuditCoding.bitCount_ge_of_externalCover_lower
    (boundedLipschitzClass K) ε n B ?_ hcode
  exact externalCoveringNumber_ge_two_pow_of_domain_packing
    δ hδ hδ1 centers hsep ε hε

/-- A strict external-covering lower bound forces a finite separated packing
of every smaller prescribed cardinality. This is the internal/external
covering-number comparison followed by the packing supremum definition. -/
theorem exists_finite_packing_of_externalCoveringNumber_gt
    {X : Type*} [PseudoEMetricSpace X] (K : Set X) (δ : ℝ≥0) (M : ℕ)
    (hcover : (M : ℕ∞) < Metric.externalCoveringNumber δ K) :
    ∃ S : Finset X, (↑S : Set X) ⊆ K ∧
      Metric.IsSeparated (δ : ℝ≥0∞) (↑S : Set X) ∧ M < S.card := by
  have hpack : (M : ℕ∞) < Metric.packingNumber δ K :=
    lt_of_lt_of_le hcover
      ((Metric.externalCoveringNumber_le_coveringNumber δ K).trans
        (Metric.coveringNumber_le_packingNumber δ K))
  by_contra h
  push_neg at h
  have hbound : ∀ S : Finset X, (↑S : Set X) ⊆ K →
      Metric.IsSeparated (δ : ℝ≥0∞) (↑S : Set X) → S.card ≤ M := by
    intro S hSK hsep
    exact h S hSK hsep
  have hpackle := HaarQuarter.TheoremD.packingNumber_le_of_finset_bound K δ M hbound
  exact (not_le_of_gt hpack) hpackle

/-- A domain entropy lower bound implies a matching deterministic bit lower
bound for the bounded Lipschitz operator class. The one-radius loss is explicit:
domain separation at `δ` gives output-code separation usable at every
`ε < δ/2`. -/
theorem operatorLearning_bitCount_lower_of_domain_externalEntropy
    [CompactSpace K] (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1)
    (M B : ℕ) (hK : (M : ℕ∞) < Metric.externalCoveringNumber δ (Set.univ : Set K))
    (ε : ℝ≥0) (hε : 2 * (ε : ℝ) < (δ : ℝ))
    (hcode : BrownianSharp.AlignmentAuditCoding.UniformCode
      (boundedLipschitzClass K) ε (Fin (2 ^ B))) : M < B := by
  obtain ⟨S, hSK, hSsep, hScard⟩ :=
    exists_finite_packing_of_externalCoveringNumber_gt
      (Set.univ : Set K) δ M hK
  let e : {x : K // x ∈ (↑S : Set K)} ≃ Fin S.card :=
    (Finset.equivToSet S).symm.trans S.equivFin
  let centers : Fin S.card → K := fun i => (e.symm i).val
  have hcenters : ∀ i j, i ≠ j → (δ : ℝ) ≤ dist (centers i) (centers j) := by
    intro i j hij
    have hval : centers i ≠ centers j := by
      intro heq
      apply hij
      simpa [centers] using congrArg e (Subtype.ext heq)
    have hs := hSsep (e.symm i).property (e.symm j).property hval
    have hs' : ENNReal.ofReal (δ : ℝ) <
        ENNReal.ofReal (dist (centers i) (centers j)) := by
      simpa [centers, edist_dist, ENNReal.ofReal_coe_nnreal] using hs
    have hreal := (ENNReal.ofReal_lt_ofReal_iff'.mp hs').1
    exact hreal.le
  have hcoverFun := externalCoveringNumber_ge_two_pow_of_domain_packing
    (δ : ℝ) hδ hδ1 centers hcenters ε hε
  have hcount : S.card ≤ B :=
    BrownianSharp.AlignmentAuditCoding.bitCount_ge_of_externalCover_lower
      (boundedLipschitzClass K) ε S.card B hcoverFun hcode
  exact lt_of_lt_of_le hScard hcount

/-- Ambient external entropy of a compact subset gives the same deterministic
bit lower bound for Lipschitz functions whose domain is the subtype of that
subset. This is the form needed for the Cameron--Martin set `K_d⊂C`. -/
theorem operatorLearning_bitCount_lower_of_compactSubset_externalEntropy
    {X : Type*} [MetricSpace X] (A : Set X) (hA : IsCompact A)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1)
    (M B : ℕ) (hK : (M : ℕ∞) < Metric.externalCoveringNumber δ A)
    (ε : ℝ≥0) (hε : 2 * (ε : ℝ) < (δ : ℝ))
    (hcode : BrownianSharp.AlignmentAuditCoding.UniformCode
      (boundedLipschitzClass A) ε (Fin (2 ^ B))) : M < B := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  obtain ⟨S, hSA, hSsep, hScard⟩ :=
    exists_finite_packing_of_externalCoveringNumber_gt A δ M hK
  let e : {x : X // x ∈ (↑S : Set X)} ≃ Fin S.card :=
    (Finset.equivToSet S).symm.trans S.equivFin
  let centers : Fin S.card → A := fun i => ⟨(e.symm i).val, hSA (e.symm i).property⟩
  have hcenters : ∀ i j, i ≠ j → (δ : ℝ) ≤ dist (centers i) (centers j) := by
    intro i j hij
    have hval : (centers i).val ≠ (centers j).val := by
      intro heq
      apply hij
      simpa [centers] using congrArg e (Subtype.ext heq)
    have hs := hSsep (e.symm i).property (e.symm j).property hval
    have hs' : ENNReal.ofReal (δ : ℝ) <
        ENNReal.ofReal (dist (centers i).val (centers j).val) := by
      simpa [edist_dist, ENNReal.ofReal_coe_nnreal] using hs
    have hreal := (ENNReal.ofReal_lt_ofReal_iff'.mp hs').1
    simpa only [Subtype.dist_eq] using hreal.le
  have hcoverFun := externalCoveringNumber_ge_two_pow_of_domain_packing
    (δ : ℝ) hδ hδ1 centers hcenters ε hε
  have hcount : S.card ≤ B :=
    BrownianSharp.AlignmentAuditCoding.bitCount_ge_of_externalCover_lower
      (boundedLipschitzClass A) ε S.card B hcoverFun hcode
  exact lt_of_lt_of_le hScard hcount

/-- Finite dyadic information lower bound for the bounded 1-Lipschitz class
on the Brownian-sheet Cameron--Martin ball. The entropy constant is supplied
by the certified Cameron--Martin lower theorem; the radius is chosen below
half that certified entropy radius. -/
theorem cameronMartin_operatorLearning_bitCount_lower
    {d B k : ℕ} (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c * BrownianSharp.cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d))
    (hk : 2 ≤ k) (ε : ℝ≥0)
    (hε : 2 * (ε : ℝ) < min 1 (c * BrownianSharp.cmIndexRate d k / 2))
    (hcode : BrownianSharp.AlignmentAuditCoding.UniformCode
      (boundedLipschitzClass {f : C(BrownianCubeAnchor d, ℝ) //
        f ∈ CameronMartin.KdUnitCube d}) ε (Fin (2 ^ B))) :
    2 ^ (k - 1) < B := by
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by
    have : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    exact this)
  have hrate : 0 < BrownianSharp.cmIndexRate d k := by
    have hpow : 0 < (Real.log (k : ℝ)) ^ ((d : ℝ) - 1 / 2) :=
      Real.rpow_pos_of_pos hlog _
    have hkinv : 0 < (k : ℝ) ^ (-1 : ℝ) := by positivity
    simpa [BrownianSharp.cmIndexRate, BrownianSharp.logarithmicIndexRate] using
      mul_pos hkinv hpow
  let r : ℝ := c * BrownianSharp.cmIndexRate d k
  have hr : 0 < r := by dsimp [r]; exact mul_pos hc hrate
  let ρ : ℝ≥0 := ⟨min 1 (r / 2), le_of_lt (lt_min (by positivity) (by positivity))⟩
  have hρ1 : (ρ : ℝ) ≤ 1 := by dsimp [ρ]; exact min_le_left _ _
  have hρr : (ρ : ℝ) < r := by
    dsimp [ρ]
    exact (min_le_right 1 (r / 2)).trans_lt (by linarith)
  have hρEntropy : (ρ : ℝ≥0∞) <
      HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) := by
    calc
      (ρ : ℝ≥0∞) = ENNReal.ofReal (ρ : ℝ) := by simp
      _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).2 hρr
      _ ≤ HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) :=
        hlower k hk
  have hK : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber ρ (CameronMartin.KdUnitCube d) :=
    BrownianSharp.externalCover_gt_of_radius_lt_entropyNumber k
      (CameronMartin.KdUnitCube d) ρ hρEntropy
  have hA : IsCompact (CameronMartin.KdUnitCube d) := by
    rw [CameronMartin.KdUnitCube_eq_Kd d]
    exact CameronMartin.Kd_isCompact d
  have hρpos : 0 < (ρ : ℝ) := by
    dsimp [ρ]
    exact lt_min (by norm_num) (by linarith)
  exact operatorLearning_bitCount_lower_of_compactSubset_externalEntropy
    (CameronMartin.KdUnitCube d) hA ρ hρpos hρ1
    (2 ^ (k - 1)) B hK ε hε hcode

/-- The preceding finite information bound with its entropy constant supplied
by the certified Cameron--Martin lower theorem. -/
theorem cameronMartin_operatorLearning_bitCount_lower_certified
    {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) (ε : ℝ≥0) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ,
      2 * (ε : ℝ) < min 1 (c * BrownianSharp.cmIndexRate d k / 2) →
      BrownianSharp.AlignmentAuditCoding.UniformCode
        (boundedLipschitzClass {f : C(BrownianCubeAnchor d, ℝ) //
          f ∈ CameronMartin.KdUnitCube d}) ε (Fin (2 ^ B)) →
      2 ^ (k - 1) < B := by
  obtain ⟨c, hc, hlower⟩ := BrownianSharp.cameronMartinEntropyLower_certified hd
  refine ⟨c, hc, ?_⟩
  intro B hε hcode
  exact cameronMartin_operatorLearning_bitCount_lower hd c hc hlower hk ε hε hcode

end BrownianSharp.AlignmentAuditLifting
