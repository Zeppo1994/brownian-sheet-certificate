import BrownianSharp.KolmogorovWidth
import BrownianSharp.TheoremDEntropyPacking
import BrownianSharp.TheoremFFiniteDimensionalCovering
import BrownianSharp.TheoremFPackingWidth
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Finite-dimensional covers for width approximations

This is the first geometric step in a multiscale proof of Carl's entropy-width
inequality.  An approximation by a finite-dimensional subspace puts the
approximants in a bounded ball of that subspace; a volumetric net of that ball
then gives an ambient-center cover of the original set.
-/

open Set
open scoped ENNReal NNReal

namespace BrownianSharp.Carl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A strict bound on the Kolmogorov width supplies one admissible subspace
with pointwise norm approximants at the same error threshold.  This is the
near-minimizer extraction from the defining two infima/supremum; compactness
is not needed because a small slack is already present in the strict bound. -/
theorem exists_width_subspace_pointwise_approximation
    (K : Set X) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hwidth : HaarQuarter.TheoremD.Width.kolmogorovWidth K m <
      ENNReal.ofReal ε) :
    ∃ V : Submodule ℝ X, Module.rank ℝ V ≤ (m : Cardinal) ∧
      ∀ x ∈ K, ∃ v : V, ‖x - (v : X)‖ < ε := by
  classical
  have hnear := (iInf_lt_iff.mp hwidth)
  obtain ⟨V, hV⟩ := hnear
  refine ⟨V.1, V.2, ?_⟩
  exact HaarQuarter.TheoremF.Carl.exists_pointwise_norm_approximation
    K V.1 hε hV

/-- Choose all pointwise approximants to a strict width minimizer at once. -/
theorem exists_width_approximant_function
    (K : Set X) (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hwidth : HaarQuarter.TheoremD.Width.kolmogorovWidth K m <
      ENNReal.ofReal ε) :
    ∃ V : Submodule ℝ X, Module.rank ℝ V ≤ (m : Cardinal) ∧
      FiniteDimensional ℝ V ∧
      ∃ f : {x : X // x ∈ K} → V,
        ∀ x : {x : X // x ∈ K}, ‖(x : X) - (f x : X)‖ ≤ ε := by
  classical
  obtain ⟨V, hV, hpoint⟩ :=
    exists_width_subspace_pointwise_approximation K m hε hwidth
  let f : {x : X // x ∈ K} → V := fun x => Classical.choose (hpoint x.1 x.2)
  have hf (x : {x : X // x ∈ K}) :
      ‖(x : X) - (f x : X)‖ < ε := Classical.choose_spec (hpoint x.1 x.2)
  exact ⟨V, hV, finiteDimensional_of_rank_le V hV, f, fun x => (hf x).le⟩

/-- Simultaneously select the finite family of width-minimizing subspaces and
pointwise approximants used by a dyadic Carl chain. -/
theorem exists_finite_width_approximation_family
    (K : Set X) (L : ℕ) (ε : Fin (L + 1) → ℝ)
    (hε : ∀ j, 0 < ε j)
    (hwidth : ∀ j : Fin (L + 1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2 ^ j.val - 1) <
        ENNReal.ofReal (ε j)) :
    ∃ V : Fin (L + 1) → Submodule ℝ X,
      (∀ j, Module.rank ℝ (V j) ≤ ((2 ^ j.val - 1 : ℕ) : Cardinal)) ∧
      (∀ j, FiniteDimensional ℝ (V j)) ∧
      ∃ f : ∀ j, {x : X // x ∈ K} → X,
        ∀ j x, f j x ∈ V j ∧ ‖(x : X) - f j x‖ ≤ ε j := by
  classical
  have hexists : ∀ j : Fin (L + 1),
      ∃ V : Submodule ℝ X,
        Module.rank ℝ V ≤ ((2 ^ j.val - 1 : ℕ) : Cardinal) ∧
        FiniteDimensional ℝ V ∧
        ∃ f : {x : X // x ∈ K} → V,
          ∀ x : {x : X // x ∈ K}, ‖(x : X) - (f x : X)‖ ≤ ε j := by
    intro j
    simpa using exists_width_approximant_function K (2 ^ j.val - 1)
      (hε j) (hwidth j)
  choose V hV hfd f hf using hexists
  refine ⟨V, hV, hfd, ?_⟩
  refine ⟨fun j x => (f j x : X), ?_⟩
  intro j x
  exact ⟨(f j x).property, hf j x⟩

/-- The sum of two consecutive width approximant spaces has the dyadic
finite-dimensional size needed by the volumetric Carl chain. -/
theorem finrank_consecutive_width_sup_le
    {L : ℕ} (V : Fin (L + 1) → Submodule ℝ X)
    (hV : ∀ j, Module.rank ℝ (V j) ≤ ((2 ^ j.val - 1 : ℕ) : Cardinal))
    (hfd : ∀ j, FiniteDimensional ℝ (V j)) (j : Fin L) :
    Module.finrank ℝ ((V j.succ ⊔ V j.castSucc) : Submodule ℝ X) ≤
      2 ^ (j.val + 2) := by
  let j₁ : Fin (L + 1) := j.succ
  let j₀ : Fin (L + 1) := j.castSucc
  letI : FiniteDimensional ℝ (V j₁) := hfd j₁
  letI : FiniteDimensional ℝ (V j₀) := hfd j₀
  have hsum := Submodule.finrank_add_le_finrank_add_finrank (V j₁) (V j₀)
  have hnat1 : Module.finrank ℝ (V j₁) ≤ 2 ^ (j.val + 1) - 1 := by
    have hh := hV j₁
    rw [← Module.finrank_eq_rank ℝ (V j₁)] at hh
    exact_mod_cast hh
  have hnat0 : Module.finrank ℝ (V j₀) ≤ 2 ^ j.val - 1 := by
    have hh := hV j₀
    rw [← Module.finrank_eq_rank ℝ (V j₀)] at hh
    exact_mod_cast hh
  have h1 : Module.finrank ℝ (V j₁) ≤ 2 ^ (j.val + 1) :=
    le_trans hnat1 (Nat.sub_le _ _)
  have h0 : Module.finrank ℝ (V j₀) ≤ 2 ^ j.val :=
    le_trans hnat0 (Nat.sub_le _ _)
  calc
    Module.finrank ℝ ((V j₁ ⊔ V j₀) : Submodule ℝ X) ≤
        Module.finrank ℝ (V j₁) + Module.finrank ℝ (V j₀) := hsum
    _ ≤ 2 ^ (j.val + 1) + 2 ^ j.val := add_le_add h1 h0
    _ ≤ 2 ^ (j.val + 2) := by
      calc
        2 ^ (j.val + 1) + 2 ^ j.val = 3 * 2 ^ j.val := by
          rw [pow_succ]
          ring
        _ ≤ 4 * 2 ^ j.val := by nlinarith [Nat.zero_le (2 ^ j.val)]
        _ = 2 ^ (j.val + 2) := by rw [pow_succ, pow_succ]; ring

/-- Pointwise relations between two functions on a finite index type lift to
`List.ofFn` without changing the order of the indices. -/
theorem forall₂_ofFn {α β : Type*} {n : ℕ} (R : α → β → Prop)
    (a : Fin n → α) (b : Fin n → β)
    (h : ∀ i, R (a i) (b i)) :
    List.Forall₂ R (List.ofFn a) (List.ofFn b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (h 0)
        (ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ))

/-- Minkowski sum of two sets. -/
def sumSet (A B : Set X) : Set X :=
  (fun p : X × X => p.1 + p.2) '' (A ×ˢ B)

/-- Adding two finite sets of centers adds their covering radii. -/
theorem isCover_sumSet {A B C D : Set X} {ε δ : ℝ≥0}
    (hA : Metric.IsCover ε A C) (hB : Metric.IsCover δ B D) :
    Metric.IsCover (ε + δ) (sumSet A B) (sumSet C D) := by
  change ∀ ⦃x⦄, x ∈ sumSet A B →
    ∃ y ∈ sumSet C D, edist x y ≤ ((ε + δ : ℝ≥0) : ENNReal)
  rintro x ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  obtain ⟨c, hc, hac⟩ := hA ha
  obtain ⟨d, hd, hbd⟩ := hB hb
  refine ⟨c + d, ⟨⟨c, d⟩, ⟨hc, hd⟩, rfl⟩, ?_⟩
  calc
    edist (a + b) (c + d) ≤ edist a c + edist b d := edist_add_add_le _ _ _ _
    _ ≤ (ε : ENNReal) + (δ : ENNReal) := add_le_add hac hbd
    _ = ((ε + δ : ℝ≥0) : ENNReal) := by simp

/-- The sum of finite center sets is finite and its cardinality is bounded by
the product of their cardinalities. -/
theorem finite_sumSet_card_le {C D : Set X}
    (hC : C.Finite) (hD : D.Finite) :
    (sumSet C D).Finite ∧ (sumSet C D).encard ≤ C.encard * D.encard := by
  let addMap : X × X → X := fun p => p.1 + p.2
  have hprod : (C ×ˢ D).Finite := hC.prod hD
  refine ⟨hprod.image addMap, ?_⟩
  calc
    (sumSet C D).encard = (addMap '' (C ×ˢ D)).encard := rfl
    _ ≤ (C ×ˢ D).encard := Set.encard_image_le _ _
    _ = C.encard * D.encard := Set.encard_prod

/-- One scale in a multiscale cover: a finite cover of an increment set. -/
structure CoverPiece (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  source : Set X
  centers : Set X
  radius : ℝ≥0
  cover : Metric.IsCover radius source centers
  centers_finite : centers.Finite

/-- A volumetric net of a finite-dimensional subspace ball, packaged as one
increment in a multiscale cover. -/
theorem exists_submodule_ball_piece (V : Submodule ℝ X)
    [FiniteDimensional ℝ V] [Nontrivial V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ p : CoverPiece X,
      p.source = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage V R ∧
      p.radius = NNReal.mk ε hε.le ∧
      p.centers.encard ≤
        ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ V)) := by
  obtain ⟨C, hsub, hfinite, hcover, hcard⟩ :=
    HaarQuarter.TheoremF.FiniteDimensionalCovering.exists_submodule_ball_cover
      V R ε hR hε
  exact ⟨⟨_, C, _, hcover, hfinite⟩, rfl, rfl, hcard⟩

/-- The finite-dimensional ball-net constructor also covers the zero
subspace; in that case its image ball is the singleton `{0}`. -/
theorem exists_submodule_ball_piece_general (V : Submodule ℝ X)
    [FiniteDimensional ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ p : CoverPiece X,
      p.source = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage V R ∧
      p.radius = NNReal.mk ε hε.le ∧
      p.centers.encard ≤
        ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ V)) := by
  classical
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    exact exists_submodule_ball_piece V hR hε
  · letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    have hdim : Module.finrank ℝ V = 0 :=
      Module.finrank_zero_iff.mpr inferInstance
    let S : Set X :=
      HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage V R
    have hS : S = {0} := by
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        have : v = 0 := Subsingleton.elim v 0
        simp [this]
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        subst x
        refine ⟨0, ?_, rfl⟩
        change dist (0 : V) 0 ≤ R
        simpa using hR
    let p : CoverPiece X :=
      ⟨S, {0}, NNReal.mk ε hε.le, by
        intro x hx
        have hx0 : x = 0 := by rw [hS] at hx; simpa using hx
        subst x
        refine ⟨0, by simp, ?_⟩
        simp, by simp⟩
    refine ⟨p, ?_, rfl, ?_⟩
    · change S = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage V R
      rfl
    · rw [hdim]
      simp [p]

/-- A radius-R ball is covered by the single center zero at radius R. -/
noncomputable def zeroBallPiece (R : ℝ≥0) : CoverPiece X :=
  ⟨Metric.closedBall (0 : X) R, {0}, R, by
    change ∀ ⦃x⦄, x ∈ Metric.closedBall (0 : X) R →
      ∃ y ∈ ({0} : Set X), edist x y ≤ (R : ENNReal)
    intro x hx
    refine ⟨0, by simp, ?_⟩
    have hnorm : ‖x‖ ≤ (R : ℝ) := by
      simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hx)
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
    apply (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ (R : ℝ) from R.2)).2
    simpa [dist_eq_norm] using hnorm, by simp⟩

/-- Iterated Minkowski sum of a list of sets. -/
def sumSetList : List (Set X) → Set X
  | [] => {0}
  | A :: As => sumSet A (sumSetList As)

/-- The Minkowski sum of the source sets in a finite cover chain. -/
def sumSources : List (CoverPiece X) → Set X
  | [] => {0}
  | p :: ps => sumSet p.source (sumSources ps)

/-- The Minkowski sum of the center sets in a finite cover chain. -/
def sumCenters : List (CoverPiece X) → Set X
  | [] => {0}
  | p :: ps => sumSet p.centers (sumCenters ps)

/-- Sum of the radii in a finite cover chain. -/
def sumRadii : List (CoverPiece X) → ℝ≥0
  | [] => 0
  | p :: ps => p.radius + sumRadii ps

theorem sumRadii_eq_list_sum (pieces : List (CoverPiece X)) :
    sumRadii pieces = (pieces.map CoverPiece.radius).sum := by
  induction pieces with
  | nil => rfl
  | cons p ps ih => simp [sumRadii, ih]

theorem sumSources_eq_sumSetList (pieces : List (CoverPiece X)) :
    sumSources pieces = sumSetList (pieces.map CoverPiece.source) := by
  induction pieces with
  | nil => rfl
  | cons p ps ih => simp [sumSources, sumSetList, ih]

/-- Successive differences from a previous approximation, followed by the
final residual. -/
def tailIncrements (x previous : X) : List X → List X
  | [] => [x - previous]
  | next :: rest => (next - previous) :: tailIncrements x next rest

/-- The initial approximation followed by its successive differences and the
last residual. This is the canonical list decomposition used by the
multiscale cover. -/
def chainIncrements (x : X) : List X → List X
  | [] => [x]
  | first :: rest => first :: tailIncrements x first rest

/-- The successive differences and residual telescope to the original point. -/
theorem previous_add_tailIncrements_sum (x previous : X) (ys : List X) :
    previous + (tailIncrements x previous ys).sum = x := by
  induction ys generalizing previous with
  | nil =>
      simp [tailIncrements]
  | cons next rest ih =>
      simp only [tailIncrements, List.sum_cons]
      calc
        previous + ((next - previous) + (tailIncrements x next rest).sum) =
            next + (tailIncrements x next rest).sum := by abel
        _ = x := ih next

/-- The canonical approximation chain exactly sums back to its target. -/
theorem chainIncrements_sum (x : X) (ys : List X) :
    (chainIncrements x ys).sum = x := by
  cases ys with
  | nil => simp [chainIncrements]
  | cons first rest =>
      simp only [chainIncrements, List.sum_cons]
      exact previous_add_tailIncrements_sum x first rest

/-- The tail differences of a finite `Fin`-indexed approximant sequence
line up with the corresponding scale sources and terminal residual. -/
theorem forall₂_tailIncrements_ofFn {n : ℕ} {x : X}
    (f : Fin (n + 1) → X) (A : Fin n → Set X) (tail : Set X)
    (hstep : ∀ i, f i.succ - f i.castSucc ∈ A i)
    (hend : x - f (Fin.last n) ∈ tail) :
    List.Forall₂ (fun z S => z ∈ S)
      (tailIncrements x (f 0) (List.ofFn (fun i : Fin n => f i.succ)))
      (List.ofFn A ++ [tail]) := by
  induction n with
  | zero =>
      simpa [tailIncrements, List.ofFn_zero, Fin.last_zero] using
        (List.Forall₂.cons hend List.Forall₂.nil)
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      have htail : List.Forall₂ (fun z S => z ∈ S)
          (tailIncrements x (f (Fin.succ 0)) (List.ofFn fun i : Fin n => f i.succ.succ))
          (List.ofFn (fun i : Fin n => A i.succ) ++ [tail]) := by
        refine ih (fun i => f i.succ) (fun i => A i.succ) ?_ ?_
        · intro i
          simpa using hstep i.succ
        · simpa [Fin.succ_last] using hend
      simpa only [tailIncrements, List.cons_append] using
        (List.Forall₂.cons (R := fun z S => z ∈ S) (by simpa using hstep 0) htail)


/-- Selected finite-dimensional approximants give the actual telescoping
increment chain used by Carl's covering argument. The initial zero space,
each consecutive sum-space increment, and the final residual are all
verified pointwise; no abstract chain condition is assumed. -/
theorem selected_width_approximation_chain
    (K : Set X) (L : ℕ)
    (V : Fin (L + 1) → Submodule ℝ X)
    (f : ∀ j, {x : X // x ∈ K} → X)
    (δ : Fin (L + 1) → ℝ)
    (hzero : ∀ x : {x : X // x ∈ K}, f 0 x = 0)
    (hmem : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}), f j x ∈ V j)
    (happrox : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}),
      ‖(x : X) - f j x‖ ≤ δ j) :
    ∀ x : {x : X // x ∈ K},
      List.Forall₂ (fun z S => z ∈ S)
        (chainIncrements (x : X) (List.ofFn fun j : Fin (L + 1) => f j x))
        ({0} :: (List.ofFn (fun j : Fin L =>
          HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
            (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc)) ++
          [Metric.closedBall (0 : X) (δ (Fin.last L))])) := by
  intro x
  have hstep : ∀ j : Fin L,
      f j.succ x - f j.castSucc x ∈
        HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc) := by
    intro j
    have hmem' : f j.succ x - f j.castSucc x ∈ V j.succ ⊔ V j.castSucc :=
      Submodule.sub_mem_sup (hmem j.succ x) (hmem j.castSucc x)
    have hnorm : ‖f j.succ x - f j.castSucc x‖ ≤ δ j.succ + δ j.castSucc := by
      calc
        ‖f j.succ x - f j.castSucc x‖ =
            ‖(f j.succ x - (x : X)) + ((x : X) - f j.castSucc x)‖ := by
              congr 1
              abel
        _ ≤ ‖f j.succ x - (x : X)‖ + ‖(x : X) - f j.castSucc x‖ := norm_add_le _ _
        _ = ‖(x : X) - f j.succ x‖ + ‖(x : X) - f j.castSucc x‖ := by
          rw [norm_sub_rev]
        _ ≤ δ j.succ + δ j.castSucc := add_le_add (happrox j.succ x) (happrox j.castSucc x)
    refine ⟨⟨f j.succ x - f j.castSucc x, hmem'⟩, ?_, rfl⟩
    change dist (f j.succ x - f j.castSucc x) 0 ≤ δ j.succ + δ j.castSucc
    simpa [dist_eq_norm] using hnorm
  have htail : (x : X) - f (Fin.last L) x ∈
      Metric.closedBall (0 : X) (δ (Fin.last L)) := by
    apply Metric.mem_closedBall.mpr
    simpa [dist_eq_norm] using happrox (Fin.last L) x
  rw [List.ofFn_succ]
  simp only [chainIncrements]
  exact List.Forall₂.cons (by simp [hzero x])
    (forall₂_tailIncrements_ofFn
      (fun j => f j x) (fun j =>
        HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc))
      (Metric.closedBall (0 : X) (δ (Fin.last L))) hstep htail)

/-- Strict dyadic width bounds select finite-dimensional spaces and actual
pointwise approximants which satisfy `selected_width_approximation_chain`.
The initial rank-zero space is proved to be the zero space. -/
theorem exists_selected_width_chain
    (K : Set X) (L : ℕ) (δ : Fin (L + 1) → ℝ)
    (hδ : ∀ j, 0 < δ j)
    (hwidth : ∀ j : Fin (L + 1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2 ^ j.val - 1) <
        ENNReal.ofReal (δ j)) :
    ∃ V : Fin (L + 1) → Submodule ℝ X,
      (∀ j, Module.rank ℝ (V j) ≤ ((2 ^ j.val - 1 : ℕ) : Cardinal)) ∧
      (∀ j, FiniteDimensional ℝ (V j)) ∧
      ∃ f : ∀ j, {x : X // x ∈ K} → X,
        (∀ x : {x : X // x ∈ K}, f 0 x = 0) ∧
        (∀ j x, f j x ∈ V j ∧ ‖(x : X) - f j x‖ ≤ δ j) ∧
        (∀ x : {x : X // x ∈ K},
          List.Forall₂ (fun z S => z ∈ S)
            (chainIncrements (x : X) (List.ofFn fun j : Fin (L + 1) => f j x))
            ({0} :: (List.ofFn (fun j : Fin L =>
              HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
                (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc)) ++
              [Metric.closedBall (0 : X) (δ (Fin.last L))]))) := by
  classical
  obtain ⟨V, hV, hfd, hdata⟩ :=
    exists_finite_width_approximation_family K L δ hδ hwidth
  rcases hdata with ⟨f, hf⟩
  have hrank0 : Module.rank ℝ (V (0 : Fin (L + 1))) = 0 := by
    apply le_antisymm
    · exact hV 0
    · exact Cardinal.zero_le _
  have hfr0 : Module.finrank ℝ (V (0 : Fin (L + 1))) = 0 := by
    have hcast := Module.finrank_eq_rank ℝ (V (0 : Fin (L + 1)))
    have hle : (Module.finrank ℝ (V (0 : Fin (L + 1))) : Cardinal) ≤ 0 := by
      rw [hcast, hrank0]
    have hle' : Module.finrank ℝ (V (0 : Fin (L + 1))) ≤ 0 := by
      exact_mod_cast hle
    omega
  have hall : ∀ v : V (0 : Fin (L + 1)), v = 0 :=
    finrank_zero_iff_forall_zero.mp hfr0
  let f' : ∀ j, {x : X // x ∈ K} → X := fun j x => f j x
  have hzero : ∀ x : {x : X // x ∈ K}, f' 0 x = 0 := by
    intro x
    have hv : (⟨f 0 x, (hf 0 x).1⟩ : V (0 : Fin (L + 1))) = 0 := hall _
    exact congrArg Subtype.val hv
  refine ⟨V, hV, hfd, f', hzero, ?_⟩
  constructor
  · intro (j : Fin (L + 1)) x
    exact ⟨(hf j x).1, (hf j x).2⟩
  · intro x
    apply selected_width_approximation_chain K L V f' δ hzero
      (fun j x => (hf j x).1) (fun j x => (hf j x).2)
      x

/-- A list of pointwise increments lying in the corresponding source sets
belongs to their Minkowski sum. -/
theorem list_sum_mem_sumSources (xs : List X) (As : List (Set X))
    (hrel : List.Forall₂ (fun x A => x ∈ A) xs As) :
    xs.sum ∈ sumSetList As := by
  induction xs generalizing As with
  | nil =>
      cases As with
      | nil => simpa [sumSetList]
      | cons A As => simp at hrel
  | cons x xs ih =>
      cases As with
      | nil => simp at hrel
      | cons A As =>
          simp only [List.forall₂_cons] at hrel
          rcases hrel with ⟨hx, hrest⟩
          have htail := ih As hrest
          change x + xs.sum ∈ sumSet A (sumSetList As)
          exact ⟨(x, xs.sum), ⟨hx, htail⟩, rfl⟩

/-- A canonical chain decomposition whose increments lie in the cover-piece
source sets is contained in their Minkowski sum. -/
theorem chain_mem_sumSources (x : X) (approximants : List X)
    (pieces : List (CoverPiece X))
    (hrel : List.Forall₂ (fun z p => z ∈ p.source)
      (chainIncrements x approximants) pieces) :
    x ∈ sumSources pieces := by
  have hrel' : List.Forall₂ (fun z A => z ∈ A)
      (chainIncrements x approximants) (pieces.map CoverPiece.source) := by
    exact (List.forall₂_map_right_iff).2 hrel
  rw [sumSources_eq_sumSetList]
  rw [← chainIncrements_sum x approximants]
  exact list_sum_mem_sumSources _ _ hrel'

/-- Finite Minkowski sums of covering sets remain covers, with additive radius. -/
theorem isCover_sumPieces (pieces : List (CoverPiece X)) :
    Metric.IsCover (sumRadii pieces) (sumSources pieces) (sumCenters pieces) := by
  induction pieces with
  | nil =>
      change ∀ ⦃x⦄, x ∈ ({0} : Set X) →
        ∃ y ∈ ({0} : Set X), edist x y ≤ (0 : ℝ≥0∞)
      intro x hx
      have hx0 : x = 0 := by simpa using hx
      subst x
      exact ⟨0, by simp, by simp⟩
  | cons p ps ih =>
      simpa [sumRadii, sumSources, sumCenters] using isCover_sumSet p.cover ih

/-- The set of centers in a multiscale cover remains finite, and its cardinal
is at most the product of the cardinalities at each scale. -/
theorem finite_sumPieces_card_le (pieces : List (CoverPiece X)) :
    (sumCenters pieces).Finite ∧
      (sumCenters pieces).encard ≤ (pieces.map (fun p => p.centers.encard)).prod := by
  induction pieces with
  | nil =>
      constructor
      · simp [sumCenters]
      · simp [sumCenters]
  | cons p ps ih =>
      obtain ⟨hfin, hcard⟩ := ih
      obtain ⟨hfin', hcard'⟩ := finite_sumSet_card_le p.centers_finite hfin
      refine ⟨hfin', ?_⟩
      rw [sumCenters, List.map_cons, List.prod_cons]
      calc
        (sumSet p.centers (sumCenters ps)).encard ≤
            p.centers.encard * (sumCenters ps).encard := hcard'
        _ ≤ p.centers.encard * (ps.map (fun p => p.centers.encard)).prod := by
          gcongr

/-- A pointwise telescoping decomposition into finitely many increment sets
inherits the product cover and additive error budget of the increment nets. -/
theorem exists_cover_of_subset_sumPieces (K : Set X)
    (pieces : List (CoverPiece X))
    (hsubset : K ⊆ sumSources pieces) :
    ∃ C : Set X, C.Finite ∧
      Metric.IsCover (sumRadii pieces) K C ∧
      C.encard ≤ (pieces.map (fun p => p.centers.encard)).prod := by
  obtain ⟨hfinite, hcard⟩ := finite_sumPieces_card_le pieces
  refine ⟨sumCenters pieces, hfinite, ?_, hcard⟩
  change ∀ ⦃x⦄, x ∈ K →
    ∃ y ∈ sumCenters pieces, edist x y ≤ (sumRadii pieces : ENNReal)
  intro x hx
  exact isCover_sumPieces pieces (hsubset hx)

/-- The increment-cover chain gives an upper bound for the dyadic entropy
number as soon as the product of the per-scale net sizes fits the dyadic
budget. -/
theorem entropyNumber_le_sumRadii_of_multiscale_budget
    (K : Set X)
    (pieces : List (CoverPiece X)) (k : ℕ)
    (hsubset : K ⊆ sumSources pieces)
    (hbudget : (pieces.map (fun p => p.centers.encard)).prod ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞)) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ sumRadii pieces := by
  obtain ⟨C, _hfinite, hcover, hcard⟩ :=
    exists_cover_of_subset_sumPieces K pieces hsubset
  apply sInf_le
  refine ⟨sumRadii pieces, rfl, ?_⟩
  calc
    Metric.externalCoveringNumber (sumRadii pieces) K ≤ C.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcover
    _ ≤ (pieces.map (fun p => p.centers.encard)).prod := hcard
    _ ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := hbudget

/-- Entropy bound from an actual finite approximation chain: each point has a
finite telescoping sequence of increments in the prescribed source sets, and
the finite covering budget controls their product cardinality. -/
theorem entropyNumber_le_of_approximation_chain
    (K : Set X) (pieces : List (CoverPiece X)) (k : ℕ)
    (hchain : ∀ x ∈ K, ∃ approximants : List X,
      List.Forall₂ (fun z p => z ∈ p.source)
        (chainIncrements x approximants) pieces)
    (hbudget : (pieces.map (fun p => p.centers.encard)).prod ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞)) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ sumRadii pieces := by
  apply entropyNumber_le_sumRadii_of_multiscale_budget K pieces k ?_ hbudget
  intro x hx
  obtain ⟨approximants, hrel⟩ := hchain x hx
  exact chain_mem_sumSources x approximants pieces hrel

/-- Multiply scale-by-scale dyadic cardinality bounds.  This keeps the
volumetric calculation separate from the telescoping argument while giving
the exact product budget required by the entropy-number definition. -/
theorem list_product_le_dyadic_of_forall₂ {α : Type*}
    (counts : α → ℕ∞) (items : List α) (exponents : List ℕ)
    (hcounts : List.Forall₂ (fun a e => counts a ≤ ((2 ^ e : ℕ) : ℕ∞))
      items exponents) :
    (items.map counts).prod ≤ ((2 ^ exponents.sum : ℕ) : ℕ∞) := by
  induction hcounts with
  | nil => simp
  | @cons a e items exponents hhead htail ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      calc
        counts a * (items.map counts).prod ≤
            ((2 ^ e : ℕ) : ℕ∞) * ((2 ^ exponents.sum : ℕ) : ℕ∞) :=
          mul_le_mul hhead ih (by positivity) (by positivity)
        _ = ((2 ^ (e + exponents.sum) : ℕ) : ℕ∞) := by
          rw [pow_add, Nat.cast_mul]

/-- A telescoping approximation chain whose increment covers have dyadic
scale budgets gives an entropy upper bound.  The exponent sum hypothesis
records the full finite product budget; it is not a concentration or Carl
inequality premise. -/
theorem entropyNumber_le_of_dyadic_approximation_chain
    (K : Set X) (pieces : List (CoverPiece X))
    (k : ℕ) (exponents : List ℕ)
    (hchain : ∀ x ∈ K, ∃ approximants : List X,
      List.Forall₂ (fun z p => z ∈ p.source)
        (chainIncrements x approximants) pieces)
    (hcounts : List.Forall₂
      (fun p exponent => p.centers.encard ≤ ((2 ^ exponent : ℕ) : ℕ∞))
      pieces exponents)
    (hexponent : exponents.sum ≤ k - 1) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ sumRadii pieces := by
  have hprod : (pieces.map (fun p => p.centers.encard)).prod ≤
      ((2 ^ exponents.sum : ℕ) : ℕ∞) :=
    list_product_le_dyadic_of_forall₂
      (fun p : CoverPiece X => p.centers.encard) pieces exponents hcounts
  have hbudget : (pieces.map (fun p => p.centers.encard)).prod ≤
      ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
    calc
      _ ≤ ((2 ^ exponents.sum : ℕ) : ℕ∞) := hprod
      _ ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) hexponent
  exact entropyNumber_le_of_approximation_chain K pieces k hchain hbudget

/-- A norm approximation by a finite-dimensional subspace turns a bounded set
into an ambient-center cover.  The output radius is the sum of the subspace
net radius and the approximation error. -/
theorem exists_approximation_cover
    (K : Set X) (V : Submodule ℝ X)
    [FiniteDimensional ℝ V] [Nontrivial V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    {R δ ε : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ R)
    (happrox : ∀ x ∈ K, ∃ v : V, ‖x - (v : X)‖ ≤ δ) :
    ∃ C : Set X, C.Finite ∧
      Metric.IsCover (NNReal.mk (ε + δ) (by positivity)) K C ∧
      C.encard ≤ ↑(Nat.ceil ((1 + 2 * (R + δ) / ε) ^ Module.finrank ℝ V)) := by
  classical
  obtain ⟨C, hCball, hCfin, hCcover, hCcard⟩ :=
    HaarQuarter.TheoremF.FiniteDimensionalCovering.exists_submodule_ball_cover
      V (R + δ) ε (by positivity) hε
  refine ⟨C, hCfin, ?_, hCcard⟩
  change ∀ ⦃x⦄, x ∈ K →
    ∃ y ∈ C, edist x y ≤ (NNReal.mk (ε + δ) (by positivity) : ENNReal)
  intro x hx
  obtain ⟨v, hv⟩ := happrox x hx
  have hvnorm : ‖(v : X)‖ ≤ R + δ := by
    calc
      ‖(v : X)‖ = ‖x - (x - (v : X))‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖x - (v : X)‖ := norm_sub_le _ _
      _ ≤ R + δ := add_le_add (hbound x hx) hv
  have hvball : (v : X) ∈
      HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage V (R + δ) :=
    ⟨v, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hvnorm), rfl⟩
  obtain ⟨y, hyC, hvy⟩ := hCcover hvball
  have hdist : dist x y ≤ δ + ε := by
    calc
      dist x y ≤ dist x (v : X) + dist (v : X) y := dist_triangle x (v : X) y
      _ ≤ δ + ε := by
        have h1 : dist x (v : X) ≤ δ := by
          simpa [dist_eq_norm] using hv
        have h2 : dist (v : X) y ≤ ε := by
          have h2' : edist (v : X) y ≤ (NNReal.mk ε hε.le : ENNReal) := by
            change edist (v : X) y ≤ (NNReal.mk ε hε.le : ENNReal) at hvy
            exact hvy
          have h2'' : dist (v : X) y ≤ ε := by
            have hcast : (↑(nndist (v : X) y) : ℝ) = nndist (v : X) y := rfl
            have hnnd : nndist (v : X) y ≤ (NNReal.mk ε hε.le : ℝ≥0) :=
              (edist_le_coe.mp h2')
            exact_mod_cast hnnd
          exact h2''
        linarith
  have hdist' : edist x y ≤ (NNReal.mk (ε + δ) (by positivity) : ENNReal) := by
    rw [edist_dist]
    rw [← ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ ε + δ)]
    apply ENNReal.ofReal_le_ofReal
    simpa [add_comm] using hdist
  exact ⟨y, hyC, hdist'⟩

private theorem dyadic_geom_sum_le (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), 2 ^ j) ≤ 2 ^ (L + 1) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range (L + 1), 2 ^ j) + 2 ^ (L + 1)
            ≤ 2 ^ (L + 1) + 2 ^ (L + 1) := by gcongr
        _ = 2 ^ (L + 2) := by rw [pow_succ, pow_succ]; ring

/-- The dyadic weighted sum appearing in the scale-by-scale volumetric Carl
cover is bounded by a constant times its final dyadic dimension.  The weight
`L-j+1` records the logarithm of the ratio between the increment radius and
the allocated net accuracy at scale `j`. -/
theorem dyadicCarl_weighted_sum_le (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L - j + 1)) ≤ 4 * 2 ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
      have hgeom := dyadic_geom_sum_le L
      rw [Finset.sum_range_succ]
      have hsplit :
          (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L + 1 - j + 1)) =
            (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L - j + 1)) +
              (∑ j ∈ Finset.range (L + 1), 2 ^ j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j ≤ L := by simp only [Finset.mem_range] at hj; omega
        rw [show L + 1 - j + 1 = (L - j + 1) + 1 by omega]
        ring
      calc
        (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L + 1 - j + 1)) +
            2 ^ (L + 1) * (L + 1 - (L + 1) + 1) =
            (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L - j + 1)) +
              (∑ j ∈ Finset.range (L + 1), 2 ^ j) + 2 ^ (L + 1) := by
                rw [hsplit]
                norm_num
        _ ≤ 4 * 2 ^ L + 2 ^ (L + 1) + 2 ^ (L + 1) := by
              gcongr
        _ = 4 * 2 ^ (L + 1) := by rw [pow_succ]; ring

/-- One volumetric increment net at scale `j` costs at most an exponential in
`2^j(L-j+1)`, provided its radius-to-accuracy ratio has the standard
`2^{3(L-j)}` scale. This is the local numerical estimate behind the dyadic
multiscale budget. -/
theorem dyadic_volumetric_card_bound {L j n : ℕ} {R ε : ℝ}
    (hLj : j ≤ L) (hR : 0 ≤ R) (hε : 0 < ε)
    (hdim : n ≤ 2 ^ (j + 1))
    (hratio : R / ε ≤ 10 * 2 ^ (3 * (L - j))) :
    Nat.ceil ((1 + 2 * R / ε) ^ n) ≤
      2 ^ (24 * 2 ^ j * (L - j + 1)) := by
  let q : ℕ := 3 * (L - j) + 5
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ (3 * (L - j)) :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hbase : 1 + 2 * R / ε ≤ (2 : ℝ) ^ q := by
    dsimp [q]
    have hmul : 1 + 20 * (2 : ℝ) ^ (3 * (L - j)) ≤
        32 * (2 : ℝ) ^ (3 * (L - j)) := by nlinarith [hpow1]
    calc
      1 + 2 * R / ε = 1 + 2 * (R / ε) := by ring
      _ ≤ 1 + 20 * (2 : ℝ) ^ (3 * (L - j)) := by linarith [hratio]
      _ ≤ 32 * (2 : ℝ) ^ (3 * (L - j)) := hmul
      _ = (2 : ℝ) ^ (3 * (L - j)) * 32 := by ring
      _ = (2 : ℝ) ^ (3 * (L - j) + 5) := by rw [pow_add]; norm_num
  have hbase0 : 0 ≤ 1 + 2 * R / ε := by positivity
  have hpow : (1 + 2 * R / ε) ^ n ≤
      (2 : ℝ) ^ (q * n) := by
    calc
      (1 + 2 * R / ε) ^ n ≤ ((2 : ℝ) ^ q) ^ n :=
        pow_le_pow_left₀ hbase0 hbase n
      _ = (2 : ℝ) ^ (q * n) := by rw [← pow_mul]
  have hdimcast : (n : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast hdim
  have hexp : q * n ≤ 24 * 2 ^ j * (L - j + 1) := by
    dsimp [q]
    have hq : 3 * (L - j) + 5 ≤ 12 * (L - j + 1) := by omega
    calc
      (3 * (L - j) + 5) * n ≤ (3 * (L - j) + 5) * 2 ^ (j + 1) :=
        Nat.mul_le_mul_left _ hdim
      _ ≤ 12 * (L - j + 1) * 2 ^ (j + 1) := Nat.mul_le_mul_right _ hq
      _ = 24 * 2 ^ j * (L - j + 1) := by rw [pow_succ]; ring
  have hceilreal : (1 + 2 * R / ε) ^ n ≤
      (2 : ℝ) ^ (24 * 2 ^ j * (L - j + 1)) := by
    calc
      _ ≤ (2 : ℝ) ^ (q * n) := hpow
      _ ≤ (2 : ℝ) ^ (24 * 2 ^ j * (L - j + 1)) := by
        exact_mod_cast (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp)
  apply Nat.ceil_le.mpr
  exact_mod_cast hceilreal

/-- Construct an actual increment cover piece and carry its volumetric bound
through the dyadic budget estimate. -/
theorem exists_dyadic_submodule_ball_piece (V : Submodule ℝ X)
    [FiniteDimensional ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V]
    {L j : ℕ} {R ε : ℝ} (hLj : j ≤ L) (hR : 0 ≤ R) (hε : 0 < ε)
    (hdim : Module.finrank ℝ V ≤ 2 ^ (j + 1))
    (hratio : R / ε ≤ 10 * 2 ^ (3 * (L - j))) :
    ∃ p : CoverPiece X,
      p.source = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage V R ∧
      p.radius = NNReal.mk ε hε.le ∧
      p.centers.encard ≤
        ((2 ^ (24 * 2 ^ j * (L - j + 1)) : ℕ) : ℕ∞) := by
  obtain ⟨p, hp, hradius, hcard⟩ :=
    exists_submodule_ball_piece_general V hR hε
  refine ⟨p, hp, hradius, ?_⟩
  calc
    p.centers.encard ≤
        ↑(Nat.ceil ((1 + 2 * R / ε) ^ Module.finrank ℝ V)) := hcard
    _ ≤ ((2 ^ (24 * 2 ^ j * (L - j + 1)) : ℕ) : ℕ∞) := by
      exact_mod_cast dyadic_volumetric_card_bound hLj hR hε hdim hratio

/-- Build one actual finite-dimensional increment cover from two finite
width spaces, including the needed complete/Borel structures on their sum. -/
theorem exists_sup_increment_piece
    (V W : Submodule ℝ X) [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    {L j : ℕ} {R ε : ℝ} (hLj : j ≤ L) (hR : 0 ≤ R) (hε : 0 < ε)
    (hdim : Module.finrank ℝ (V ⊔ W : Submodule ℝ X) ≤ 2 ^ (j + 1))
    (hratio : R / ε ≤ 10 * 2 ^ (3 * (L - j))) :
    ∃ p : CoverPiece X,
      p.source = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
        (V ⊔ W) R ∧ p.radius = NNReal.mk ε hε.le ∧
      p.centers.encard ≤ ((2 ^ (24 * 2 ^ j * (L - j + 1)) : ℕ) : ℕ∞) := by
  let U : Submodule ℝ X := V ⊔ W
  letI : FiniteDimensional ℝ U := inferInstance
  letI : CompleteSpace U := FiniteDimensional.complete ℝ U
  letI : MeasurableSpace U := borel U
  letI : BorelSpace U := ⟨rfl⟩
  exact exists_dyadic_submodule_ball_piece U hLj hR hε hdim hratio

/-- Select the actual volumetric cover at every dyadic increment scale and
attach those pieces to the already-verified approximation chain. -/
theorem exists_selected_width_cover_pieces
    (K : Set X) (L : ℕ) [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (V : Fin (L + 1) → Submodule ℝ X)
    (f : ∀ j, {x : X // x ∈ K} → X)
    (δ : Fin (L + 1) → ℝ) (η : Fin L → ℝ)
    (hzero : ∀ x : {x : X // x ∈ K}, f 0 x = 0)
    (hrank : ∀ j, Module.rank ℝ (V j) ≤ ((2 ^ j.val - 1 : ℕ) : Cardinal))
    (hmem : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}), f j x ∈ V j)
    (happrox : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}),
      ‖(x : X) - f j x‖ ≤ δ j)
    (hfd : ∀ j, FiniteDimensional ℝ (V j))
    (hδ : ∀ j, 0 ≤ δ j) (hη : ∀ j, 0 < η j)
    (hratio : ∀ j : Fin L,
      (δ j.succ + δ j.castSucc) / η j ≤
        10 * 2 ^ (3 * (L - (j.val + 1)))) :
    ∃ P : Fin L → CoverPiece X,
      (∀ j : Fin L,
        (P j).source =
          HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
            (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc) ∧
        (P j).radius = NNReal.mk (η j) (hη j).le ∧
        (P j).centers.encard ≤
          ((2 ^ (24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1)) : ℕ) : ℕ∞)) ∧
      ∀ x : {x : X // x ∈ K},
        List.Forall₂ (fun z p => z ∈ p.source)
          (chainIncrements (x : X) (List.ofFn fun j : Fin (L + 1) => f j x))
          ((zeroBallPiece 0 : CoverPiece X) ::
            (List.ofFn P ++ [zeroBallPiece (NNReal.mk (δ (Fin.last L))
              (hδ (Fin.last L))) ])) := by
  classical
  letI : ∀ j, FiniteDimensional ℝ (V j) := hfd
  have hselected := selected_width_approximation_chain K L V f δ hzero hmem happrox
  let Q : Fin L → CoverPiece X := fun j =>
    Classical.choose (exists_sup_increment_piece (V j.succ) (V j.castSucc)
      (L := L) (j := j.val + 1) (R := δ j.succ + δ j.castSucc) (ε := η j)
      (by omega) (add_nonneg (hδ j.succ) (hδ j.castSucc)) (hη j)
      (by simpa [Nat.add_assoc] using
        (finrank_consecutive_width_sup_le V hrank hfd j))
      (hratio j))
  have hQ (j : Fin L) :
      (Q j).source = HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc) ∧
      (Q j).radius = NNReal.mk (η j) (hη j).le ∧
      (Q j).centers.encard ≤
        ((2 ^ (24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1)) : ℕ) : ℕ∞) := by
    exact Classical.choose_spec (exists_sup_increment_piece (V j.succ) (V j.castSucc)
      (L := L) (j := j.val + 1) (R := δ j.succ + δ j.castSucc) (ε := η j)
      (by omega) (add_nonneg (hδ j.succ) (hδ j.castSucc)) (hη j)
      (by simpa [Nat.add_assoc] using
        (finrank_consecutive_width_sup_le V hrank hfd j))
      (hratio j))
  refine ⟨Q, hQ, ?_⟩
  intro x
  have hzeroSource : (zeroBallPiece 0 : CoverPiece X).source = ({0} : Set X) := by
    ext y
    simp [zeroBallPiece, Metric.closedBall, dist_eq_norm]
  have htailSource :
      (zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L))) : CoverPiece X).source =
        Metric.closedBall (0 : X) (δ (Fin.last L)) := by rfl
  have hmidSource : List.map CoverPiece.source (List.ofFn Q) =
      List.ofFn (fun j : Fin L =>
        HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc)) := by
    rw [List.map_ofFn]
    congr 1
    funext j
    exact (hQ j).1
  have hsrc :
      ((zeroBallPiece 0 : CoverPiece X) ::
        (List.ofFn Q ++ [zeroBallPiece (NNReal.mk (δ (Fin.last L))
          (hδ (Fin.last L))) ])).map CoverPiece.source =
      ({0} :: (List.ofFn (fun j : Fin L =>
        HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
          (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc)) ++
        [Metric.closedBall (0 : X) (δ (Fin.last L))])) := by
    calc
      _ = (zeroBallPiece 0).source ::
          (List.map CoverPiece.source (List.ofFn Q) ++
            [(zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L)))).source]) := by
              simp
      _ = _ := by rw [hzeroSource, hmidSource, htailSource]
  have hx := hselected x
  apply (List.forall₂_map_right_iff
    (R := fun z S => z ∈ S) (f := CoverPiece.source)).mp
  rw [hsrc]
  exact hx

/-- Consecutive near-approximants from two (not necessarily nested)
subspaces have their difference in the sum subspace, with the expected sum
of approximation errors. -/
theorem approximation_increment_mem_ball_sup
    {V W : Submodule ℝ X} {x y z : X} {δ ε : ℝ}
    (hy : y ∈ V) (hz : z ∈ W)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hyerr : ‖x - y‖ ≤ δ) (hzerr : ‖x - z‖ ≤ ε) :
    y - z ∈ V ⊔ W ∧ ‖y - z‖ ≤ δ + ε := by
  constructor
  · exact Submodule.sub_mem_sup hy hz
  · calc
      ‖y - z‖ = ‖(y - x) + (x - z)‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
      _ = ‖x - y‖ + ‖x - z‖ := by rw [norm_sub_rev]
      _ ≤ δ + ε := add_le_add hyerr hzerr

/-- The actual increment scales are the nonzero levels of the dyadic sum,
so their total logarithmic budget is bounded by the full level sum. -/
theorem dyadicCarl_increment_exponent_sum_le (L : ℕ) :
    (∑ j : Fin L, 24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1)) ≤
      96 * 2 ^ L := by
  let w : Fin (L + 1) → ℕ := fun j => 24 * 2 ^ j.val * (L - j.val + 1)
  have hshift :
      (∑ j : Fin L, 24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1)) =
        ∑ j : Fin L, w j.succ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [w, Nat.add_assoc]
  have hfull : (∑ j : Fin (L + 1), w j) ≤ 96 * 2 ^ L := by
    have hbase := dyadicCarl_weighted_sum_le L
    have hscaled : 24 * (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L - j + 1)) ≤
        96 * 2 ^ L := by nlinarith
    have hcast :
        (∑ j ∈ Finset.range (L + 1), 24 * 2 ^ j * (L - j + 1)) ≤
          96 * 2 ^ L := by
      calc
        _ = 24 * (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L - j + 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ ≤ 96 * 2 ^ L := hscaled
    rw [← Fin.sum_univ_eq_sum_range] at hcast
    simpa [w] using hcast
  have hdecomp :
      (∑ j : Fin (L + 1), w j) = w 0 + ∑ j : Fin L, w j.succ := by
    simpa using (Fin.sum_univ_succ w)
  rw [hshift]
  calc
    (∑ j : Fin L, w j.succ) ≤ ∑ j : Fin (L + 1), w j := by
      rw [hdecomp]
      exact Nat.le_add_left _ _
    _ ≤ 96 * 2 ^ L := hfull

/-- The actual finite-dimensional Carl chain gives a concrete entropy upper
bound at index `96·2^L+1`; the only remaining scalar quantity is the sum of
its explicitly constructed radii. -/
theorem exists_entropy_cover_of_width_approximants
    (K : Set X) (L : ℕ) [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (V : Fin (L + 1) → Submodule ℝ X)
    (f : ∀ j, {x : X // x ∈ K} → X)
    (δ : Fin (L + 1) → ℝ) (η : Fin L → ℝ)
    (hzero : ∀ x : {x : X // x ∈ K}, f 0 x = 0)
    (hrank : ∀ j, Module.rank ℝ (V j) ≤ ((2 ^ j.val - 1 : ℕ) : Cardinal))
    (hmem : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}), f j x ∈ V j)
    (happrox : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}),
      ‖(x : X) - f j x‖ ≤ δ j)
    (hfd : ∀ j, FiniteDimensional ℝ (V j))
    (hδ : ∀ j, 0 ≤ δ j) (hη : ∀ j, 0 < η j)
    (hratio : ∀ j : Fin L,
      (δ j.succ + δ j.castSucc) / η j ≤
        10 * 2 ^ (3 * (L - (j.val + 1)))) :
    ∃ P : Fin L → CoverPiece X,
      (∀ j : Fin L,
        (P j).source =
          HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
            (V j.succ ⊔ V j.castSucc) (δ j.succ + δ j.castSucc) ∧
        (P j).radius = NNReal.mk (η j) (hη j).le ∧
        (P j).centers.encard ≤
          ((2 ^ (24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1)) : ℕ) : ℕ∞)) ∧
      HaarQuarter.TheoremD.entropyNumber (96 * 2 ^ L + 1) K ≤
        sumRadii ((zeroBallPiece 0 : CoverPiece X) ::
          (List.ofFn P ++ [zeroBallPiece (NNReal.mk (δ (Fin.last L))
            (hδ (Fin.last L))) ])) := by
  classical
  obtain ⟨P, hP, hchain⟩ := exists_selected_width_cover_pieces K L V f δ η
    hzero hrank hmem happrox hfd hδ hη hratio
  let pieces : List (CoverPiece X) :=
    (zeroBallPiece 0 : CoverPiece X) ::
      (List.ofFn P ++ [zeroBallPiece (NNReal.mk (δ (Fin.last L))
        (hδ (Fin.last L)))])
  let exponents : List ℕ := 0 ::
    (List.ofFn (fun j : Fin L => 24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1)) ++ [0])
  have hfirst : (zeroBallPiece 0 : CoverPiece X).centers.encard ≤
      ((2 ^ 0 : ℕ) : ℕ∞) := by simp [zeroBallPiece]
  have hlast :
      (zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L))) : CoverPiece X).centers.encard ≤
        ((2 ^ 0 : ℕ) : ℕ∞) := by simp [zeroBallPiece]
  have hmiddle : List.Forall₂
      (fun p exponent => p.centers.encard ≤ ((2 ^ exponent : ℕ) : ℕ∞))
      (List.ofFn P)
      (List.ofFn (fun j : Fin L => 24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1))) :=
    forall₂_ofFn _ _ _ (fun j => (hP j).2.2)
  have hcounts : List.Forall₂
      (fun p exponent => p.centers.encard ≤ ((2 ^ exponent : ℕ) : ℕ∞))
      pieces exponents := by
    change List.Forall₂ _
      ((zeroBallPiece 0 : CoverPiece X) :: (List.ofFn P ++
        [zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L)))]))
      (0 :: (List.ofFn (fun j : Fin L =>
        24 * 2 ^ (j.val + 1) * (L - (j.val + 1) + 1)) ++ [0]))
    exact List.Forall₂.cons hfirst
      (List.rel_append hmiddle (List.Forall₂.cons hlast List.Forall₂.nil))
  have hexponent : exponents.sum ≤ (96 * 2 ^ L + 1) - 1 := by
    have hsum : exponents.sum ≤ 96 * 2 ^ L := by
      simp [exponents, List.sum_ofFn]
      exact dyadicCarl_increment_exponent_sum_le L
    omega
  have hchain' : ∀ x ∈ K, ∃ approximants : List X,
      List.Forall₂ (fun z p => z ∈ p.source)
        (chainIncrements x approximants) pieces := by
    intro x hx
    let x' : {x : X // x ∈ K} := ⟨x, hx⟩
    refine ⟨List.ofFn (fun j : Fin (L + 1) => f j x'), ?_⟩
    exact hchain x'
  have hEntropy := entropyNumber_le_of_dyadic_approximation_chain K pieces
    (96 * 2 ^ L + 1) exponents hchain' hcounts hexponent
  refine ⟨P, hP, ?_⟩
  simpa [pieces] using hEntropy

/-- Strict dyadic width bounds alone select the approximation spaces and
pointwise maps needed for the concrete entropy upper bound. -/
theorem exists_entropy_cover_of_strict_width_bounds
    (K : Set X) (L : ℕ) [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (δ : Fin (L + 1) → ℝ) (η : Fin L → ℝ)
    (hδ : ∀ j, 0 < δ j)
    (hwidth : ∀ j : Fin (L + 1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2 ^ j.val - 1) <
        ENNReal.ofReal (δ j))
    (hη : ∀ j, 0 < η j)
    (hratio : ∀ j : Fin L,
      (δ j.succ + δ j.castSucc) / η j ≤
        10 * 2 ^ (3 * (L - (j.val + 1)))) :
    ∃ P : Fin L → CoverPiece X,
      (∀ j : Fin L, (P j).radius = NNReal.mk (η j) (hη j).le) ∧
      HaarQuarter.TheoremD.entropyNumber (96 * 2 ^ L + 1) K ≤
        sumRadii ((zeroBallPiece 0 : CoverPiece X) ::
          (List.ofFn P ++ [zeroBallPiece (NNReal.mk (δ (Fin.last L))
            (hδ (Fin.last L)).le) ])) := by
  classical
  obtain ⟨V, hV, hfd, hdata⟩ := exists_selected_width_chain K L δ hδ hwidth
  rcases hdata with ⟨f, hzero, happ, _hchain⟩
  have hmem : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}), f j x ∈ V j :=
    fun j x => (happ j x).1
  have happrox : ∀ (j : Fin (L + 1)) (x : {x : X // x ∈ K}),
      ‖(x : X) - f j x‖ ≤ δ j := fun j x => (happ j x).2
  obtain ⟨P, hP, hEntropy⟩ := exists_entropy_cover_of_width_approximants
    K L V f δ η hzero hV hmem happrox hfd (fun j => (hδ j).le) hη hratio
  exact ⟨P, (fun j => (hP j).2.1), hEntropy⟩

/-- The geometric sum of the noninitial dyadic accuracy weights is bounded by
the next dyadic power. -/
private theorem dyadic_shifted_geom_sum_le (L : ℕ) :
    (∑ j : Fin L, (2 : ℝ) ^ (j.val + 1)) ≤ (2 : ℝ) ^ (L + 1) := by
  by_cases hL : L = 0
  · simp [hL]
  · have hL' : L - 1 + 1 = L := by omega
    have h := dyadic_geom_sum_le (L - 1)
    rw [hL'] at h
    have hsum : (∑ j : Fin L, (2 : ℝ) ^ (j.val + 1)) =
        ∑ j ∈ Finset.range L, (2 : ℝ) ^ (j + 1) := by
      rw [← Fin.sum_univ_eq_sum_range]
    rw [hsum]
    have hmul : (∑ j ∈ Finset.range L, (2 : ℝ) ^ (j + 1)) =
        2 * ∑ j ∈ Finset.range L, (2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
    rw [hmul]
    have hgeom : (∑ j ∈ Finset.range L, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ L := by
      exact_mod_cast h
    calc
      2 * (∑ j ∈ Finset.range L, (2 : ℝ) ^ j) ≤ 2 * (2 : ℝ) ^ L := by
        gcongr
      _ = (2 : ℝ) ^ (L + 1) := by rw [pow_succ]; ring

/-- The exact scalar choice for the dyadic Carl chain: a nonstrict width
upper bound `B 4^{-j}` is made strict by using twice that tolerance, while
the intermediate radii sum to at most `2 B 4^{-L}`. -/
theorem exists_entropy_cover_of_dyadic_width_bound
    (K : Set X) (L : ℕ) [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (B : ℝ) (hB : 0 < B)
    (hwidth : ∀ j : Fin (L + 1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2 ^ j.val - 1) ≤
        ENNReal.ofReal (B / (4 : ℝ) ^ j.val)) :
    ∃ P : Fin L → CoverPiece X,
      HaarQuarter.TheoremD.entropyNumber (96 * 2 ^ L + 1) K ≤
        NNReal.mk (4 * B / (4 : ℝ) ^ L) (by positivity) := by
  classical
  let δ : Fin (L + 1) → ℝ := fun j => 2 * B / (4 : ℝ) ^ j.val
  let η : Fin L → ℝ := fun j => B * (2 : ℝ) ^ (j.val + 1) / (2 : ℝ) ^ (3 * L)
  have hδ : ∀ j, 0 < δ j := by
    intro j
    dsimp [δ]
    positivity
  have hwidth' : ∀ j : Fin (L + 1),
      HaarQuarter.TheoremD.Width.kolmogorovWidth K (2 ^ j.val - 1) <
        ENNReal.ofReal (δ j) := by
    intro j
    have hreal : B / (4 : ℝ) ^ j.val < 2 * B / (4 : ℝ) ^ j.val := by
      have hp : 0 < (4 : ℝ) ^ j.val := by positivity
      exact div_lt_div_of_pos_right (by linarith) hp
    rw [show δ j = 2 * B / (4 : ℝ) ^ j.val by rfl]
    exact lt_of_le_of_lt (hwidth j)
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hreal)
  have hη : ∀ j, 0 < η j := by
    intro j
    dsimp [η]
    positivity
  have hratio : ∀ j : Fin L,
      (δ j.succ + δ j.castSucc) / η j ≤
        10 * 2 ^ (3 * (L - (j.val + 1))) := by
    intro j
    have hj : j.val + 1 ≤ L := j.isLt
    dsimp [δ, η]
    have hp4 : (4 : ℝ) ^ (j.val + 1) = (2 : ℝ) ^ (2 * (j.val + 1)) := by
      norm_num [pow_mul]
    have hp4' : (4 : ℝ) ^ j.val = (2 : ℝ) ^ (2 * j.val) := by
      norm_num [pow_mul]
    rw [hp4, hp4']
    have hden : (2 : ℝ) ^ (3 * L) ≠ 0 := by positivity
    have hpow : 3 * L = 3 * (j.val + 1) + 3 * (L - (j.val + 1)) := by omega
    rw [hpow, pow_add]
    field_simp
    have hdouble : (2 : ℝ) ^ (j.val + 1) = 2 * (2 : ℝ) ^ j.val := by
      rw [pow_succ]
      ring
    have hpow2 : (2 : ℝ) ^ (2 * j.val) = ((2 : ℝ) ^ j.val) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    have hpow2s : (2 : ℝ) ^ (2 * (j.val + 1)) = 4 * ((2 : ℝ) ^ j.val) ^ 2 := by
      rw [show 2 * (j.val + 1) = 2 * j.val + 2 by omega, pow_add, hpow2]
      ring
    have hpow3 : (2 : ℝ) ^ (3 * j.val) = ((2 : ℝ) ^ j.val) ^ 3 := by
      rw [← pow_mul]
      congr 1
      omega
    have hpow3s : (2 : ℝ) ^ (3 * (j.val + 1)) = 8 * ((2 : ℝ) ^ j.val) ^ 3 := by
      rw [show 3 * (j.val + 1) = 3 * j.val + 3 by omega, pow_add]
      rw [hpow3]
      ring
    rw [pow_add, hpow2, hpow2s, hpow3s]
    ring_nf
    rfl
  obtain ⟨P, hPradius, hEntropy⟩ := exists_entropy_cover_of_strict_width_bounds
    K L δ η hδ hwidth' hη hratio
  have hsumη : (∑ j : Fin L, η j) ≤ 2 * B / (4 : ℝ) ^ L := by
    dsimp [η]
    have hgeom := dyadic_shifted_geom_sum_le L
    have hsum : (∑ j : Fin L, B * (2 : ℝ) ^ (j.val + 1) / (2 : ℝ) ^ (3 * L)) =
        B / (2 : ℝ) ^ (3 * L) * ∑ j : Fin L, (2 : ℝ) ^ (j.val + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    have hden : 0 < (2 : ℝ) ^ (3 * L) := by positivity
    calc
      B / (2 : ℝ) ^ (3 * L) * (∑ j : Fin L, (2 : ℝ) ^ (j.val + 1)) ≤
          B / (2 : ℝ) ^ (3 * L) * (2 : ℝ) ^ (L + 1) := by
        gcongr
      _ ≤ 2 * B / (4 : ℝ) ^ L := by
        have h4 : (4 : ℝ) ^ L = (2 : ℝ) ^ (2 * L) := by norm_num [pow_mul]
        rw [h4]
        have hpow : L + 1 + 2 * L = 1 + 3 * L := by omega
        have heq : B / (2 : ℝ) ^ (3 * L) * (2 : ℝ) ^ (L + 1) =
            2 * B / (2 : ℝ) ^ (2 * L) := by
          field_simp
          rw [← pow_add, hpow, show 1 + 3 * L = 3 * L + 1 by omega, pow_succ]
        rw [heq]
  have htail : δ (Fin.last L) = 2 * B / (4 : ℝ) ^ L := by
    simp [δ, Fin.last]
  have htotal : (∑ j : Fin L, η j) + δ (Fin.last L) ≤
      4 * B / (4 : ℝ) ^ L := by
    rw [htail]
    calc
      (∑ j : Fin L, η j) + 2 * B / (4 : ℝ) ^ L ≤
          2 * B / (4 : ℝ) ^ L + 2 * B / (4 : ℝ) ^ L := add_le_add hsumη le_rfl
      _ = 4 * B / (4 : ℝ) ^ L := by ring
  -- The selected cover's radii are exactly the intermediate `η`'s plus the
  -- terminal tolerance; the initial zero-ball contributes no error.
  refine ⟨P, ?_⟩
  have hradii :
      sumRadii ((zeroBallPiece 0 : CoverPiece X) ::
        (List.ofFn P ++ [zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ _).le)])) ≤
        NNReal.mk (4 * B / (4 : ℝ) ^ L) (by positivity) := by
    apply NNReal.coe_le_coe.mp
    have hlist :
        (sumRadii (List.ofFn P ++
          [zeroBallPiece (NNReal.mk (δ (Fin.last L)) (hδ (Fin.last L)).le)]) : ℝ) =
          (∑ j : Fin L, η j) + δ (Fin.last L) := by
      rw [sumRadii_eq_list_sum]
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      simp [List.map_ofFn, List.sum_ofFn, hPradius, htail, zeroBallPiece]
    have hz : (zeroBallPiece (0 : ℝ≥0) : CoverPiece X).radius = 0 := rfl
    simp only [sumRadii]
    rw [hz, zero_add]
    rw [hlist]
    simpa using htotal
  exact hEntropy.trans (ENNReal.coe_le_coe.mpr hradii)

/-- Product budget for all scales `0,…,L` when each scale is paid at the
volumetric cost from `dyadic_volumetric_card_bound`. -/
theorem dyadicCarl_product_budget (L : ℕ) :
    (∏ j ∈ Finset.range (L + 1),
      2 ^ (24 * 2 ^ j * (L - j + 1))) ≤ 2 ^ (96 * 2 ^ L) := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hsum :
      (∑ j ∈ Finset.range (L + 1), 24 * 2 ^ j * (L - j + 1)) =
        24 * (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L - j + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  have hweighted := dyadicCarl_weighted_sum_le L
  have hexp : 24 * (∑ j ∈ Finset.range (L + 1), 2 ^ j * (L - j + 1)) ≤
      96 * 2 ^ L := by nlinarith
  exact Nat.pow_le_pow_right (by omega) hexp

end BrownianSharp.Carl
