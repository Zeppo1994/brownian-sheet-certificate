import BrownianSharp.GaussianRIPNet
import Mathlib.Data.Fintype.Sigma

set_option maxHeartbeats 1000000

/-!
# One Gaussian map on many dictionary spans

The finite sphere-net extension is applied on each coordinate subspace spanned
by a sparse dictionary support.  This is the deterministic glue between a
single finite family of good random directions and restricted norm control on
every supported linear combination.
-/

namespace BrownianSharp.GaussianRIP

/-- If a linear map is well conditioned on a finite unit-sphere net in each of
finitely many subspaces, it is well conditioned on every vector in their
union. The subspace index is arbitrary finite data; in applications it is a
padded list of at most `s` dictionary atoms. -/
theorem finite_subspace_sphere_net_global_bounds
    {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ E] [CompleteSpace E] [Fintype J]
    (A : E →L[ℝ] F) (V : J → Submodule ℝ E)
    (K : J → Type*) [∀ j, Fintype (K j)]
    (v : ∀ j, K j → V j)
    (ε L U : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1) (hU : 0 ≤ U)
    (hcover : ∀ j (x : V j), ‖x‖ = 1 →
      ∃ k, ‖x - v j k‖ ≤ ε)
    (hnet : ∀ j k, L ≤ ‖A (v j k : E)‖ ∧ ‖A (v j k : E)‖ ≤ U) :
    ∀ j (x : V j),
      (L - ε * (U / (1 - ε))) * ‖x‖ ≤ ‖A (x : E)‖ ∧
        ‖A (x : E)‖ ≤ (U / (1 - ε)) * ‖x‖ := by
  intro j x
  letI : Fintype (K j) := inferInstance
  have h := finite_sphere_net_global_bounds
      (A.comp (V j).subtypeL) (v j) ε L U hε hεlt hU
      (by
        intro y hy
        exact hcover j y hy)
      (by
        intro k
        exact hnet j k)
  have hx := h x
  simpa using hx

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- A finite-dimensional family of nonzero subspaces admits simultaneous
finite unit-sphere nets. The cardinality estimate depends only on the common
upper bound `s` for the subspace dimensions, which is what permits a later
union bound over all padded sparse supports. -/
theorem exists_family_finite_unit_sphere_nets
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [Fintype J]
    (V : J → Submodule ℝ E) (hV : ∀ j, Nontrivial (V j))
    (s : ℕ) (hs : ∀ j, Module.finrank ℝ (V j) ≤ s)
    (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1) :
    ∃ C : ∀ j, Set (V j),
      (∀ j, (C j).Finite) ∧
      (∀ j (x : V j), ‖x‖ = 1 →
        ∃ c : C j, ‖x - (‖c.1‖⁻¹ • c.1)‖ ≤ 2 * ε) ∧
      (∀ j (c : C j), ‖‖c.1‖⁻¹ • c.1‖ = 1) ∧
      (∀ j, ((C j).ncard : ℝ) ≤ Nat.ceil ((1 + 2 / ε) ^ s)) := by
  classical
  have hex : ∀ j, ∃ C : Set (V j),
      C.Finite ∧
      (∀ x : V j, ‖x‖ = 1 → ∃ c : C, ‖x - (‖c.1‖⁻¹ • c.1)‖ ≤ 2 * ε) ∧
      (∀ c : C, ‖‖c.1‖⁻¹ • c.1‖ = 1) ∧
      (C.ncard : ℝ) ≤ Nat.ceil ((1 + 2 / ε) ^ Module.finrank ℝ (V j)) := by
    intro j
    letI : Nontrivial (V j) := hV j
    obtain ⟨C, hC, hcover, hunit, hcard⟩ :=
      exists_finite_unit_sphere_net (E := V j) ε hε hεlt
    exact ⟨C, hC, hcover, hunit, hcard⟩
  choose C hCfin hCcover hCunit hCcard using hex
  refine ⟨C, hCfin, hCcover, hCunit, ?_⟩
  intro j
  have hbase : 1 ≤ 1 + 2 / ε := by
    have : 0 < 2 / ε := div_pos (by norm_num) hε
    linarith
  have hpow : (1 + 2 / ε) ^ Module.finrank ℝ (V j) ≤
      (1 + 2 / ε) ^ s := by
    exact pow_le_pow_right₀ hbase (hs j)
  have hceil := Nat.ceil_le_ceil hpow
  exact hCcard j |>.trans (by exact_mod_cast hceil)

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- The union of all the support-specific nets has at most the number of
supports times the volumetric size of one net. -/
theorem family_sphere_net_sigma_card_le
    {J : Type*} [Fintype J] {E : J → Type*}
    (C : ∀ j, Set (E j)) [∀ j, Fintype (C j)]
    (hCfin : ∀ j, (C j).Finite)
    (B : ℕ) (hCcard : ∀ j, ((C j).ncard : ℝ) ≤ (B : ℝ)) :
    Fintype.card (Sigma fun j => C j) ≤ Fintype.card J * B := by
  classical
  have hfiber (j : J) : Fintype.card (C j) ≤ B := by
    have h := hCcard j
    have hn : (C j).ncard ≤ B := by exact_mod_cast h
    simpa only [Set.fintypeCard_eq_ncard] using hn
  calc
    Fintype.card (Sigma fun j => C j) = ∑ j, Fintype.card (C j) := Fintype.card_sigma
    _ ≤ ∑ _j : J, B := Finset.sum_le_sum fun j hj => hfiber j
    _ = Fintype.card J * B := by simp [Finset.sum_const, nsmul_eq_mul]

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- One Gaussian matrix is simultaneously well conditioned on the net centers
from every member of a finite family of subspaces.  The input norm is the
ambient Euclidean norm; its coordinates are exactly those fed to the random
matrix projection law. -/
theorem exists_gaussianMatrix_good_on_subspace_net_centers
    {m N J : ℕ} (V : Fin J → Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (K : Fin J → Type*) [∀ j, Fintype (K j)]
    (v : ∀ j, K j → V j)
    (hv : ∀ j k, ‖(v j k : EuclideanSpace ℝ (Fin N))‖ = 1)
    (hbudget : (Fintype.card (Sigma fun j => K j) : ℝ) *
      (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ ω : Fin m → (Fin N → ℝ),
      ∀ jk : Sigma fun j => K j,
        (m : ℝ) / 2 < ∑ i,
          (gaussianMatrixProjection (fun k => (v jk.1 jk.2 : EuclideanSpace ℝ (Fin N)) k)
            ω i) ^ 2 ∧
        ∑ i,
          (gaussianMatrixProjection (fun k => (v jk.1 jk.2 : EuclideanSpace ℝ (Fin N)) k)
            ω i) ^ 2 < 2 * (m : ℝ) := by
  classical
  have hunit (jk : Sigma fun j => K j) :
      ∑ k : Fin N, ((v jk.1 jk.2 : EuclideanSpace ℝ (Fin N)) k) ^ 2 = 1 := by
    have hnorm := hv jk.1 jk.2
    have hnormsq : ‖(v jk.1 jk.2 : EuclideanSpace ℝ (Fin N))‖ ^ 2 = 1 := by
      rw [hnorm]
      norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at hnormsq
    exact hnormsq
  exact exists_gaussianMatrix_good_on_finite_directions
    (m := m) (N := N) (J := Sigma fun j => K j)
    (u := fun jk k => (v jk.1 jk.2 : EuclideanSpace ℝ (Fin N)) k)
    hunit hbudget

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- The complete finite net/RIP existence step for finitely many nontrivial
subspaces.  The volumetric budget uses only the number of subspaces and their
common dimension bound; no property of the dictionary beyond the spans is
used here. -/
theorem exists_good_gaussian_matrix_on_family_of_subspaces
    {m N : ℕ} {J : Type*} [Fintype J]
    (V : J → Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hV : ∀ j, Nontrivial (V j))
    (s : ℕ) (hs : ∀ j, Module.finrank ℝ (V j) ≤ s)
    (ε : ℝ) (hε : 0 < ε) (hεlt : ε < 1)
    (hbudget : (Fintype.card J : ℝ) *
        (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ (C : ∀ j, Set (V j)),
      (∀ j, (C j).Finite) ∧
      (∀ j (x : V j), ‖x‖ = 1 →
        ∃ c : C j, ‖x - (‖c.1‖⁻¹ • c.1)‖ ≤ 2 * ε) ∧
      (∀ j (c : C j), ‖‖c.1‖⁻¹ • c.1‖ = 1) ∧
      ∃ ω : Fin m → (Fin N → ℝ), ∀ jk : Sigma fun j => C j,
        (m : ℝ) / 2 < ∑ i,
          (gaussianMatrixProjection
            (fun k => ((‖jk.2.1‖⁻¹ • jk.2.1 : V jk.1) : EuclideanSpace ℝ (Fin N)) k)
            ω i) ^ 2 ∧
        ∑ i,
          (gaussianMatrixProjection
            (fun k => ((‖jk.2.1‖⁻¹ • jk.2.1 : V jk.1) : EuclideanSpace ℝ (Fin N)) k)
            ω i) ^ 2 < 2 * (m : ℝ) := by
  classical
  obtain ⟨C, hCfin, hCcover, hCunit, hCcard⟩ :=
    exists_family_finite_unit_sphere_nets V hV s hs ε hε hεlt
  letI : ∀ j, Fintype (C j) := fun j => (hCfin j).fintype
  letI : Fintype (Sigma fun j => C j) := inferInstance
  have hcards := family_sphere_net_sigma_card_le C hCfin
      (Nat.ceil ((1 + 2 / ε) ^ s)) (by
        intro j
        exact hCcard j)
  have hprobBudget :
      (Fintype.card (Sigma fun j => C j) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1 := by
    have htail : 0 ≤ Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100) := by positivity
    have hcards' : (Fintype.card (Sigma fun j => C j) : ℝ) ≤
        (Fintype.card J : ℝ) * (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) := by
      exact_mod_cast hcards
    exact (mul_le_mul_of_nonneg_right hcards' htail).trans_lt hbudget
  have hunit (jk : Sigma fun j => C j) :
      ∑ k : Fin N,
        (((‖jk.2.1‖⁻¹ • jk.2.1 : V jk.1) : EuclideanSpace ℝ (Fin N)) k) ^ 2 = 1 := by
    have hn : ‖((‖jk.2.1‖⁻¹ • jk.2.1 : V jk.1) : EuclideanSpace ℝ (Fin N))‖ = 1 := by
      simpa using hCunit jk.1 jk.2
    have hn2 : ‖((‖jk.2.1‖⁻¹ • jk.2.1 : V jk.1) : EuclideanSpace ℝ (Fin N))‖ ^ 2 = 1 := by
      rw [hn]
      norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at hn2
    exact hn2
  have hgood := exists_gaussianMatrix_good_on_finite_directions
      (m := m) (N := N) (J := Sigma fun j => C j)
      (u := fun jk k =>
        ((‖jk.2.1‖⁻¹ • jk.2.1 : V jk.1) : EuclideanSpace ℝ (Fin N)) k)
      hunit hprobBudget
  exact ⟨C, hCfin, hCcover, hCunit, hgood⟩

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- The linear operator represented by a matrix of Gaussian rows. -/
noncomputable def gaussianMatrixLinearMap {m N : ℕ}
    (ω : Fin m → (Fin N → ℝ)) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin m) := by
  let f : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := {
    toFun := fun x => WithLp.toLp 2 (fun i => ∑ k : Fin N, ω i k * x k)
    map_add' := by
      intro x y
      ext i
      simp [Finset.sum_add_distrib, mul_add]
    map_smul' := by
      intro c x
      ext i
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  }
  exact ⟨f, f.continuous_of_finiteDimensional⟩

@[simp]
theorem gaussianMatrixLinearMap_apply_coord {m N : ℕ}
    (ω : Fin m → (Fin N → ℝ)) (x : EuclideanSpace ℝ (Fin N)) (i : Fin m) :
    gaussianMatrixLinearMap ω x i = ∑ k : Fin N, ω i k * x k := rfl

/-- The output norm squared of the Gaussian matrix is the sum of squared row
measurements used in the probability estimates. -/
theorem gaussianMatrixLinearMap_norm_sq {m N : ℕ}
    (ω : Fin m → (Fin N → ℝ)) (x : EuclideanSpace ℝ (Fin N)) :
    ‖gaussianMatrixLinearMap ω x‖ ^ 2 =
      ∑ i : Fin m, (gaussianMatrixProjection (fun k => x k) ω i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [gaussianMatrixProjection, gaussianMatrixLinearMap_apply_coord, mul_comm]

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- A single Gaussian row matrix is uniformly well conditioned on an entire
finite family of subspaces once its Gaussian union-bound budget pays for their
volumetric nets.  The loss is the standard `ε‖A‖` net approximation. -/
theorem exists_gaussian_matrix_uniform_on_subspaces
    {m N : ℕ} {J : Type*} [Fintype J]
    (V : J → Submodule ℝ (EuclideanSpace ℝ (Fin N)))
    (hV : ∀ j, Nontrivial (V j))
    (s : ℕ) (hs : ∀ j, Module.finrank ℝ (V j) ≤ s)
    (ε : ℝ) (hε : 0 < ε) (hεlt : 2 * ε < 1)
    (hbudget : (Fintype.card J : ℝ) *
        (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ ω : Fin m → (Fin N → ℝ),
      ∀ j (x : V j),
        (Real.sqrt ((m : ℝ) / 2) -
            (2 * ε) * (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * ε))) * ‖x‖ ≤
          ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ ∧
        ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ ≤
          (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * ε)) * ‖x‖ := by
  classical
  obtain ⟨C, hCfin, hCcover, hCunit, ω, hgood⟩ :=
    exists_good_gaussian_matrix_on_family_of_subspaces
      V hV s hs ε hε (by linarith) hbudget
  letI : ∀ j, Fintype (C j) := fun j => (hCfin j).fintype
  have hnet (j : J) (c : C j) :
      Real.sqrt ((m : ℝ) / 2) ≤
          ‖gaussianMatrixLinearMap ω
            ((‖c.1‖⁻¹ • c.1 : V j) : EuclideanSpace ℝ (Fin N))‖ ∧
      ‖gaussianMatrixLinearMap ω
          ((‖c.1‖⁻¹ • c.1 : V j) : EuclideanSpace ℝ (Fin N))‖ ≤
          Real.sqrt (2 * (m : ℝ)) := by
    have hsum := hgood ⟨j, c⟩
    have hnormsq := gaussianMatrixLinearMap_norm_sq ω
      ((‖c.1‖⁻¹ • c.1 : V j) : EuclideanSpace ℝ (Fin N))
    constructor
    · have hsquare : (m : ℝ) / 2 <
          ‖gaussianMatrixLinearMap ω
            ((‖c.1‖⁻¹ • c.1 : V j) : EuclideanSpace ℝ (Fin N))‖ ^ 2 := by
        rw [hnormsq]
        exact hsum.1
      have hroot := (Real.sqrt_lt_sqrt_iff (by positivity : 0 ≤ (m : ℝ) / 2)).2 hsquare
      rw [Real.sqrt_sq (norm_nonneg _)] at hroot
      exact le_of_lt hroot
    · have hsquare :
          ‖gaussianMatrixLinearMap ω
            ((‖c.1‖⁻¹ • c.1 : V j) : EuclideanSpace ℝ (Fin N))‖ ^ 2 ≤
            2 * (m : ℝ) := by
        rw [hnormsq]
        exact le_of_lt hsum.2
      calc
        ‖gaussianMatrixLinearMap ω
            ((‖c.1‖⁻¹ • c.1 : V j) : EuclideanSpace ℝ (Fin N))‖ =
            Real.sqrt (‖gaussianMatrixLinearMap ω
              ((‖c.1‖⁻¹ • c.1 : V j) : EuclideanSpace ℝ (Fin N))‖ ^ 2) := by
                symm
                exact Real.sqrt_sq (norm_nonneg _)
        _ ≤ Real.sqrt (2 * (m : ℝ)) := Real.sqrt_le_sqrt hsquare
  have hglobal := finite_subspace_sphere_net_global_bounds
      (gaussianMatrixLinearMap ω) V (fun j => C j)
      (fun j c => (‖c.1‖⁻¹ • c.1 : V j))
      (2 * ε) (Real.sqrt ((m : ℝ) / 2)) (Real.sqrt (2 * (m : ℝ)))
      (by positivity) hεlt (by positivity)
      (by intro j x hx; exact hCcover j x hx)
      (by intro j c; exact hnet j c)
  exact ⟨ω, hglobal⟩

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- A length-`s` padded word over the dictionary; `none` denotes the zero
atom. -/
abbrev PaddedDictionaryWord (M s : ℕ) := Fin s → Option (Fin M)

def paddedDictionaryAtoms {M s N : ℕ} (v : Fin M → EuclideanSpace ℝ (Fin N))
    (w : PaddedDictionaryWord M s) : Fin s → EuclideanSpace ℝ (Fin N) :=
  fun k => (w k).elim 0 v

def paddedDictionarySpan {M s N : ℕ} (v : Fin M → EuclideanSpace ℝ (Fin N))
    (w : PaddedDictionaryWord M s) :
    Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
  Submodule.span ℝ (Set.range (paddedDictionaryAtoms v w))

def NonemptyPaddedDictionaryWord (M s : ℕ) :=
  {w : PaddedDictionaryWord M s // ∃ k i, w k = some i}

def paddedDictionarySpanFamily {M s N : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N)) :
    NonemptyPaddedDictionaryWord M s →
      Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
  fun w => paddedDictionarySpan v w.1

theorem paddedDictionarySpan_finrank_le {M s N : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N)) (w : PaddedDictionaryWord M s) :
    Module.finrank ℝ (paddedDictionarySpan v w) ≤ s := by
  exact (finrank_range_le_card (paddedDictionaryAtoms v w)).trans (by simp)

theorem paddedDictionarySpan_nontrivial {M s N : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N))
    (hv : ∀ i, v i ≠ 0)
    (w : NonemptyPaddedDictionaryWord M s) :
    Nontrivial (paddedDictionarySpan v w.1) := by
  classical
  obtain ⟨k, i, hki⟩ := w.2
  have hmem : v i ∈ Set.range (paddedDictionaryAtoms v w.1) := by
    refine ⟨k, ?_⟩
    simp [paddedDictionaryAtoms, hki]
  have hspan : v i ∈ paddedDictionarySpan v w.1 :=
    Submodule.subset_span hmem
  apply (nontrivial_iff_exists_ne (0 : paddedDictionarySpan v w.1)).2
  refine ⟨⟨v i, hspan⟩, ?_⟩
  simpa using hv i

theorem nonemptyPaddedDictionaryWord_card_le {M s : ℕ}
    [Fintype (NonemptyPaddedDictionaryWord M s)] :
    Fintype.card (NonemptyPaddedDictionaryWord M s) ≤ (M + 1) ^ s := by
  classical
  letI : Fintype (PaddedDictionaryWord M s) := inferInstance
  calc
    Fintype.card (NonemptyPaddedDictionaryWord M s) ≤
        Fintype.card (PaddedDictionaryWord M s) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = (M + 1) ^ s := by simp [PaddedDictionaryWord]

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- A genuinely finite dictionary RIP witness: with the displayed volumetric
budget, one Gaussian matrix controls every vector in every span generated by
at most `s` dictionary atoms (padded to length `s`). -/
theorem exists_gaussian_matrix_on_sparse_dictionary_spans
    {m N M s : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N))
    (hv : ∀ i, v i ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hεlt : 2 * ε < 1)
    (hbudget : ((M + 1) ^ s : ℝ) *
        (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ ω : Fin m → (Fin N → ℝ),
      ∀ w : NonemptyPaddedDictionaryWord M s,
      ∀ x : paddedDictionarySpan v w.1,
        (Real.sqrt ((m : ℝ) / 2) -
            (2 * ε) * (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * ε))) * ‖x‖ ≤
          ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ ∧
        ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ ≤
          (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * ε)) * ‖x‖ := by
  classical
  letI : Fintype (NonemptyPaddedDictionaryWord M s) :=
    Fintype.subtype (Finset.univ.filter fun w : PaddedDictionaryWord M s =>
      ∃ k i, w k = some i) (by intro w; simp)
  let V : NonemptyPaddedDictionaryWord M s →
      Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    paddedDictionarySpanFamily (s := s) v
  have hV (w : NonemptyPaddedDictionaryWord M s) : Nontrivial (V w) := by
    exact paddedDictionarySpan_nontrivial v hv w
  have hs (w : NonemptyPaddedDictionaryWord M s) : Module.finrank ℝ (V w) ≤ s := by
    exact paddedDictionarySpan_finrank_le v w.1
  have hcountNat := nonemptyPaddedDictionaryWord_card_le (M := M) (s := s)
  have hcount : (Fintype.card (NonemptyPaddedDictionaryWord M s) : ℝ) ≤
      ((M + 1) ^ s : ℝ) := by exact_mod_cast hcountNat
  have htail : 0 ≤ Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100) := by positivity
  have hscale :
      (Fintype.card (NonemptyPaddedDictionaryWord M s) : ℝ) *
          (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
          (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) ≤
        ((M + 1) ^ s : ℝ) * (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
          (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) := by
    gcongr
  exact exists_gaussian_matrix_uniform_on_subspaces V hV s hs ε hε hεlt
    (hscale.trans_lt hbudget)

end BrownianSharp.GaussianRIP

namespace BrownianSharp.GaussianRIP

/-- Padded words whose dictionary span is nonzero. Zero atoms and all-zero
words are deliberately omitted; they contribute only the zero vector and need
no sphere net. -/
def NontrivialPaddedDictionaryWord {M s N : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N)) :=
  {w : PaddedDictionaryWord M s // paddedDictionarySpan (s := s) v w ≠ ⊥}

def nontrivialPaddedDictionarySpanFamily {M s N : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N)) :
    NontrivialPaddedDictionaryWord (s := s) v →
      Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
  fun w => paddedDictionarySpan (s := s) v w.1

theorem nontrivialPaddedDictionaryWord_card_le {M s N : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N))
    [Fintype (NontrivialPaddedDictionaryWord (s := s) v)] :
    Fintype.card (NontrivialPaddedDictionaryWord (s := s) v) ≤ (M + 1) ^ s := by
  classical
  letI : Fintype (PaddedDictionaryWord M s) := inferInstance
  calc
    Fintype.card (NontrivialPaddedDictionaryWord (s := s) v) ≤
        Fintype.card (PaddedDictionaryWord M s) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = (M + 1) ^ s := by simp [PaddedDictionaryWord]

/-- Sparse dictionary norm control without a nonzero-atom assumption. The
family index includes precisely the padded supports with nontrivial span, so
zero dictionary atoms and empty rows do not require special filtering. -/
theorem exists_gaussian_matrix_on_sparse_dictionary_spans_of_any_atoms
    {m N M s : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N))
    (ε : ℝ) (hε : 0 < ε) (hεlt : 2 * ε < 1)
    (hbudget : ((M + 1) ^ s : ℝ) *
        (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ ω : Fin m → (Fin N → ℝ),
      ∀ w : NontrivialPaddedDictionaryWord (s := s) v,
      ∀ x : paddedDictionarySpan (s := s) v w.1,
        (Real.sqrt ((m : ℝ) / 2) -
            (2 * ε) * (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * ε))) * ‖x‖ ≤
          ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ ∧
        ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ ≤
          (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * ε)) * ‖x‖ := by
  classical
  letI : Fintype (PaddedDictionaryWord M s) := inferInstance
  letI : Fintype (NontrivialPaddedDictionaryWord (s := s) v) :=
    Fintype.subtype (Finset.univ.filter fun w : PaddedDictionaryWord M s =>
      paddedDictionarySpan (s := s) v w ≠ ⊥) (by intro w; simp)
  let V : NontrivialPaddedDictionaryWord (s := s) v →
      Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    nontrivialPaddedDictionarySpanFamily v
  have hV (w : NontrivialPaddedDictionaryWord (s := s) v) : Nontrivial (V w) :=
    Submodule.nontrivial_iff_ne_bot.mpr w.2
  have hs (w : NontrivialPaddedDictionaryWord (s := s) v) : Module.finrank ℝ (V w) ≤ s :=
    paddedDictionarySpan_finrank_le v w.1
  have hcountNat := nontrivialPaddedDictionaryWord_card_le (s := s) v
  have hcount : (Fintype.card (NontrivialPaddedDictionaryWord (s := s) v) : ℝ) ≤
      ((M + 1) ^ s : ℝ) := by exact_mod_cast hcountNat
  have htail : 0 ≤ Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100) := by positivity
  have hscale :
      (Fintype.card (NontrivialPaddedDictionaryWord (s := s) v) : ℝ) *
          (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
          (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) ≤
        ((M + 1) ^ s : ℝ) * (Nat.ceil ((1 + 2 / ε) ^ s) : ℝ) *
          (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) := by
    gcongr
  exact exists_gaussian_matrix_uniform_on_subspaces V hV s hs ε hε hεlt
    (hscale.trans_lt hbudget)

end BrownianSharp.GaussianRIP
