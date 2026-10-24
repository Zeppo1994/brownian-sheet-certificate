import BrownianSharp.GaussianRIPDictionaryNet
import BrownianSharp.MaureyHilbert
import BrownianSharp.KGGFiniteDuality

set_option maxHeartbeats 1000000

noncomputable section
open scoped ENNReal

namespace BrownianSharp.GaussianRIP

/-- Encode a length-`s` sample as a padded dictionary word. -/
def paddedWordOfList {M s : ℕ} (l : List (Option (Fin M)))
    (hl : l.length = s) : PaddedDictionaryWord M s :=
  fun i => l.get (Fin.cast hl.symm i)

theorem list_mem_paddedWordOfList {M s : ℕ} (l : List (Option (Fin M)))
    (hl : l.length = s) (o : Option (Fin M)) (ho : o ∈ l) :
    ∃ i, paddedWordOfList l hl i = o := by
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp ho
  have hns : n < s := by omega
  refine ⟨⟨n, hns⟩, ?_⟩
  simp [paddedWordOfList, List.get_eq_getElem, hget]

theorem signedDictionaryAtom_mem_paddedDictionarySpan
    {M s N : ℕ} (v : Fin M → EuclideanSpace ℝ (Fin N))
    (coeff : Fin M → ℝ) (l : List (Option (Fin M))) (hl : l.length = s)
    (o : Option (Fin M)) (ho : o ∈ l) :
    BrownianSharp.signedDictionaryAtom coeff v o ∈
      paddedDictionarySpan v (paddedWordOfList l hl) := by
  obtain ⟨i, hi⟩ := list_mem_paddedWordOfList l hl o ho
  cases o with
  | none => simp [BrownianSharp.signedDictionaryAtom]
  | some j =>
      let W := paddedDictionarySpan v (paddedWordOfList l hl)
      have hmem : v j ∈ paddedDictionarySpan v (paddedWordOfList l hl) := by
        apply Submodule.subset_span
        exact ⟨i, by simp [paddedDictionaryAtoms, hi]⟩
      change (if 0 ≤ coeff j then v j else -v j) ∈ W
      by_cases h : 0 ≤ coeff j
      · simp [h, W, hmem]
      · simpa [h, W] using (paddedDictionarySpan v (paddedWordOfList l hl)).neg_mem hmem

theorem list_signedDictionaryAtom_sum_mem_paddedDictionarySpan
    {M s N : ℕ} (v : Fin M → EuclideanSpace ℝ (Fin N))
    (coeff : Fin M → ℝ) (l : List (Option (Fin M))) (hl : l.length = s) :
    (l.map (BrownianSharp.signedDictionaryAtom coeff v)).sum ∈
      paddedDictionarySpan v (paddedWordOfList l hl) := by
  let W := paddedDictionarySpan v (paddedWordOfList l hl)
  have hlist : List.ofFn (paddedWordOfList l hl) = l := by
    apply List.ext_get (by simp [hl])
    intro n h1 h2
    simp [paddedWordOfList, List.get_ofFn]
  have hsingle : ∀ o ∈ l, BrownianSharp.signedDictionaryAtom coeff v o ∈ W := by
    intro o ho
    exact signedDictionaryAtom_mem_paddedDictionarySpan v coeff l hl o ho
  have hmap := congrArg (List.map (BrownianSharp.signedDictionaryAtom coeff v)) hlist.symm
  rw [hmap, List.map_ofFn, List.sum_ofFn]
  apply Submodule.sum_mem
  intro k hk
  apply hsingle
  have hlen : (List.ofFn (paddedWordOfList l hl)).length = s :=
    by simp
  have hget := List.get_mem (List.ofFn (paddedWordOfList l hl))
    (Fin.cast hlen.symm k)
  simpa [paddedWordOfList, hlist] using hget

/-- Fixed-radius normalization of the Gaussian RIP witness. At radius `1/64`
the net theorem gives lower and upper singular-value bounds `1/3` and `1` on
all sparse dictionary spans, after dividing by its deterministic upper factor. -/
theorem exists_normalized_good_gaussian_matrix_on_sparse_dictionary_spans
    {m N M s : ℕ} (hm : 0 < m)
    (v : Fin M → EuclideanSpace ℝ (Fin N))
    (hbudget : ((M + 1) ^ s : ℝ) * (Nat.ceil (129 ^ s : ℝ) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin m),
      ∀ w : NontrivialPaddedDictionaryWord (s := s) v,
      ∀ x : paddedDictionarySpan v w.1,
        (1 / 3 : ℝ) * ‖x‖ ≤ ‖A (x : EuclideanSpace ℝ (Fin N))‖ ∧
          ‖A (x : EuclideanSpace ℝ (Fin N))‖ ≤ ‖x‖ := by
  classical
  have hbudget' : ((M + 1) ^ s : ℝ) *
      (Nat.ceil ((1 + 2 / (1 / 64 : ℝ)) ^ s) : ℝ) *
      (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1 := by
    norm_num at hbudget ⊢
    exact hbudget
  obtain ⟨ω, hω⟩ := exists_gaussian_matrix_on_sparse_dictionary_spans_of_any_atoms
    (m := m) (N := N) (M := M) (s := s) v (1 / 64 : ℝ) (by norm_num)
    (by norm_num) hbudget'
  let C : ℝ := Real.sqrt (2 * (m : ℝ)) / (1 - 2 * (1 / 64 : ℝ))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hroot : Real.sqrt ((m : ℝ) / 2) = Real.sqrt (2 * (m : ℝ)) / 2 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
    rw [show Real.sqrt (2 * (m : ℝ)) / 2 * (Real.sqrt (2 * (m : ℝ)) / 2) =
        (Real.sqrt (2 * (m : ℝ))) ^ 2 / 4 by ring,
      Real.sq_sqrt (by positivity)]
    ring
  have hratio :
      (Real.sqrt ((m : ℝ) / 2) -
        (2 * (1 / 64 : ℝ)) *
          (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * (1 / 64 : ℝ)))) / C =
        (29 / 64 : ℝ) := by
    rw [hroot]
    dsimp [C]
    have hden : 1 - 2 * (1 / 64 : ℝ) = (31 / 32 : ℝ) := by norm_num
    rw [hden]
    have hmroot : Real.sqrt (2 * (m : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp
    <;> ring
  have hratio' : (1 / 3 : ℝ) ≤
      (Real.sqrt ((m : ℝ) / 2) -
        (2 * (1 / 64 : ℝ)) *
          (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * (1 / 64 : ℝ)))) / C := by
    rw [hratio]
    norm_num
  refine ⟨C⁻¹ • gaussianMatrixLinearMap ω, ?_⟩
  intro w x
  obtain ⟨hlow, hupp⟩ := hω w x
  have hnorm : ‖(C⁻¹ • gaussianMatrixLinearMap ω) (x : EuclideanSpace ℝ (Fin N))‖ =
      C⁻¹ * ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ := by
    change ‖C⁻¹ • gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hC.le)]
  constructor
  · have hraw := mul_le_mul_of_nonneg_right hratio' (norm_nonneg (x : EuclideanSpace ℝ (Fin N)))
    have hscaled := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hC.le)
    rw [hnorm]
    have hmiddle :
        ((Real.sqrt ((m : ℝ) / 2) -
          (2 * (1 / 64 : ℝ)) *
            (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * (1 / 64 : ℝ)))) / C) * ‖x‖ ≤
          C⁻¹ * ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ := by
      calc
        _ = C⁻¹ * (Real.sqrt ((m : ℝ) / 2) -
            (2 * (1 / 64 : ℝ)) *
              (Real.sqrt (2 * (m : ℝ)) / (1 - 2 * (1 / 64 : ℝ)))) * ‖x‖ := by ring
        _ ≤ C⁻¹ * ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ := by
          simpa [mul_assoc] using hscaled
    exact hraw.trans hmiddle
  · have hscaled := mul_le_mul_of_nonneg_left hupp (inv_nonneg.mpr hC.le)
    rw [hnorm]
    calc
      C⁻¹ * ‖gaussianMatrixLinearMap ω (x : EuclideanSpace ℝ (Fin N))‖ ≤
          C⁻¹ * (C * ‖x‖) := hscaled
      _ = ‖x‖ := by field_simp

/-- A kernel vector synthesized from an ℓ¹-unit dictionary coefficient vector
must be small. The proof combines uniform sparse-span RIP with the joint
Hilbert-valued Maurey average; zero dictionary atoms are allowed. -/
theorem exists_gaussian_dictionary_kernel_bound
    {m N M s : ℕ} (hm : 0 < m) (hs : 1 ≤ s)
    (v : Fin M → EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (hR : 0 ≤ R) (hbound : ∀ i, ‖v i‖ ≤ R)
    (hbudget : ((M + 1) ^ s : ℝ) * (Nat.ceil (129 ^ s : ℝ) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ A : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin m),
      ∀ coeff : Fin M → ℝ, ∀ x : EuclideanSpace ℝ (Fin N),
        (∑ i : Fin M, |coeff i|) ≤ 1 →
        x = ∑ i : Fin M, coeff i • v i →
        A x = 0 →
        ‖x‖ ≤ Real.sqrt 50 * R / Real.sqrt (s : ℝ) := by
  classical
  obtain ⟨A, hA⟩ := exists_normalized_good_gaussian_matrix_on_sparse_dictionary_spans
    hm v hbudget
  have hAbound : ∀ i, ‖A (v i)‖ ≤ 2 * R := by
    intro i
    by_cases hvi : v i = 0
    · simp [hvi]
      positivity
    · let word : PaddedDictionaryWord M s := fun _ => some i
      have hmem : v i ∈ paddedDictionarySpan v word := by
        apply Submodule.subset_span
        refine ⟨⟨0, ?_⟩, ?_⟩
        · exact hs
        · simp [paddedDictionaryAtoms, word]
      have hne : paddedDictionarySpan v word ≠ ⊥ := by
        intro h
        have : v i = 0 := by simpa [h] using hmem
        exact hvi this
      let w : NontrivialPaddedDictionaryWord (s := s) v := ⟨word, hne⟩
      have hv := hA w ⟨v i, hmem⟩
      calc
        ‖A (v i)‖ ≤ ‖v i‖ := hv.2
        _ ≤ R := hbound i
        _ ≤ 2 * R := by linarith
  refine ⟨A, ?_⟩
  intro coeff x hcoeff hx hAx
  obtain ⟨l, hl, hjoint⟩ := BrownianSharp.exists_signed_dictionary_joint_image_average
    A coeff v x R hcoeff hx hAx hR hbound hAbound s hs
  let y : EuclideanSpace ℝ (Fin N) :=
    (s : ℝ)⁻¹ • (l.map (BrownianSharp.signedDictionaryAtom coeff v)).sum
  have happrox : ‖y - x‖ ^ 2 + ‖A y‖ ^ 2 ≤ 5 * R ^ 2 / (s : ℝ) := by
    simpa [y] using hjoint
  have hyspan : y ∈ paddedDictionarySpan v (paddedWordOfList l hl) := by
    change (s : ℝ)⁻¹ • (l.map (BrownianSharp.signedDictionaryAtom coeff v)).sum ∈ _
    exact (paddedDictionarySpan v (paddedWordOfList l hl)).smul_mem _
      (list_signedDictionaryAtom_sum_mem_paddedDictionarySpan v coeff l hl)
  have hybound : (1 / 3 : ℝ) * ‖y‖ ≤ ‖A y‖ := by
    by_cases hspan : paddedDictionarySpan v (paddedWordOfList l hl) = ⊥
    · have hy0 : y = 0 := by simpa [hspan] using hyspan
      simp [hy0]
    · let w : NontrivialPaddedDictionaryWord (s := s) v :=
        ⟨paddedWordOfList l hl, hspan⟩
      have h := hA w ⟨y, hyspan⟩
      exact h.1
  have hySmall : ‖y‖ ≤ 3 * ‖A y‖ := by linarith
  have htri : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    have heq : x = (x - y) + y := by abel
    calc
      ‖x‖ = ‖(x - y) + y‖ := congrArg norm heq
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have hxSmall : ‖x‖ ≤ ‖x - y‖ + 3 * ‖A y‖ :=
    htri.trans (add_le_add (le_refl _) hySmall)
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsqbound : ‖x‖ ^ 2 ≤ 50 * R ^ 2 / (s : ℝ) := by
    have happrox' : ‖x - y‖ ^ 2 + ‖A y‖ ^ 2 ≤ 5 * R ^ 2 / (s : ℝ) := by
      simpa [norm_sub_rev] using happrox
    have hnonneg1 : 0 ≤ ‖x‖ := norm_nonneg _
    have hnonneg2 : 0 ≤ ‖x - y‖ + 3 * ‖A y‖ := by positivity
    have hsquare : ‖x‖ ^ 2 ≤ (‖x - y‖ + 3 * ‖A y‖) ^ 2 := by
      apply (sq_le_sq₀ hnonneg1 hnonneg2).2 hxSmall
    have hcombo : (‖x - y‖ + 3 * ‖A y‖) ^ 2 ≤
        10 * (‖x - y‖ ^ 2 + ‖A y‖ ^ 2) := by
      nlinarith [sq_nonneg (3 * ‖x - y‖ - ‖A y‖)]
    have hcombobound := mul_le_mul_of_nonneg_left happrox' (by norm_num : (0 : ℝ) ≤ 10)
    calc
      ‖x‖ ^ 2 ≤ (‖x - y‖ + 3 * ‖A y‖) ^ 2 := hsquare
      _ ≤ 10 * (‖x - y‖ ^ 2 + ‖A y‖ ^ 2) := hcombo
      _ ≤ 10 * (5 * R ^ 2 / (s : ℝ)) := hcombobound
      _ = 50 * R ^ 2 / (s : ℝ) := by ring
  have htargetnonneg : 0 ≤ Real.sqrt 50 * R / Real.sqrt (s : ℝ) := by
    positivity
  have htargetsq : (Real.sqrt 50 * R / Real.sqrt (s : ℝ)) ^ 2 =
      50 * R ^ 2 / (s : ℝ) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hsreal.le]
  nlinarith [sq_nonneg (‖x‖ - Real.sqrt 50 * R / Real.sqrt (s : ℝ))]

/-- The synthesis map for a finite row dictionary. -/
def dictionarySynthesisMap {N M : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N)) :
    (Fin M → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) where
  toFun coeff := ∑ i : Fin M, coeff i • v i
  map_add' a b := by simp [Finset.sum_add_distrib, add_smul]
  map_smul' c a := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_smul]

/-- Feature map into the finite `ℓ∞` row-coordinate space. -/
noncomputable def dictionaryFeatureMap {N M : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] PiLp ∞ (fun _ : Fin M => ℝ) := by
  let f : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] PiLp ∞ (fun _ : Fin M => ℝ) := {
    toFun := fun x => WithLp.toLp ∞ (fun i => inner ℝ x (v i))
    map_add' := by
      intro x y
      ext i
      simp [inner_add_left]
    map_smul' := by
      intro c x
      ext i
      simp [inner_smul_left]
  }
  exact ⟨f, f.continuous_of_finiteDimensional⟩

@[simp]
theorem dictionaryFeatureMap_apply_coord {N M : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin M) :
    dictionaryFeatureMap v x i = inner ℝ x (v i) := rfl

theorem dictionary_adjoint_pairing {N M : ℕ}
    (v : Fin M → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) (coeff : Fin M → ℝ) :
    (∑ i : Fin M, coeff i * (dictionaryFeatureMap v x) i) =
      inner ℝ x (dictionarySynthesisMap v coeff) := by
  simp only [dictionaryFeatureMap_apply_coord]
  change (∑ i : Fin M, coeff i * inner ℝ x (v i)) =
    inner ℝ x (∑ i : Fin M, coeff i • v i)
  rw [inner_sum]
  simp [inner_smul_right]

/-- KGG dictionary approximation as a concrete subspace witness. The output
includes the rank-`m` image of the orthogonal complement of the random kernel
and a pointwise distance bound for every feature of a unit source vector. -/
theorem exists_dictionary_width_subspace
    {m N M s : ℕ} (hm : 0 < m) (hs : 1 ≤ s)
    (v : Fin M → EuclideanSpace ℝ (Fin N)) (R : ℝ)
    (hR : 0 < R) (hbound : ∀ i, ‖v i‖ ≤ R)
    (hbudget : ((M + 1) ^ s : ℝ) * (Nat.ceil (129 ^ s : ℝ) : ℝ) *
        (Real.exp (-(m : ℝ) / 16) + Real.exp (-(m : ℝ) / 100)) < 1) :
    ∃ V : Submodule ℝ (PiLp ∞ (fun _ : Fin M => ℝ)),
      Module.rank ℝ V ≤ (m : Cardinal) ∧
      ∀ x : EuclideanSpace ℝ (Fin N), ‖x‖ ≤ 1 →
        ∃ y ∈ V, ‖dictionaryFeatureMap v x - y‖ ≤
          2 * (Real.sqrt 50 * R / Real.sqrt (s : ℝ)) := by
  classical
  obtain ⟨A, hkernel⟩ := exists_gaussian_dictionary_kernel_bound hm hs v R
    hR.le hbound hbudget
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := LinearMap.ker A.toLinearMap
  let V : Submodule ℝ (PiLp ∞ (fun _ : Fin M => ℝ)) :=
    BrownianSharp.KGGFiniteDuality.orthogonalImageSubspace M (dictionaryFeatureMap v) W
  have hVrank : Module.rank ℝ V ≤ (m : Cardinal) := by
    let U : (Wᗮ) →ₗ[ℝ] PiLp ∞ (fun _ : Fin M => ℝ) :=
      (dictionaryFeatureMap v).toLinearMap.comp Wᗮ.subtype
    have hWdim : Module.finrank ℝ Wᗮ ≤ m := by
      have horth : Module.finrank ℝ W + Module.finrank ℝ Wᗮ =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := W.finrank_add_finrank_orthogonal
      have hnull : Module.finrank ℝ (LinearMap.range A.toLinearMap) +
          Module.finrank ℝ W = Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
        simpa [W] using A.toLinearMap.finrank_range_add_finrank_ker
      have hrange : Module.finrank ℝ (LinearMap.range A.toLinearMap) ≤
          Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) :=
        (LinearMap.range A.toLinearMap).finrank_le
      have htarget : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
      have heq : Module.finrank ℝ Wᗮ =
          Module.finrank ℝ (LinearMap.range A.toLinearMap) := by omega
      exact heq.trans_le (hrange.trans_eq htarget)
    have hrange : Module.rank ℝ (LinearMap.range U) ≤ Module.rank ℝ Wᗮ :=
      rank_range_le U
    calc
      Module.rank ℝ V = Module.rank ℝ (LinearMap.range U) := by rfl
      _ ≤ Module.rank ℝ Wᗮ := hrange
      _ ≤ (m : Cardinal) :=
        (FiniteDimensional.finrank_le_iff_rank_le.mp hWdim)
  have hVclosed : IsClosed (V : Set (PiLp ∞ (fun _ : Fin M => ℝ))) :=
    Submodule.closed_of_finiteDimensional V
  have hB : ∀ coeff : Fin M → ℝ, (∑ i : Fin M, |coeff i|) ≤ 1 →
      dictionarySynthesisMap v coeff ∈ W →
      ‖dictionarySynthesisMap v coeff‖ ≤ Real.sqrt 50 * R / Real.sqrt (s : ℝ) := by
    intro coeff hcoeff hW
    apply hkernel coeff (dictionarySynthesisMap v coeff) hcoeff
    · rfl
    · exact LinearMap.mem_ker.mp hW
  have hdual : ∀ φ : StrongDual ℝ (PiLp ∞ (fun _ : Fin M => ℝ)),
      (∀ z ∈ V, φ z = 0) → ‖φ‖ ≤ 1 →
        ∀ x : EuclideanSpace ℝ (Fin N), ‖x‖ ≤ 1 →
          |φ (dictionaryFeatureMap v x)| ≤ Real.sqrt 50 * R / Real.sqrt (s : ℝ) := by
    intro φ hφ hφnorm x hx
    let coeff : Fin M → ℝ := fun i => φ (PiLp.single ∞ i 1)
    have hcoeff : (∑ i : Fin M, |coeff i|) ≤ 1 := by
      calc
        _ ≤ ‖φ‖ := BrownianSharp.KGGFiniteDuality.sum_abs_coordinate_coefficients_le_dual_norm φ
        _ ≤ 1 := hφnorm
    have hW : dictionarySynthesisMap v coeff ∈ W := by
      have horth : dictionarySynthesisMap v coeff ∈ Wᗮᗮ := by
        apply (Submodule.mem_orthogonal' _ _).2
        intro z hz
        have hzV : dictionaryFeatureMap v z ∈ V := by
          apply LinearMap.mem_range.mpr
          exact ⟨⟨z, hz⟩, rfl⟩
        have hzφ : φ (dictionaryFeatureMap v z) = 0 := hφ _ hzV
        have hcoord := BrownianSharp.KGGFiniteDuality.strongDual_apply_eq_sum_coordinates φ
          (dictionaryFeatureMap v z)
        have hpair := dictionary_adjoint_pairing v z coeff
        calc
          inner ℝ (dictionarySynthesisMap v coeff) z =
              inner ℝ z (dictionarySynthesisMap v coeff) := real_inner_comm _ _
          _ = ∑ i : Fin M, coeff i * (dictionaryFeatureMap v z) i := hpair.symm
          _ = φ (dictionaryFeatureMap v z) := by simpa [coeff] using hcoord.symm
          _ = 0 := hzφ
      simpa [Submodule.orthogonal_orthogonal] using horth
    have hcoeffnorm := hB coeff hcoeff hW
    have hpair := dictionary_adjoint_pairing v x coeff
    have hcoord := BrownianSharp.KGGFiniteDuality.strongDual_apply_eq_sum_coordinates φ
      (dictionaryFeatureMap v x)
    have heq : φ (dictionaryFeatureMap v x) =
        inner ℝ x (dictionarySynthesisMap v coeff) := by
      calc
        φ (dictionaryFeatureMap v x) =
            ∑ i : Fin M, coeff i * (dictionaryFeatureMap v x) i := by
              simpa [coeff] using hcoord
        _ = inner ℝ x (dictionarySynthesisMap v coeff) := hpair
    rw [heq]
    calc
      |inner ℝ x (dictionarySynthesisMap v coeff)| ≤
          ‖x‖ * ‖dictionarySynthesisMap v coeff‖ := abs_real_inner_le_norm x _
      _ ≤ 1 * (Real.sqrt 50 * R / Real.sqrt (s : ℝ)) := by
        exact mul_le_mul hx hcoeffnorm (norm_nonneg _) (by positivity)
      _ = Real.sqrt 50 * R / Real.sqrt (s : ℝ) := one_mul _
  refine ⟨V, hVrank, ?_⟩
  intro x hx
  have hdist := BrownianSharp.KGGFiniteDuality.infDist_le_of_annihilator_bound
    V (dictionaryFeatureMap v x) (by positivity)
    (fun φ hφ hφnorm => hdual φ hφ hφnorm x hx)
  have hlt : Metric.infDist (dictionaryFeatureMap v x) (V : Set _) <
      2 * (Real.sqrt 50 * R / Real.sqrt (s : ℝ)) := by
    have hC : 0 < Real.sqrt 50 * R / Real.sqrt (s : ℝ) := by positivity
    linarith
  obtain ⟨y, hyV, hyd⟩ :=
    (Metric.infDist_lt_iff (show (V : Set (PiLp ∞ (fun _ : Fin M => ℝ))).Nonempty from
      ⟨0, V.zero_mem⟩)).mp hlt
  exact ⟨y, hyV, le_of_lt (by simpa [dist_eq_norm] using hyd)⟩

end BrownianSharp.GaussianRIP

end
