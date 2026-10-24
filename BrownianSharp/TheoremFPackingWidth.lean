import BrownianSharp.KolmogorovWidth
import BrownianSharp.TheoremFFiniteDimensionalCovering
import Mathlib.Tactic

open scoped BigOperators

namespace HaarQuarter.TheoremF.Carl

open HaarQuarter.TheoremD.Width

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A strict worst-case error bound yields a pointwise approximant at every point of `K`. -/
theorem exists_pointwise_approximation
    (K : Set X) (V : Submodule ℝ X) {r : ENNReal}
    (h : approximationError K V < r) :
    ∀ x ∈ K, ∃ v : V, edist x v < r := by
  intro x hx
  have hsup := iSup_lt_iff.mp (by simpa [approximationError] using h)
  rcases hsup with ⟨b, hbr, hle⟩
  have hdist : Metric.infEDist x (V : Set X) < r :=
    lt_of_le_of_lt (hle ⟨x, hx⟩) hbr
  rcases Metric.infEDist_lt_iff.mp hdist with ⟨v, hv, hxr⟩
  exact ⟨⟨v, hv⟩, by simpa [edist_comm] using hxr⟩

/-- Real-norm form of the strict pointwise approximation consequence. -/
theorem exists_pointwise_norm_approximation
    (K : Set X) (V : Submodule ℝ X) {r : ℝ} (hr : 0 < r)
    (h : approximationError K V < ENNReal.ofReal r) :
    ∀ x ∈ K, ∃ v : V, ‖x - (v : X)‖ < r := by
  intro x hx
  obtain ⟨v, hdist⟩ := exists_pointwise_approximation K V h x hx
  have hdist' : ENNReal.ofReal ‖x - (v : X)‖ < ENNReal.ofReal r := by
    simpa [edist_dist, dist_eq_norm] using hdist
  exact ⟨v, (ENNReal.ofReal_lt_ofReal_iff hr).mp hdist'⟩

end HaarQuarter.TheoremF.Carl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A subspace of finite cardinal rank is finite-dimensional, using rank rather
than `finrank` so that the infinite-dimensional ambient-space case is excluded. -/
theorem finiteDimensional_of_rank_le
    (V : Submodule ℝ X) {n : ℕ} (hV : Module.rank ℝ V ≤ (n : Cardinal)) :
    FiniteDimensional ℝ V := by
  have hlt : Module.rank ℝ V < Cardinal.aleph0 :=
    lt_of_le_of_lt hV Cardinal.natCast_lt_aleph0
  exact Module.rank_lt_aleph0_iff.mp hlt

namespace HaarQuarter.TheoremF.PackingWidth

open HaarQuarter.TheoremD.Width
open HaarQuarter.TheoremF.Carl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Logarithmic packing form, using the direct real-valued volume bound so no
ceiling loss is needed. -/
theorem separated_packing_width_lower_bound_of_log
    (K : Set X) (m : ℕ) (T : Finset X) (R δ : ℝ)
    (hT : ∀ x ∈ T, x ∈ K) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hbound : ∀ x ∈ T, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y)
    (hlog : (m : ℝ) * Real.log (1 + 12 * R / δ) <
      Real.log (T.card : ℝ)) :
    ENNReal.ofReal (δ / 4) ≤ kolmogorovWidth K m := by
  classical
  have hcardgtone : 1 < (T.card : ℝ) := by
    have hlogcard : 0 < Real.log (T.card : ℝ) := by
      have hlarge : 1 ≤ 1 + 12 * R / δ := by
        have hq : 0 ≤ 12 * R / δ := div_nonneg (by positivity) hδ.le
        linarith [hq]
      have hloglarge : 0 ≤ Real.log (1 + 12 * R / δ) := Real.log_nonneg hlarge
      have hmterm : 0 ≤ (m : ℝ) * Real.log (1 + 12 * R / δ) :=
        mul_nonneg (by positivity) hloglarge
      linarith
    exact (Real.log_pos_iff (by positivity)).mp hlogcard
  have hcardgtoneNat : 1 < T.card := by exact_mod_cast hcardgtone
  rcases Finset.one_lt_card.mp hcardgtoneNat with ⟨x, hx, y, hy, hxy⟩
  have hδR : δ ≤ 2 * R := by
    calc
      δ ≤ dist x y := hsep x hx y hy hxy
      _ ≤ ‖x‖ + ‖y‖ := by
        rw [dist_eq_norm]
        exact norm_sub_le x y
      _ ≤ 2 * R := by nlinarith [hbound x hx, hbound y hy]
  have hratio : 2 + 4 * R / δ ≤ 1 + 12 * R / δ := by
    have hRhalf : δ / 2 ≤ R := by nlinarith [hδR]
    field_simp
    nlinarith [hRhalf]
  let b : ℝ := 1 + 12 * R / δ
  have hb : 1 ≤ b := by
    dsimp [b]
    have hq : 0 ≤ 12 * R / δ := div_nonneg (by positivity) hδ.le
    linarith
  have hbpos : 0 < b := by linarith
  have hlogTarget : Real.log (b ^ m) = (m : ℝ) * Real.log b := by
    rw [Real.log_pow]
  have htargetpos : 0 < b ^ m := by positivity
  have hcardpos : 0 < (T.card : ℝ) := by linarith
  have hloglt : Real.log (b ^ m) < Real.log (T.card : ℝ) := by
    rw [hlogTarget]
    simpa [b] using hlog
  have hbigcard : b ^ m < (T.card : ℝ) :=
    (Real.log_lt_log_iff htargetpos hcardpos).mp hloglt
  have hratio' : 1 + 2 * (R + δ / 4) / (δ / 2) ≤ b := by
    dsimp [b]
    have hfactor : 1 + 2 * (R + δ / 4) / (δ / 2) = 2 + 4 * R / δ := by
      field_simp
      <;> ring
    rw [hfactor]
    exact hratio
  have hsmall : ∀ V : {V : Submodule ℝ X // Module.rank ℝ V ≤ (m : Cardinal)},
      ¬ approximationError K V.1 < ENNReal.ofReal (δ / 4) := by
    intro V hsmall
    letI : FiniteDimensional ℝ V.1 := finiteDimensional_of_rank_le V.1 V.2
    have hdim : Module.finrank ℝ V.1 ≤ m :=
      (FiniteDimensional.finrank_le_iff_rank_le).2 V.2
    have hpt : ∀ z ∈ K, ∃ v : V.1, ‖z - (v : X)‖ < δ / 4 :=
      exists_pointwise_norm_approximation K V.1 (by positivity) hsmall
    let a : T.attach → V.1 := fun z => Classical.choose (hpt z.1 (hT z.1.1 z.1.property))
    have ha (z : T.attach) : ‖(z.1.1 : X) - (a z : X)‖ < δ / 4 :=
      Classical.choose_spec (hpt z.1 (hT z.1.1 z.1.property))
    have hnorma (z : T.attach) : ‖(a z : X)‖ ≤ R + δ / 4 := by
      calc
        ‖(a z : X)‖ = ‖(z.1.1 : X) - ((z.1.1 : X) - (a z : X))‖ := by congr 1; abel
        _ ≤ ‖(z.1.1 : X)‖ + ‖(z.1.1 : X) - (a z : X)‖ := norm_sub_le _ _
        _ ≤ R + δ / 4 := add_le_add (hbound z.1.1 z.1.property) (le_of_lt (ha z))
    have hasep (z w : T.attach) (hzw : z ≠ w) :
        δ / 2 < dist (a z : X) (a w : X) := by
      have hzw' : z.1.1 ≠ w.1.1 := by
        intro heq
        apply hzw
        exact Subtype.ext (Subtype.ext heq)
      have hsep' := hsep z.1.1 z.1.property w.1.1 w.1.property hzw'
      have hdz : dist z.1.1 (a z : X) < δ / 4 := by
        simpa [dist_eq_norm] using ha z
      have hwd : dist (a w : X) w.1.1 < δ / 4 := by
        rw [dist_comm, dist_eq_norm]
        exact ha w
      have htri : dist z.1.1 w.1.1 ≤ dist z.1.1 (a z : X) +
          dist (a z : X) (a w : X) + dist (a w : X) w.1.1 := by
        calc
          dist z.1.1 w.1.1 ≤ dist z.1.1 (a z : X) + dist (a z : X) w.1.1 :=
            dist_triangle _ _ _
          _ ≤ dist z.1.1 (a z : X) +
              (dist (a z : X) (a w : X) + dist (a w : X) w.1.1) := by
                gcongr
                exact dist_triangle _ _ _
          _ = _ := by ring
      linarith [hsep', hdz, hwd, htri]
    letI : MeasurableSpace V.1 := borel V.1
    letI : BorelSpace V.1 := ⟨rfl⟩
    by_cases htriv : Nontrivial V.1
    · letI : Nontrivial V.1 := htriv
      let S : Finset V.1 := T.attach.attach.image a
      have ha_inj : Function.Injective a := by
        intro z w heq
        by_contra hne
        have hsepzw := hasep z w hne
        rw [heq] at hsepzw
        have hzero : dist (a w : X) (a w : X) = 0 := dist_self _
        rw [hzero] at hsepzw
        linarith [hδ]
      have hScard : S.card = T.card := by
        change (T.attach.attach.image a).card = T.card
        rw [Finset.card_image_of_injective _ ha_inj]
        simp
      have hboundS : ∀ v ∈ S, dist v 0 ≤ R + δ / 4 := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨z, hz, rfl⟩
        simpa [dist_zero_right] using hnorma z
      have hsepS : Set.Pairwise (↑S : Set V.1) fun v w => δ / 2 < dist v w := by
        intro v hv w hw hvw
        rcases Finset.mem_image.mp hv with ⟨z, hz, rfl⟩
        rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
        exact hasep z u (by
          intro hzu
          apply hvw
          exact congrArg a hzu)
      have hcardBound : (T.card : ℝ) ≤
          (1 + 2 * (R + δ / 4) / (δ / 2)) ^ Module.finrank ℝ V.1 := by
        rw [← hScard]
        exact HaarQuarter.TheoremF.FiniteDimensionalCovering.card_le_covering_bound
          S (by positivity) (by positivity) hboundS hsepS
      have hcardBound' : (T.card : ℝ) ≤ b ^ m := by
        calc
          _ ≤ b ^ Module.finrank ℝ V.1 :=
            le_trans hcardBound (pow_le_pow_left₀ (by positivity) hratio' _)
          _ ≤ b ^ m := pow_le_pow_right₀ hb hdim
      linarith
    · have htriv : Subsingleton V.1 := not_nontrivial_iff_subsingleton.mp htriv
      have hcardAttach : 1 < T.attach.attach.card := by simpa using hcardgtoneNat
      obtain ⟨z, hz, w, hw, hzw⟩ := Finset.one_lt_card.mp hcardAttach
      have hposSep := hasep z w hzw
      have hzEq : a z = a w := Subsingleton.elim _ _
      rw [hzEq] at hposSep
      have hzero : dist (a w : X) (a w : X) = 0 := dist_self _
      rw [hzero] at hposSep
      linarith [hδ]
  unfold kolmogorovWidth
  apply le_iInf
  intro V
  exact le_of_not_gt (hsmall V)

end HaarQuarter.TheoremF.PackingWidth
