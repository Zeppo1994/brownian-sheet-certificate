import BrownianSharp.Alignment

/-!
# The two-law gain reduction

Source: unrestricted quarter-gain proof, Section 6.
The signed score identities, refusal/error bounds, and aligned-mass transport
are explicit hypotheses. No stopped-law estimate or physical Haar bridge is
introduced as an axiom. The final threshold lemma preserves uniformity over
the entire family of inputs at each depth.
-/

open Filter
open scoped Topology

namespace HaarQuarter

theorem twoLaw_score_bound {ι : Type*} [Fintype ι]
    (Pplus Pminus : PositiveLaw ι) (Q diag off mask : ι → ℝ) (ρ c₀ : ℝ)
    (hQ : ∀ x, |Q x| ≤ 1)
    (hplus : mean Pplus Q - c₀ =
      ρ * mean Pplus diag + mean Pplus off - mean Pplus mask)
    (hminus : mean Pminus Q - c₀ =
      -ρ * mean Pminus diag - mean Pminus off + mean Pminus mask) :
    ρ * (mean Pplus diag + mean Pminus diag) ≤
      2 + |mean Pplus off| + |mean Pminus off| +
        |mean Pplus mask| + |mean Pminus mask| := by
  have hp := (abs_le.mp (abs_mean_le_one Pplus Q hQ)).2
  have hn := (abs_le.mp (abs_mean_le_one Pminus Q hQ)).1
  have hop := neg_le_abs (mean Pplus off)
  have hon := neg_le_abs (mean Pminus off)
  have hmp := le_abs_self (mean Pplus mask)
  have hmn := le_abs_self (mean Pminus mask)
  nlinarith

/-- The normalized critical mass is bounded, with transport needed only on
the branch `ρ m ≥ 1`, exactly as in the source proof. -/
theorem twoLaw_normalized_mass_bound {ι : Type*} [Fintype ι]
    (Pplus Pminus : PositiveLaw ι) (Q diag off mask : ι → ℝ)
    (ρ c₀ m ε r : ℝ) (hρ : 0 ≤ ρ) (hm : 0 ≤ m) (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hQ : ∀ x, |Q x| ≤ 1)
    (hplus : mean Pplus Q - c₀ =
      ρ * mean Pplus diag + mean Pplus off - mean Pplus mask)
    (hminus : mean Pminus Q - c₀ =
      -ρ * mean Pminus diag - mean Pminus off + mean Pminus mask)
    (herrorPlus : |mean Pplus off| + |mean Pplus mask| ≤ r)
    (herrorMinus : |mean Pminus off| + |mean Pminus mask| ≤ r)
    (htransportPlus : 1 ≤ ρ * m → (1 - ε) * ρ * m ≤ ρ * mean Pplus diag)
    (htransportMinus : 1 ≤ ρ * m → (1 - ε) * ρ * m ≤ ρ * mean Pminus diag) :
    (1 - ε) * ρ * m ≤ 1 + r := by
  by_cases hlarge : 1 ≤ ρ * m
  · have hs := twoLaw_score_bound Pplus Pminus Q diag off mask ρ c₀ hQ hplus hminus
    have htp := htransportPlus hlarge
    have htn := htransportMinus hlarge
    nlinarith
  · have hsmall : ρ * m < 1 := lt_of_not_ge hlarge
    have hnonneg : 0 ≤ ρ * m := mul_nonneg hρ hm
    nlinarith

/-- Restore the original mass `M = K m` after normalizing the query by `K`. -/
theorem gain_from_normalized_mass_bound (ρ M K m ε r : ℝ)
    (hK : 0 < K) (hr : 0 ≤ r) (hM : M = K * m)
    (hbound : (1 - ε) * ρ * m ≤ 1 + r) :
    ((1 - ε) / (1 + r)) * ρ * M ≤ K := by
  have hden : 0 < 1 + r := by linarith
  have hscaled : ((1 - ε) / (1 + r)) * ρ * m ≤ 1 := by
    have hidentity : ((1 - ε) / (1 + r)) * ρ * m =
        ((1 - ε) * ρ * m) / (1 + r) := by ring
    rw [hidentity]
    exact (div_le_iff₀ hden).mpr (by simpa using hbound)
  calc
    _ = (((1 - ε) / (1 + r)) * ρ * m) * K := by rw [hM]; ring
    _ ≤ 1 * K := mul_le_mul_of_nonneg_right hscaled (le_of_lt hK)
    _ = K := one_mul K

theorem twoLaw_gain_reduction {ι : Type*} [Fintype ι]
    (Pplus Pminus : PositiveLaw ι) (Q diag off mask : ι → ℝ)
    (ρ c₀ M K m ε r : ℝ) (hρ : 0 ≤ ρ) (hK : 0 < K) (hm : 0 ≤ m)
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hM : M = K * m)
    (hQ : ∀ x, |Q x| ≤ 1)
    (hplus : mean Pplus Q - c₀ =
      ρ * mean Pplus diag + mean Pplus off - mean Pplus mask)
    (hminus : mean Pminus Q - c₀ =
      -ρ * mean Pminus diag - mean Pminus off + mean Pminus mask)
    (herrorPlus : |mean Pplus off| + |mean Pplus mask| ≤ r)
    (herrorMinus : |mean Pminus off| + |mean Pminus mask| ≤ r)
    (htransportPlus : 1 ≤ ρ * m → (1 - ε) * ρ * m ≤ ρ * mean Pplus diag)
    (htransportMinus : 1 ≤ ρ * m → (1 - ε) * ρ * m ≤ ρ * mean Pminus diag) :
    ((1 - ε) / (1 + r)) * ρ * M ≤ K := by
  apply gain_from_normalized_mass_bound ρ M K m ε r hK hr hM
  exact twoLaw_normalized_mass_bound Pplus Pminus Q diag off mask ρ c₀ m ε r
    hρ hm hε hr hQ hplus hminus herrorPlus herrorMinus htransportPlus htransportMinus

theorem gain_prefactor_tendsto_one (ε r : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun N => (1 - ε N) / (1 + r N)) atTop (𝓝 1) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hnum := hone.sub hε
  have hden := hone.add hr
  have h := hnum.div hden (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hf : ((fun N => 1 - ε N) / (fun N => 1 + r N)) =
      (fun N => (1 - ε N) / (1 + r N)) := by
    funext N
    exact Pi.div_apply _ _ _
  rw [hf] at h
  simpa using h

theorem gain_prefactor_eventually_ge (ε r : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 0))
    (c : ℝ) (hc : c < 1) :
    ∀ᶠ N in atTop, c ≤ (1 - ε N) / (1 + r N) := by
  have h := (gain_prefactor_tendsto_one ε r hε hr).eventually (Ioi_mem_nhds hc)
  exact h.mono (fun N hN => le_of_lt hN)

/-- A single depth threshold works for every input, not a separate threshold
for each array or drift. `X N` is the entire input family at depth `N`. -/
theorem uniform_gain_from_prefactor {X : ℕ → Type*} (ρ ε r : ℕ → ℝ)
    (M K : ∀ N, X N → ℝ) (hρ : ∀ N, 0 ≤ ρ N) (hM : ∀ N x, 0 ≤ M N x)
    (hε : Tendsto ε atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop, ∀ x : X N,
      ((1 - ε N) / (1 + r N)) * ρ N * M N x ≤ K N x)
    (c : ℝ) (hc : c < 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : X N, c * ρ N * M N x ≤ K N x := by
  have hboth := (gain_prefactor_eventually_ge ε r hε hr c hc).and hbound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hboth
  refine ⟨N₀, ?_⟩
  intro N hN x
  have h := hN₀ N hN
  calc
    _ ≤ ((1 - ε N) / (1 + r N)) * ρ N * M N x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h.1 (hρ N)) (hM N x)
    _ ≤ K N x := h.2 x

end HaarQuarter
