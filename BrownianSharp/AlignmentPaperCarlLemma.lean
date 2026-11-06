import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentPaperPeriodic

/-!
# Lemma 3.1 (Carl): two-sided entropy and width rates for every logarithmic exponent

For a bounded set `K`, `α > 0` and an arbitrary real `β`, an eventual width upper bound
`d_k ≲ k^{-α}(log k)^β` and an eventual entropy lower bound `e_k ≳ k^{-α}(log k)^β` force
`d_k ≍ e_k ≍ k^{-α}(log k)^β`.  The proof follows the manuscript: the dyadic Carl cover
replaces the maximal form of Carl's inequality, and `2^{Aj}·2^{-αj}j^β` is eventually
increasing in `j` for every real `β`.
-/

noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperCarlLemma
open BrownianSharp.AlignmentIsometricEntropy HaarQuarter.TheoremD HaarQuarter.TheoremD.Width

/-- The rate `x^{-s}(log x)^a` on the reals; `logarithmicIndexRate s a n = ρ s a n`. -/
def ρ (s a x : ℝ) : ℝ := x ^ (-s) * Real.log x ^ a

private theorem tpow {t : ℝ} (b : ℝ) (h1 : 1 ≤ t) (h2 : t ≤ 2) : t ^ b ≤ 2 ^ |b| := by
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]; exact Real.rpow_le_rpow (by linarith) h2 hb
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 hb).trans (Real.one_le_rpow (by norm_num) (abs_nonneg b))

private theorem rho_comp {s a x y : ℝ} (hs : 0 ≤ s) (hx : 1 < x) (hxy : x ≤ y) (hy : y ≤ x ^ 2) :
    ρ s a x ≤ 2 ^ |a| * (y / x) ^ s * ρ s a y ∧ ρ s a y ≤ 2 ^ |a| * ρ s a x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hly : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hly2 : Real.log y ≤ 2 * Real.log x := by
    have := Real.log_le_log hy0 hy
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have ht : 1 ≤ Real.log y / Real.log x := (one_le_div hlx).2 hly
  have ht2 : Real.log y / Real.log x ≤ 2 := (div_le_iff₀ hlx).2 (by linarith)
  set t := Real.log y / Real.log x with htdef
  have hyl : Real.log y ^ a = t ^ a * Real.log x ^ a := by
    rw [← Real.mul_rpow (by linarith) hlx.le, htdef, div_mul_cancel₀ _ hlx.ne']
  have htp : 0 < t ^ a := Real.rpow_pos_of_pos (by linarith) _
  have hxl : Real.log x ^ a = t ^ (-a) * Real.log y ^ a := by
    rw [Real.rpow_neg (by linarith), hyl]; field_simp
  have hA : Real.log y ^ a ≤ 2 ^ |a| * Real.log x ^ a := by
    rw [hyl]; exact mul_le_mul_of_nonneg_right (tpow a ht ht2) (Real.rpow_nonneg hlx.le _)
  have hB : Real.log x ^ a ≤ 2 ^ |a| * Real.log y ^ a := by
    have := tpow (-a) ht ht2
    rw [abs_neg] at this
    rw [hxl]; exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (by linarith) _)
  have hxs : x ^ (-s) = (y / x) ^ s * y ^ (-s) := by
    rw [Real.div_rpow hy0.le hx0.le, Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]
    field_simp [(Real.rpow_pos_of_pos hy0 s).ne']
  have hyx : y ^ (-s) ≤ x ^ (-s) := Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hxs0 : 0 ≤ x ^ (-s) := Real.rpow_nonneg hx0.le _
  refine ⟨?_, ?_⟩
  · unfold ρ
    calc x ^ (-s) * Real.log x ^ a ≤ ((y / x) ^ s * y ^ (-s)) * (2 ^ |a| * Real.log y ^ a) := by
          rw [← hxs]; exact mul_le_mul_of_nonneg_left hB hxs0
      _ = _ := by ring
  · unfold ρ
    calc y ^ (-s) * Real.log y ^ a ≤ x ^ (-s) * (2 ^ |a| * Real.log x ^ a) :=
          mul_le_mul hyx hA (Real.rpow_nonneg (by linarith) _) hxs0
      _ = _ := by ring

/-- The weighted dyadic rate `2^{Aj} ρ(2^j)`. -/
def G (s a : ℝ) (A j : ℕ) : ℝ := (2 : ℝ) ^ (A * j) * ρ s a ((2 : ℝ) ^ j)

private theorem G_eq {s a : ℝ} {A j : ℕ} (hj : 1 ≤ j) :
    G s a A j = Real.exp (((A : ℝ) - s) * Real.log 2 * j +
      a * (Real.log j + Real.log (Real.log 2))) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have h2 : (2 : ℝ) ^ (A * j) = Real.exp (((A * j : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hlog : Real.log ((2 : ℝ) ^ j) = j * Real.log 2 := by rw [Real.log_pow]
  unfold G ρ
  rw [h2, Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos
    (by rw [hlog]; exact mul_pos hj0 hL), hlog, Real.log_mul hj0.ne' hL.ne', ← Real.exp_add, ← Real.exp_add]
  congr 1; push_cast; ring

private theorem G_mono (s a : ℝ) {A : ℕ} (hsA : s < A) :
    ∃ i₀ : ℕ, 1 ≤ i₀ ∧ ∀ i j : ℕ, i₀ ≤ i → i ≤ j → G s a A i ≤ G s a A j := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < ((A : ℝ) - s) * Real.log 2 := mul_pos (by linarith) hL
  obtain ⟨i₀, hi₀⟩ := exists_nat_ge (|a| / (((A : ℝ) - s) * Real.log 2))
  refine ⟨max i₀ 1, le_max_right _ _, fun i j hi hij => ?_⟩
  have hi1 : 1 ≤ i := (le_max_right _ _).trans hi
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
  have hiR : |a| / (((A : ℝ) - s) * Real.log 2) ≤ i :=
    hi₀.trans (by exact_mod_cast (le_max_left _ _).trans hi)
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  rw [G_eq hi1, G_eq (hi1.trans hij), Real.exp_le_exp]
  have hlog1 : Real.log i ≤ Real.log j := Real.log_le_log hi0 hijR
  have hlog2 : Real.log j - Real.log i ≤ ((j : ℝ) - i) / i := by
    rw [← Real.log_div (by linarith) hi0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0:ℝ) < j) hi0)
    rwa [div_sub_one hi0.ne'] at this
  have h3 : |a| ≤ i * (((A : ℝ) - s) * Real.log 2) := (div_le_iff₀ hδ).1 hiR
  have h4 : -|a| * (Real.log j - Real.log i) ≤ a * (Real.log j - Real.log i) :=
    mul_le_mul_of_nonneg_right (neg_abs_le a) (by linarith)
  have h5 : |a| * (Real.log j - Real.log i) ≤ ((A : ℝ) - s) * Real.log 2 * ((j : ℝ) - i) := by
    calc |a| * (Real.log j - Real.log i) ≤ |a| * (((j : ℝ) - i) / i) :=
          mul_le_mul_of_nonneg_left hlog2 (abs_nonneg a)
      _ = |a| / i * ((j : ℝ) - i) := by ring
      _ ≤ ((A : ℝ) - s) * Real.log 2 * ((j : ℝ) - i) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [div_le_iff₀ hi0]; linarith
  nlinarith

section Carl
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Real-valued Kolmogorov width (finite for bounded sets). -/
private def W (K : Set X) (k : ℕ) : ℝ := (kolmogorovWidth K k).toReal

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
private theorem W_anti {K : Set X} {R : ℝ} (hR : 0 ≤ R) (hzero : kolmogorovWidth K 0 ≤ ENNReal.ofReal R)
    {m n : ℕ} (h : m ≤ n) : W K n ≤ W K m ∧ W K m ≤ R :=
  ⟨ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((kolmogorovWidth_antitone K (Nat.zero_le m)).trans hzero)) (kolmogorovWidth_antitone K h),
   ENNReal.toReal_le_of_le_ofReal hR ((kolmogorovWidth_antitone K (Nat.zero_le m)).trans hzero)⟩

/-- Dyadic Carl cover: weighted dyadic width bounds give an entropy bound. -/
private theorem carl_dyadic (K : Set X) (A L : ℕ) {B : ℝ} (hB : 0 < B)
    (hfin : kolmogorovWidth K 0 ≠ ⊤)
    (hw : ∀ j ≤ L, W K (2 ^ j - 1) * 2 ^ (A * j) ≤ B) :
    entropyNumber (96 * (A + 1) * 2 ^ L + 1) K ≤
      ENNReal.ofReal (((2 : ℝ) ^ (A + 1) + 2) * B / 2 ^ (A * L)) := by
  obtain ⟨P, _, hcover⟩ := AlignmentPeriodicWidth.entropy_cover_of_Q_dyadic_width_bound
    K A (A + 1) L (by omega) hB (fun j => by
      refine (ENNReal.le_ofReal_iff_toReal_le (ne_top_of_le_ne_top hfin
        (kolmogorovWidth_antitone K (Nat.zero_le _))) (by positivity)).2 ?_
      rw [le_div_iff₀ (by positivity)]
      exact hw j (by omega))
  exact hcover

private theorem rho_nonneg {s a : ℝ} {x : ℝ} (hx : 1 < x) : 0 ≤ ρ s a x :=
  mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (Real.log_nonneg hx.le) _)

private theorem G_pos {s a : ℝ} {A j : ℕ} (hj : 1 ≤ j) : 0 < G s a A j := by
  rw [G_eq hj]; exact Real.exp_pos _

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Under the eventual width upper bound, the weighted dyadic widths are dominated by `G L`. -/
private theorem envelope {K : Set X} {s a R C : ℝ} {A n₀ : ℕ} (hs : 0 < s) (hsA : s < A)
    (hR : 0 ≤ R) (hC : 0 < C) (hzero : kolmogorovWidth K 0 ≤ ENNReal.ofReal R)
    (hU : ∀ n, n₀ ≤ n → kolmogorovWidth K n ≤ ENNReal.ofReal (C * ρ s a n)) :
    ∃ C₅ : ℝ, 0 < C₅ ∧ ∃ j₂ : ℕ, 1 ≤ j₂ ∧ ∀ L, j₂ ≤ L → ∀ j ≤ L,
      W K (2 ^ j - 1) * 2 ^ (A * j) ≤ C₅ * G s a A L := by
  obtain ⟨i₀, hi₀, hmono⟩ := G_mono s a hsA
  let j₂ := max (n₀ + 2) i₀
  have hj₂ : 1 ≤ j₂ := by omega
  let C₃ := C * (2 ^ |a| * 2 ^ s)
  let M := 2 ^ (A * j₂) * R
  have hγ := G_pos (s := s) (a := a) (A := A) hj₂
  have hC₃ : 0 < C₃ := by positivity
  have hM : 0 ≤ M / G s a A j₂ := by positivity
  refine ⟨C₃ + M / G s a A j₂, by positivity, j₂, hj₂, fun L hL j hj => ?_⟩
  have hGL : G s a A j₂ ≤ G s a A L := hmono _ _ (le_max_right _ _) hL
  have hGL0 : 0 < G s a A L := hγ.trans_le hGL
  by_cases hjj : j₂ ≤ j
  · have hj2 : n₀ + 2 ≤ j := (le_max_left _ _).trans hjj
    have hpow : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hn₀ : n₀ ≤ 2 ^ j - 1 := by generalize 2 ^ j = P at hpow; omega
    have hx : (1 : ℝ) < ((2 ^ j - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by generalize 2 ^ j = P at h4; omega : 1 < 2 ^ j - 1)
    have hcast : ((2 ^ j - 1 : ℕ) : ℝ) = 2 ^ j - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]; simp
    have h2j : (3 : ℝ) ≤ 2 ^ j := by exact_mod_cast (by omega : 3 ≤ 2 ^ j)
    have hW : W K (2 ^ j - 1) ≤ C * ρ s a ((2 : ℝ) ^ j - 1) := by
      rw [← hcast]
      exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC.le (rho_nonneg hx)) (hU _ hn₀)
    rw [hcast] at hx
    obtain ⟨hc1, _⟩ := rho_comp (s := s) (a := a) hs.le hx (by linarith)
      (by nlinarith : (2 : ℝ) ^ j ≤ ((2 : ℝ) ^ j - 1) ^ 2)
    have hratio : (2 ^ j / (2 ^ j - 1) : ℝ) ^ s ≤ 2 ^ s :=
      Real.rpow_le_rpow (by positivity) ((div_le_iff₀ (by linarith)).2 (by linarith)) hs.le
    have hρy : 0 ≤ ρ s a ((2 : ℝ) ^ j) := rho_nonneg (by linarith)
    have hGj : G s a A j ≤ G s a A L := hmono _ _ ((le_max_right _ _).trans hjj) hj
    have hin : 2 ^ |a| * (2 ^ j / (2 ^ j - 1) : ℝ) ^ s * ρ s a ((2 : ℝ) ^ j) ≤
        2 ^ |a| * 2 ^ s * ρ s a ((2 : ℝ) ^ j) := by gcongr
    calc W K (2 ^ j - 1) * 2 ^ (A * j)
        ≤ (C * (2 ^ |a| * 2 ^ s * ρ s a ((2 : ℝ) ^ j))) * 2 ^ (A * j) :=
          mul_le_mul_of_nonneg_right
            (hW.trans (mul_le_mul_of_nonneg_left (hc1.trans hin) hC.le)) (by positivity)
      _ = C₃ * G s a A j := by unfold G; ring
      _ ≤ C₃ * G s a A L := mul_le_mul_of_nonneg_left hGj hC₃.le
      _ ≤ _ := by nlinarith [mul_nonneg hM hGL0.le]
  · have hjlt : j < j₂ := not_le.1 hjj
    have h1 : W K (2 ^ j - 1) ≤ R := (W_anti hR hzero (Nat.zero_le (2 ^ j - 1))).1.trans
      (W_anti hR hzero (Nat.zero_le (2 ^ j - 1))).2
    have h2 : (2 : ℝ) ^ (A * j) ≤ 2 ^ (A * j₂) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hjlt.le)
    calc W K (2 ^ j - 1) * 2 ^ (A * j) ≤ R * 2 ^ (A * j₂) :=
          mul_le_mul h1 h2 (by positivity) hR
      _ = M / G s a A j₂ * G s a A j₂ := by
          rw [div_mul_cancel₀ _ hγ.ne']; ring
      _ ≤ M / G s a A j₂ * G s a A L := mul_le_mul_of_nonneg_left hGL hM
      _ ≤ _ := by nlinarith [mul_pos hC₃ hGL0]

/-- Entropy upper rate at all large indices (manuscript: `e_n ≲ η_n`). -/
private theorem entropy_upper {K : Set X} {s a R C : ℝ} {A n₀ : ℕ} (hs : 0 < s) (hsA : s < A)
    (hR : 0 ≤ R) (hC : 0 < C) (hzero : kolmogorovWidth K 0 ≤ ENNReal.ofReal R)
    (hU : ∀ n, n₀ ≤ n → kolmogorovWidth K n ≤ ENNReal.ofReal (C * ρ s a n)) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      entropyNumber n K ≤ ENNReal.ofReal (C' * ρ s a n) := by
  obtain ⟨C₅, hC₅, j₂, hj₂, henv⟩ := envelope hs hsA hR hC hzero hU
  let D := 96 * (A + 1)
  let J : ℝ := (2 : ℝ) ^ (A + 1) + 2
  have hD : 1 ≤ D := by omega
  have hdy : ∀ L, j₂ ≤ L → entropyNumber (D * 2 ^ L + 1) K ≤
      ENNReal.ofReal (J * C₅ * ρ s a ((2 : ℝ) ^ L)) := fun L hL => by
    have hG := G_pos (s := s) (a := a) (A := A) (hj₂.trans hL)
    refine (carl_dyadic K A L (mul_pos hC₅ hG) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hzero)
      (henv L hL)).trans (le_of_eq ?_)
    unfold G; congr 1; field_simp; exact mul_comm _ _
  refine ⟨J * C₅ * (2 ^ |a| * (2 * D : ℝ) ^ s), by positivity, D * 2 ^ (max j₂ (2 * D)) + 1,
    fun n hn => ?_⟩
  have hL₁ : max j₂ (2 * D) < 2 ^ max j₂ (2 * D) := Nat.lt_two_pow_self
  let t := (n - 1) / D
  have ht : 2 ^ max j₂ (2 * D) ≤ t := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; omega)
  let L := Nat.log 2 t
  have hL : max j₂ (2 * D) ≤ L := Nat.le_log_of_pow_le one_lt_two ht
  have hLt : 2 ^ L ≤ t := Nat.pow_log_le_self 2 (by omega)
  have ht2 : t < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self one_lt_two t
  have hn1 : D * 2 ^ L ≤ n - 1 := (Nat.mul_le_mul_left D hLt).trans (Nat.mul_div_le _ _)
  have hn2 : n - 1 < D * 2 ^ (L + 1) :=
    (Nat.lt_mul_div_succ (n - 1) (by omega)).trans_le (Nat.mul_le_mul_left D ht2)
  have h2D : 2 * D ≤ 2 ^ L := by
    have : L < 2 ^ L := Nat.lt_two_pow_self
    omega
  have hLj : j₂ ≤ L := (le_max_left _ _).trans hL
  have hx : (1 : ℝ) < (2 : ℝ) ^ L := by
    have : (4 : ℝ) ≤ 2 ^ L := by exact_mod_cast (by omega : 4 ≤ 2 ^ L)
    linarith
  have hxy : (2 : ℝ) ^ L ≤ n := by
    exact_mod_cast (by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ n)] : 2 ^ L ≤ n)
  have hyx : (n : ℝ) ≤ ((2 : ℝ) ^ L) ^ 2 := by
    have h : n ≤ (2 ^ L) ^ 2 := by
      have : n ≤ D * 2 ^ (L + 1) := by omega
      calc n ≤ 2 * D * 2 ^ L := by rw [pow_succ] at this; nlinarith
        _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ h2D
        _ = _ := (sq _).symm
    exact_mod_cast h
  obtain ⟨h1, _⟩ := rho_comp (s := s) (a := a) hs.le hx hxy hyx
  have hnx : (n : ℝ) / 2 ^ L ≤ 2 * D := by
    rw [div_le_iff₀ (by positivity)]
    have : n ≤ 2 * D * 2 ^ L := by
      have : n ≤ D * 2 ^ (L + 1) := by omega
      rw [pow_succ] at this; nlinarith
    exact_mod_cast this
  have hρ := rho_nonneg (s := s) (a := a) (hx.trans_le hxy)
  have hrat : ((n : ℝ) / 2 ^ L) ^ s ≤ (2 * D : ℝ) ^ s :=
    Real.rpow_le_rpow (by positivity) hnx hs.le
  refine (entropyNumber_antitone K (by omega : D * 2 ^ L + 1 ≤ n)).trans
    ((hdy L hLj).trans (ENNReal.ofReal_le_ofReal ?_))
  calc J * C₅ * ρ s a ((2 : ℝ) ^ L) ≤ J * C₅ * (2 ^ |a| * ((n : ℝ) / 2 ^ L) ^ s * ρ s a n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := by
      have : 2 ^ |a| * ((n : ℝ) / 2 ^ L) ^ s * ρ s a n ≤
          2 ^ |a| * (2 * D : ℝ) ^ s * ρ s a n := by gcongr
      nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ J * C₅ by positivity)]

end Carl

private theorem real_core {c J C₅ P t d ls lA ω Rm Ry Rl : ℝ} (hc : 0 < c) (hJ : 0 < J)
    (hC : 0 < C₅) (hP : 0 < P) (hd : 0 < d) (hls : 0 < ls) (hlA : 0 < lA) (hRm : 0 ≤ Rm)
    (E1 : c * Ry ≤ J * ω + J * C₅ * Rl / lA) (E2 : Rl ≤ P * t * Rm)
    (E3 : Rm ≤ P * d * ls * Ry) (hlam : 2 * P * P * t * d * J * C₅ / c * ls ≤ lA) :
    c / (2 * P * d * ls * J) * Rm ≤ ω := by
  have hQ : 0 < P * d * ls := by positivity
  have key : P * d * ls * J * C₅ * (P * t) ≤ c / 2 * lA := by
    have h : 2 * P * P * t * d * J * C₅ * ls / c ≤ lA := by rwa [div_mul_eq_mul_div] at hlam
    rw [div_le_iff₀ hc] at h; nlinarith
  have h2 : P * d * ls * J * C₅ * Rl / lA ≤ c / 2 * Rm := by
    rw [div_le_iff₀ hlA]
    calc P * d * ls * J * C₅ * Rl ≤ P * d * ls * J * C₅ * (P * t * Rm) :=
          mul_le_mul_of_nonneg_left E2 (by positivity)
      _ = P * d * ls * J * C₅ * (P * t) * Rm := by ring
      _ ≤ c / 2 * lA * Rm := mul_le_mul_of_nonneg_right (by linarith) hRm
      _ = _ := by ring
  have h3 : c * Rm ≤ P * d * ls * J * ω + c / 2 * Rm := by
    calc c * Rm ≤ c * (P * d * ls * Ry) := mul_le_mul_of_nonneg_left E3 hc.le
      _ = P * d * ls * (c * Ry) := by ring
      _ ≤ P * d * ls * (J * ω + J * C₅ * Rl / lA) := mul_le_mul_of_nonneg_left E1 hQ.le
      _ = P * d * ls * J * ω + P * d * ls * J * C₅ * Rl / lA := by ring
      _ ≤ _ := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

section Carl2
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Width lower rate (manuscript (3.6)-(3.8)): `d_m ≳ η_m` for large `m`. -/
private theorem width_lower {K : Set X} {s a R C c : ℝ} {A n₀ n₁ : ℕ} (hs : 0 < s)
    (hsA : s < A) (hR : 0 ≤ R) (hC : 0 < C) (hc : 0 < c)
    (hzero : kolmogorovWidth K 0 ≤ ENNReal.ofReal R)
    (hU : ∀ n, n₀ ≤ n → kolmogorovWidth K n ≤ ENNReal.ofReal (C * ρ s a n))
    (hE : ∀ n, n₁ ≤ n → ENNReal.ofReal (c * ρ s a n) ≤ entropyNumber n K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℕ, ∀ m, M ≤ m →
      ENNReal.ofReal (ε * ρ s a m) ≤ kolmogorovWidth K m := by
  obtain ⟨C₅, hC₅, j₂, hj₂, henv⟩ := envelope hs hsA hR hC hzero hU
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = 96 * (A + 1) := ⟨_, rfl⟩
  let J : ℝ := (2 : ℝ) ^ (A + 1) + 2
  let P : ℝ := 2 ^ |a|
  let T : ℝ := 2 * P * P * 2 ^ s * (3 * (D : ℝ)) ^ s * J * C₅ / c
  have hD : 1 ≤ D := by omega
  have hJ : 0 < J := by positivity
  have hP : 0 < P := by positivity
  have hδ : 0 < (A : ℝ) - s := by linarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop T)
  let lam : ℕ := max 1 ⌈x₀⌉₊
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlam0 : (0 : ℝ) < lam := by exact_mod_cast hlam1
  have hlamT : T * (lam : ℝ) ^ s ≤ (lam : ℝ) ^ A := by
    have h := hx₀ lam ((Nat.le_ceil x₀).trans (by exact_mod_cast le_max_right _ _))
    rw [Real.rpow_sub hlam0, Real.rpow_natCast, le_div_iff₀ (by positivity)] at h
    exact h
  let ε : ℝ := c / (2 * P * (3 * (D : ℝ)) ^ s * (lam : ℝ) ^ s * J)
  refine ⟨ε, by positivity, max (max (2 ^ j₂) n₁) (max (3 * D * lam) 2), fun m hm => ?_⟩
  have hmj : 2 ^ j₂ ≤ m := ((le_max_left _ _).trans (le_max_left _ _)).trans hm
  have hmn₁ : n₁ ≤ m := ((le_max_right _ _).trans (le_max_left _ _)).trans hm
  have hm3 : 3 * D * lam ≤ m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hm2 : 2 ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hfin : kolmogorovWidth K 0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hzero
  -- dyadic scales
  let l := Nat.log 2 m
  have hl1 : 2 ^ l ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hl2 : m < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self one_lt_two m
  have hlj : j₂ ≤ l := Nat.le_log_of_pow_le one_lt_two hmj
  let L' := Nat.log 2 (lam * m)
  have hL1 : 2 ^ L' ≤ lam * m := Nat.pow_log_le_self 2 (by positivity)
  have hL2 : lam * m < 2 ^ (L' + 1) := Nat.lt_pow_succ_log_self one_lt_two _
  let L := L' + 1
  have hlm : m ≤ lam * m := Nat.le_mul_of_pos_left m hlam1
  have h2L : 2 ^ L ≤ 2 * (lam * m) := by
    have : 2 ^ L = 2 * 2 ^ L' := by dsimp [L]; ring
    omega
  -- Carl cover
  have hG := G_pos (s := s) (a := a) (A := A) (hj₂.trans hlj)
  have hω0 : 0 ≤ W K m := ENNReal.toReal_nonneg
  have hB : 0 < W K m * 2 ^ (A * L) + C₅ * G s a A l := by positivity
  have hw : ∀ j ≤ L, W K (2 ^ j - 1) * 2 ^ (A * j) ≤ W K m * 2 ^ (A * L) + C₅ * G s a A l := by
    intro j hj
    by_cases hjl : j ≤ l
    · exact (henv l hlj j hjl).trans (by nlinarith [mul_nonneg hω0 (show (0 : ℝ) ≤ 2 ^ (A * L) by positivity)])
    · have hlj' : l + 1 ≤ j := by omega
      have hmj' : m ≤ 2 ^ j - 1 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hlj'
        generalize 2 ^ j = P at this ⊢; omega
      have h1 := (W_anti hR hzero hmj').1
      have h2 : (2 : ℝ) ^ (A * j) ≤ 2 ^ (A * L) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hj)
      nlinarith [mul_le_mul h1 h2 (by positivity) hω0, mul_pos hC₅ hG]
  have hcar := carl_dyadic K A L hB hfin hw
  rw [← hDdef] at hcar
  -- entropy lower bound at the Carl index
  have hN : lam * m < 2 ^ L := hL2
  let n' := D * 2 ^ L + 1
  have hn'1 : n₁ ≤ n' := by
    have : 2 ^ L ≤ D * 2 ^ L := Nat.le_mul_of_pos_left _ (by omega)
    show n₁ ≤ D * 2 ^ L + 1
    omega
  have hE' := (hE n' hn'1).trans hcar
  have hpos : 0 ≤ ((2 : ℝ) ^ (A + 1) + 2) * (W K m * 2 ^ (A * L) + C₅ * G s a A l) / 2 ^ (A * L) :=
    by positivity
  rw [ENNReal.ofReal_le_ofReal_iff hpos] at hE'
  have h2l : (2 : ℝ) ≤ 2 ^ l :=
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) (by omega)
  have hρ2l : (1 : ℝ) < 2 ^ l := by linarith
  have hl1R : (2 : ℝ) ^ l ≤ m := by exact_mod_cast hl1
  have hl2R : (m : ℝ) < 2 * 2 ^ l := by
    exact_mod_cast (by rw [pow_succ] at hl2; omega : m < 2 * 2 ^ l)
  have hRl : 0 ≤ ρ s a ((2 : ℝ) ^ l) := rho_nonneg hρ2l
  -- E1
  have E1 : c * ρ s a n' ≤ J * W K m + J * C₅ * ρ s a ((2 : ℝ) ^ l) / (lam : ℝ) ^ A := by
    refine hE'.trans ?_
    have hlamL : (2 : ℝ) ^ (A * l) * (lam : ℝ) ^ A ≤ 2 ^ (A * L) := by
      rw [mul_comm A l, mul_comm A L, pow_mul, pow_mul, ← mul_pow, mul_comm]
      apply pow_le_pow_left₀ (by positivity)
      have : ((lam : ℝ) * m) < 2 ^ L := by exact_mod_cast hN
      nlinarith
    have hGl : G s a A l / 2 ^ (A * L) ≤ ρ s a ((2 : ℝ) ^ l) / (lam : ℝ) ^ A := by
      unfold G
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hlamL hRl]
    calc ((2 : ℝ) ^ (A + 1) + 2) * (W K m * 2 ^ (A * L) + C₅ * G s a A l) / 2 ^ (A * L)
        = J * W K m + J * C₅ * (G s a A l / 2 ^ (A * L)) := by field_simp; rfl
      _ ≤ _ := by
        rw [mul_div_assoc]
        gcongr
  -- E2
  have E2 : ρ s a ((2 : ℝ) ^ l) ≤ P * 2 ^ s * ρ s a m := by
    obtain ⟨h1, _⟩ := rho_comp (s := s) (a := a) hs.le hρ2l hl1R
      (by nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 ^ l by positivity) (show (0 : ℝ) ≤ 2 ^ l - 2 by linarith)] : (m : ℝ) ≤ ((2 : ℝ) ^ l) ^ 2)
    have h2 : ((m : ℝ) / 2 ^ l) ^ s ≤ 2 ^ s :=
      Real.rpow_le_rpow (by positivity) ((div_le_iff₀ (by linarith)).2 (by linarith)) hs.le
    refine h1.trans ?_
    have := rho_nonneg (s := s) (a := a) (show (1 : ℝ) < m by linarith)
    calc 2 ^ |a| * ((m : ℝ) / 2 ^ l) ^ s * ρ s a m ≤ 2 ^ |a| * 2 ^ s * ρ s a m := by gcongr
      _ = _ := by ring
  -- E3
  have E3 : ρ s a m ≤ P * (3 * (D : ℝ)) ^ s * (lam : ℝ) ^ s * ρ s a n' := by
    have hmn' : (m : ℝ) ≤ n' := by
      have : m ≤ n' := by show m ≤ D * 2 ^ L + 1; have : 2 ^ L ≤ D * 2 ^ L := Nat.le_mul_of_pos_left _ (by omega); omega
      exact_mod_cast this
    have hn'2 : (n' : ℝ) ≤ 3 * D * lam * m := by
      have : n' ≤ 3 * D * lam * m := by
        show D * 2 ^ L + 1 ≤ 3 * D * lam * m
        have h1 : D * 2 ^ L ≤ D * (2 * (lam * m)) := Nat.mul_le_mul_left D h2L
        have h2 : 1 ≤ D * (lam * m) := Nat.mul_pos (by omega) (by positivity)
        nlinarith
      exact_mod_cast this
    have hm3R : (3 * D * lam : ℝ) ≤ m := by exact_mod_cast hm3
    obtain ⟨h1, _⟩ := rho_comp (s := s) (a := a) hs.le (show (1 : ℝ) < m by linarith) hmn'
      (hn'2.trans (by rw [sq]; exact mul_le_mul_of_nonneg_right hm3R (by positivity)))
    have h2 : ((n' : ℝ) / m) ^ s ≤ (3 * (D : ℝ)) ^ s * (lam : ℝ) ^ s := by
      rw [← Real.mul_rpow (by positivity) hlam0.le]
      exact Real.rpow_le_rpow (by positivity)
        ((div_le_iff₀ (by linarith)).2 (by linarith)) hs.le
    refine h1.trans ?_
    have := rho_nonneg (s := s) (a := a) (show (1 : ℝ) < n' by linarith)
    calc 2 ^ |a| * ((n' : ℝ) / m) ^ s * ρ s a n' ≤
        2 ^ |a| * ((3 * (D : ℝ)) ^ s * (lam : ℝ) ^ s) * ρ s a n' := by gcongr
      _ = _ := by ring
  have hcore := real_core (c := c) (J := J) (C₅ := C₅) (P := P) (t := 2 ^ s)
    (d := (3 * (D : ℝ)) ^ s) (ls := (lam : ℝ) ^ s) (lA := (lam : ℝ) ^ A) (ω := W K m)
    (Rm := ρ s a m) (Ry := ρ s a n') (Rl := ρ s a ((2 : ℝ) ^ l)) hc hJ hC₅ hP
    (by positivity) (by positivity) (by positivity)
    (rho_nonneg (show (1 : ℝ) < m by linarith)) E1 E2
    (by simpa [mul_assoc] using E3) (by simpa [T, mul_assoc] using hlamT)
  have hfinm : kolmogorovWidth K m ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (kolmogorovWidth_antitone K (Nat.zero_le m))
  calc ENNReal.ofReal (ε * ρ s a m) ≤ ENNReal.ofReal (W K m) := ENNReal.ofReal_le_ofReal hcore
    _ = kolmogorovWidth K m := ENNReal.ofReal_toReal hfinm

end Carl2

/-- Lemma 3.1 (Carl).  For a bounded set `K` (finite zeroth Kolmogorov width), `s = α > 0` and an
arbitrary real log exponent `a = β`, an eventual width upper bound `d_k ≤ C η_k` and an eventual
entropy lower bound `e_k ≥ c η_k`, with `η_k = k^{-s} (log k)^a`, give `e_k ≍ η_k` and
`d_k ≍ η_k` for all large `k`.  (The repository's `log k` replaces the manuscript's
`log (k+1)`; the two agree up to constants for `k ≥ 2`.) -/
theorem carl_lemma_3_1
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (s a : ℝ) (hs : 0 < s)
    (hbdd : kolmogorovWidth K 0 ≠ ⊤)
    (hWidth : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      kolmogorovWidth K n ≤ ENNReal.ofReal (C * logarithmicIndexRate s a n))
    (hEntropy : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ENNReal.ofReal (c * logarithmicIndexRate s a n) ≤ entropyNumber n K) :
    AlignmentPaperPeriodic.twoSidedEntropyRate K s a ∧ Latest.twoSidedWidthRate K s a := by
  obtain ⟨C, hC, nU, hU⟩ := hWidth
  obtain ⟨c, hc, nE, hE⟩ := hEntropy
  let A := ⌈s⌉₊ + 1
  have hsA : s < A := by
    have := Nat.le_ceil s
    dsimp [A]; push_cast; linarith
  have hR : 0 ≤ (kolmogorovWidth K 0).toReal := ENNReal.toReal_nonneg
  have hzero : kolmogorovWidth K 0 ≤ ENNReal.ofReal (kolmogorovWidth K 0).toReal :=
    (ENNReal.ofReal_toReal hbdd).ge
  obtain ⟨C', hC', N, hN⟩ := entropy_upper (A := A) hs hsA hR hC hzero hU
  obtain ⟨ε, hε, M, hM⟩ := width_lower (A := A) hs hsA hR hC hc hzero hU hE
  refine ⟨⟨c, C', hc, hC', max 2 (max nE N), le_max_left _ _, fun k hk => ⟨hE k ?_, hN k ?_⟩⟩,
    ⟨ε, C, hε, hC, max 2 (max M nU), le_max_left _ _, fun k hk => ⟨hM k ?_, hU k ?_⟩⟩⟩
  all_goals omega

end BrownianSharp.AlignmentPaperCarlLemma
