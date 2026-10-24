import BrownianSharp.AlignmentFractionalGeometricPartition
import Mathlib.Tactic

/-! One-hot refinement of the coarse and dyadic MvN partition weights into
short intervals suitable for one-sided Taylor approximation. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentFractionalPastTailPartition

open BrownianSharp.AlignmentFractionalGeometricPartition

def shellScale (j : Fin J) : ℝ := 1/(2:ℝ)^j.val

def coarseLeft (k : Fin 4) : ℝ :=
  if k.val = 0 then 1/2 else if k.val = 1 then 3/4 else 1

def coarseRight (k : Fin 4) : ℝ :=
  if k.val = 0 then 3/4 else if k.val = 1 then 1 else 1

def shellLeft (j : Fin J) (k : Fin 4) : ℝ :=
  shellScale j * (if k.val = 0 then 1/4 else if k.val = 1 then 3/8
    else if k.val = 2 then 9/16 else 27/32)

def shellRight (j : Fin J) (k : Fin 4) : ℝ :=
  shellScale j * (if k.val = 0 then 3/8 else if k.val = 1 then 9/16
    else if k.val = 2 then 27/32 else 1)

def pieceLeft (J : ℕ) (i : Option (Fin J) × Fin 4) : ℝ :=
  match i.1 with
  | none => coarseLeft i.2
  | some j => shellLeft j i.2

def pieceRight (J : ℕ) (i : Option (Fin J) × Fin 4) : ℝ :=
  match i.1 with
  | none => coarseRight i.2
  | some j => shellRight j i.2

def chosenPiece (J : ℕ) (base : Option (Fin J)) (t : ℝ) : Fin 4 :=
  match base with
  | none => if t < 3/4 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  | some j =>
      let c := shellScale j
      if t < 3*c/8 then ⟨0, by omega⟩
      else if t < 9*c/16 then ⟨1, by omega⟩
      else if t < 27*c/32 then ⟨2, by omega⟩
      else ⟨3, by omega⟩

/-- Exactly one refined interval receives the mass of its parent POU piece. -/
def refinedWeight (J : ℕ) (i : Option (Fin J) × Fin 4) (t : ℝ) : ℝ :=
  if i.2 = chosenPiece J i.1 t then partitionWeight J i.1 t else 0

theorem refinedWeight_nonneg {J : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (i : Option (Fin J) × Fin 4) : 0 ≤ refinedWeight J i t := by
  unfold refinedWeight
  split
  · exact partitionWeight_nonneg ht i.1
  · exact le_rfl

theorem refinedWeight_fiber_sum (J : ℕ) (base : Option (Fin J)) (t : ℝ) :
    (∑ k : Fin 4, refinedWeight J (base,k) t) = partitionWeight J base t := by
  classical
  simp [refinedWeight, Finset.sum_ite_eq', Finset.mem_univ]

theorem refinedWeight_sum (J : ℕ) (t : ℝ) :
    (∑ i : Option (Fin J) × Fin 4, refinedWeight J i t) =
      cutoff (t*(2:ℝ)^J) := by
  rw [Fintype.sum_prod_type]
  simp_rw [refinedWeight_fiber_sum]
  exact partitionWeight_sum J t

theorem refinedMass_eq_one (J : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ i : Option (Fin J) × Fin 4, refinedWeight J i t) +
      (1-cutoff (t*(2:ℝ)^J)) = 1 := by
  rw [refinedWeight_sum]
  ring

theorem refinedWeight_support {J : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Option (Fin J) × Fin 4) (hwi : refinedWeight J i t ≠ 0) :
    t ∈ Set.Icc (pieceLeft J i) (pieceRight J i) := by
  classical
  have hparent : partitionWeight J i.1 t ≠ 0 := by
    unfold refinedWeight at hwi
    split at hwi
    · exact hwi
    · exact (hwi rfl).elim
  have hchosen : i.2 = chosenPiece J i.1 t := by
    unfold refinedWeight at hwi
    split at hwi
    · assumption
    · exact (hwi rfl).elim
  cases ibase : i.1 with
  | none =>
      have hpar : coarseWeight t ≠ 0 := by
        simpa [partitionWeight, ibase] using hparent
      have hs := coarseWeight_support ht0 ht1 hpar
      by_cases hcut : t < 3/4
      · have hk : i.2.val = 0 := by
          have := hchosen
          simp [chosenPiece, ibase, hcut] at this
          exact congrArg Fin.val this
        have hleft : coarseLeft i.2 = 1/2 := by simp [coarseLeft, hk]
        have hright : coarseRight i.2 = 3/4 := by simp [coarseRight, hk]
        simp only [pieceLeft, pieceRight, ibase]
        rw [hleft, hright]
        exact ⟨hs.1, le_of_lt hcut⟩
      · have hk : i.2.val = 1 := by
          have := hchosen
          simp [chosenPiece, ibase, hcut] at this
          exact congrArg Fin.val this
        have hleft : coarseLeft i.2 = 3/4 := by simp [coarseLeft, hk]
        have hright : coarseRight i.2 = 1 := by simp [coarseRight, hk]
        simp only [pieceLeft, pieceRight, ibase]
        rw [hleft, hright]
        exact ⟨le_of_not_gt hcut, hs.2⟩
  | some j =>
      have hpar : shellWeight j.val t ≠ 0 := by
        simpa [partitionWeight, ibase] using hparent
      have hs := shellWeight_support ht0 hpar
      let c := shellScale j
      have hc : 0 < c := by dsimp [c, shellScale]; positivity
      by_cases h0 : t < 3*c/8
      · have h0' : t < 3*shellScale j/8 := by simpa [c] using h0
        have hk : i.2.val = 0 := by
          have := hchosen
          have hv := congrArg Fin.val this
          simpa [chosenPiece, ibase, h0'] using hv
        have hlo : c/4 ≤ t := by
          simpa [c, shellScale] using hs.1
        have hleft : shellLeft j i.2 = c/4 := by simp [shellLeft, hk, c]; ring
        have hright : shellRight j i.2 = 3*c/8 := by simp [shellRight, hk, c]; ring
        simp only [pieceLeft, pieceRight, ibase]
        rw [hleft, hright]
        exact ⟨hlo, le_of_lt h0⟩
      · by_cases h1 : t < 9*c/16
        · have h0' : 3*shellScale j/8 ≤ t := by
            simpa [c] using (le_of_not_gt h0)
          have hn0 : ¬ t < 3*shellScale j/8 := not_lt.mpr h0'
          have h1' : t < 9*shellScale j/16 := by simpa [c] using h1
          have hk : i.2.val = 1 := by
            have := hchosen
            have hv := congrArg Fin.val this
            simpa [chosenPiece, ibase, hn0, h1'] using hv
          have hlo : 3*c/8 ≤ t := le_of_not_gt h0
          have hleft : shellLeft j i.2 = 3*c/8 := by simp [shellLeft, hk, c]; ring
          have hright : shellRight j i.2 = 9*c/16 := by simp [shellRight, hk, c]; ring
          simp only [pieceLeft, pieceRight, ibase]
          rw [hleft, hright]
          exact ⟨hlo, le_of_lt h1⟩
        · by_cases h2 : t < 27*c/32
          · have h0' : 3*shellScale j/8 ≤ t := by
              simpa [c] using (le_of_not_gt h0)
            have h1' : 9*shellScale j/16 ≤ t := by
              simpa [c] using (le_of_not_gt h1)
            have hn0 : ¬ t < 3*shellScale j/8 := not_lt.mpr h0'
            have hn1 : ¬ t < 9*shellScale j/16 := not_lt.mpr h1'
            have h2' : t < 27*shellScale j/32 := by simpa [c] using h2
            have hk : i.2.val = 2 := by
              have := hchosen
              have hv := congrArg Fin.val this
              simpa [chosenPiece, ibase, hn0, hn1, h2'] using hv
            have hlo : 9*c/16 ≤ t := le_of_not_gt h1
            have hleft : shellLeft j i.2 = 9*c/16 := by simp [shellLeft, hk, c]; ring
            have hright : shellRight j i.2 = 27*c/32 := by simp [shellRight, hk, c]; ring
            simp only [pieceLeft, pieceRight, ibase]
            rw [hleft, hright]
            exact ⟨hlo, le_of_lt h2⟩
          · have h0' : 3*shellScale j/8 ≤ t := by
              simpa [c] using (le_of_not_gt h0)
            have h1' : 9*shellScale j/16 ≤ t := by
              simpa [c] using (le_of_not_gt h1)
            have h2' : 27*shellScale j/32 ≤ t := by
              simpa [c] using (le_of_not_gt h2)
            have hn0 : ¬ t < 3*shellScale j/8 := not_lt.mpr h0'
            have hn1 : ¬ t < 9*shellScale j/16 := not_lt.mpr h1'
            have hn2 : ¬ t < 27*shellScale j/32 := not_lt.mpr h2'
            have hk : i.2.val = 3 := by
              have := hchosen
              have hv := congrArg Fin.val this
              simpa [chosenPiece, ibase, hn0, hn1, hn2] using hv
            have hlo : 27*c/32 ≤ t := le_of_not_gt h2
            have hright : shellRight j i.2 = c := by simp [shellRight, hk, c]
            have hleft : shellLeft j i.2 = 27*c/32 := by simp [shellLeft, hk, c]; ring
            have hupper : t ≤ c := by
              simpa [c, shellScale] using hs.2
            simp only [pieceLeft, pieceRight, ibase]
            rw [hleft, hright]
            exact ⟨hlo, hupper⟩

end BrownianSharp.AlignmentFractionalPastTailPartition
