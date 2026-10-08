import KLS.SubsetIncidenceGram
import KLS.BlockSymmetryInequality

open Finset
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {α : Type*} [DecidableEq α]

/-- Count the 2d-element supersets shared by two d-element sets in 2d+k positions. -/
lemma card_common_double_supersets_long (Ω F G : Finset α) (d k : ℕ)
    (hΩ : Ω.card = 2 * d + k) (hF : F ∈ Ω.powersetCard d) (hG : G ∈ Ω.powersetCard d) :
    ((Ω.powersetCard (2 * d)).filter fun E => F ⊆ E ∧ G ⊆ E).card =
      (k + (F ∩ G).card).choose k := by
  have hFt := (mem_powersetCard.mp hF).1
  have hGt := (mem_powersetCard.mp hG).1
  have hFc := (mem_powersetCard.mp hF).2
  have hGc := (mem_powersetCard.mp hG).2
  have hu : (F ∪ G).card + (F ∩ G).card = 2 * d := by
    simpa [hFc, hGc, two_mul] using card_union_add_card_inter F G
  have huc : (F ∪ G).card ≤ 2 * d := by omega
  have he : (Ω.powersetCard (2 * d)).filter (fun E => F ⊆ E ∧ G ⊆ E) =
      (Ω.powersetCard (2 * d)).filter (F ∪ G ⊆ ·) := by
    ext E
    simp only [mem_filter, union_subset_iff]
  rw [he, card_filter_powersetCard_subset (F ∪ G) Ω (2 * d)
    (union_subset hFt hGt) huc, hΩ]
  have hleft : 2 * d + k - (F ∪ G).card = k + (F ∩ G).card := by omega
  have hright : 2 * d - (F ∪ G).card = (F ∩ G).card := by omega
  rw [hleft, hright, Nat.choose_symm_of_eq_add (by omega :
    k + (F ∩ G).card = (F ∩ G).card + k)]

/-- The exact Hilbert-space Gram identity BKL (25), for arbitrary vectors
indexed by d-element subsets of an actual set of 2d+k positions. -/
theorem subset_incidence_gram_identity_long (Ω : Finset α) (d k : ℕ)
    (hΩ : Ω.card = 2 * d + k) (v : Finset α → H) :
    (∑ E ∈ Ω.powersetCard (2 * d),
      ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then v F else 0‖ ^ 2) =
    ∑ s ∈ range (k + 1), (k.choose s : ℝ) *
      ∑ S ∈ Ω.powersetCard s,
        ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2 := by
  classical
  let I := Ω.powersetCard d
  have hL := incidence_sum_norm_sq_eq (Ω.powersetCard (2 * d)) I
    (fun E F => F ⊆ E) v
  have hR (s : ℕ) := incidence_sum_norm_sq_eq (Ω.powersetCard s) I
    (fun S F => S ⊆ F) v
  dsimp only [I] at hR
  rw [hL]
  calc
    _ = ∑ F ∈ I, ∑ G ∈ I,
        (((k + (F ∩ G).card).choose k : ℕ) : ℝ) * inner ℝ (v F) (v G) := by
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro G hG
      rw [card_common_double_supersets_long Ω F G d k hΩ hF hG]
    _ = ∑ F ∈ I, ∑ G ∈ I, ∑ s ∈ range (k + 1),
        (k.choose s : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) := by
      simp_rw [vandermonde_intersection_kernel, Nat.cast_sum, Nat.cast_mul,
        Finset.sum_mul]
    _ = ∑ F ∈ I, ∑ s ∈ range (k + 1), ∑ G ∈ I,
        (k.choose s : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) := by
      apply Finset.sum_congr rfl
      intro F hF
      exact Finset.sum_comm
    _ = ∑ s ∈ range (k + 1), ∑ F ∈ I, ∑ G ∈ I,
        (k.choose s : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) :=
      Finset.sum_comm
    _ = _ := by
      simp_rw [hR]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Finset.mul_sum, ← mul_assoc]
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro G hG
      rw [card_common_subsets Ω F G s (mem_powersetCard.mp hF).1
        (mem_powersetCard.mp hG).1]

/-- The top-degree term of the actual nonnegative Gram decomposition gives
the lower bound used in BKL (25); it is not an assumed positivity premise. -/
theorem sum_norm_sq_le_subset_incidence_long (Ω : Finset α) (d k : ℕ)
    (hΩ : Ω.card = 2 * d + k) (hdk : d ≤ k) (v : Finset α → H) :
    (k.choose d : ℝ) * (∑ F ∈ Ω.powersetCard d, ‖v F‖ ^ 2) ≤
      ∑ E ∈ Ω.powersetCard (2 * d),
        ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then v F else 0‖ ^ 2 := by
  classical
  rw [subset_incidence_gram_identity_long Ω d k hΩ v]
  have hdiag (S : Finset α) (hS : S ∈ Ω.powersetCard d) :
      (∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0) = v S := by
    rw [Finset.sum_eq_single S]
    · simp
    · intro F hF hFS
      rw [ite_eq_right]
      intro hSF
      exact hFS ((eq_of_subset_of_card_le hSF
        (by rw [(mem_powersetCard.mp hF).2, (mem_powersetCard.mp hS).2])).symm)
    · intro h
      exact False.elim (h hS)
  have htop : (k.choose d : ℝ) *
      (∑ S ∈ Ω.powersetCard d,
        ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2) =
      (k.choose d : ℝ) * ∑ S ∈ Ω.powersetCard d, ‖v S‖ ^ 2 := by
    congr 1
    exact Finset.sum_congr rfl fun S hS => congrArg (fun w : H => ‖w‖ ^ 2) (hdiag S hS)
  rw [← htop]
  exact Finset.single_le_sum
    (f := fun s => (k.choose s : ℝ) * ∑ S ∈ Ω.powersetCard s,
      ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2)
    (fun s _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun S _ => sq_nonneg _)) (by simp; omega)

end KLS.ConstantReduction
end
