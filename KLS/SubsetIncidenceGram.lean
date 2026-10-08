import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Bounds

/-! The finite Hilbert-space incidence identity underlying BKL (25). -/
open Finset
open scoped BigOperators
noncomputable section
namespace KLS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma norm_finset_sum_sq {ι : Type*} (s : Finset ι) (v : ι → H) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  exact Finset.sum_congr rfl fun i _ => inner_sum _ _ _

/-- Expand squared incidence sums and count every actual common row. -/
theorem incidence_sum_norm_sq_eq {α β : Type*} [DecidableEq α]
    (R : Finset α) (I : Finset β) (P : α → β → Prop)
    [DecidableRel P] (v : β → H) :
    (∑ r ∈ R, ‖∑ i ∈ I, if P r i then v i else 0‖ ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I,
        (((R.filter fun r => P r i ∧ P r j).card : ℕ) : ℝ) * inner ℝ (v i) (v j) := by
  classical
  simp_rw [norm_finset_sum_sq]
  have hp (r : α) (i j : β) :
      inner ℝ (if P r i then v i else 0) (if P r j then v j else 0) =
        if P r i ∧ P r j then inner ℝ (v i) (v j) else 0 := by
    split_ifs <;> simp_all
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]

variable {α : Type*} [DecidableEq α]

/-- Count the 2d-element supersets shared by two d-element sets in 3d positions. -/
lemma card_common_double_supersets (Ω F G : Finset α) (d : ℕ)
    (hΩ : Ω.card = 3 * d) (hF : F ∈ Ω.powersetCard d) (hG : G ∈ Ω.powersetCard d) :
    ((Ω.powersetCard (2 * d)).filter fun E => F ⊆ E ∧ G ⊆ E).card =
      (d + (F ∩ G).card).choose d := by
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
  have hleft : 3 * d - (F ∪ G).card = d + (F ∩ G).card := by omega
  have hright : 2 * d - (F ∪ G).card = (F ∩ G).card := by omega
  rw [hleft, hright, Nat.choose_symm_of_eq_add (by omega :
    d + (F ∩ G).card = (F ∩ G).card + d)]

/-- Count common s-element subsets of the same two sets. -/
lemma card_common_subsets (Ω F G : Finset α) (s : ℕ)
    (hF : F ⊆ Ω) (_hG : G ⊆ Ω) :
    ((Ω.powersetCard s).filter fun S => S ⊆ F ∧ S ⊆ G).card =
      (F ∩ G).card.choose s := by
  have he : (Ω.powersetCard s).filter (fun S => S ⊆ F ∧ S ⊆ G) =
      (F ∩ G).powersetCard s := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_inter_iff]
    constructor
    · rintro ⟨⟨_, hc⟩, hSF, hSG⟩
      exact ⟨⟨hSF, hSG⟩, hc⟩
    · rintro ⟨⟨hSF, hSG⟩, hc⟩
      exact ⟨⟨hSF.trans hF, hc⟩, hSF, hSG⟩
  rw [he, card_powersetCard]

lemma vandermonde_intersection_kernel (d r : ℕ) :
    (d + r).choose d = ∑ s ∈ range (d + 1), d.choose s * r.choose s := by
  rw [Nat.add_comm, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hs), Nat.mul_comm]

/-- The exact Hilbert-space Gram identity BKL (25), for arbitrary vectors
indexed by d-element subsets of an actual set of 3d positions. -/
theorem subset_incidence_gram_identity (Ω : Finset α) (d : ℕ)
    (hΩ : Ω.card = 3 * d) (v : Finset α → H) :
    (∑ E ∈ Ω.powersetCard (2 * d),
      ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then v F else 0‖ ^ 2) =
    ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
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
        (((d + (F ∩ G).card).choose d : ℕ) : ℝ) * inner ℝ (v F) (v G) := by
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro G hG
      rw [card_common_double_supersets Ω F G d hΩ hF hG]
    _ = ∑ F ∈ I, ∑ G ∈ I, ∑ s ∈ range (d + 1),
        (d.choose s : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) := by
      simp_rw [vandermonde_intersection_kernel, Nat.cast_sum, Nat.cast_mul,
        Finset.sum_mul]
    _ = ∑ F ∈ I, ∑ s ∈ range (d + 1), ∑ G ∈ I,
        (d.choose s : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) := by
      apply Finset.sum_congr rfl
      intro F hF
      exact Finset.sum_comm
    _ = ∑ s ∈ range (d + 1), ∑ F ∈ I, ∑ G ∈ I,
        (d.choose s : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) :=
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
theorem sum_norm_sq_le_subset_incidence (Ω : Finset α) (d : ℕ)
    (hΩ : Ω.card = 3 * d) (v : Finset α → H) :
    (∑ F ∈ Ω.powersetCard d, ‖v F‖ ^ 2) ≤
      ∑ E ∈ Ω.powersetCard (2 * d),
        ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then v F else 0‖ ^ 2 := by
  classical
  rw [subset_incidence_gram_identity Ω d hΩ v]
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
  have htop : (d.choose d : ℝ) *
      (∑ S ∈ Ω.powersetCard d,
        ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2) =
      ∑ S ∈ Ω.powersetCard d, ‖v S‖ ^ 2 := by
    simp only [Nat.choose_self, Nat.cast_one, one_mul]
    exact Finset.sum_congr rfl fun S hS => congrArg (fun w : H => ‖w‖ ^ 2) (hdiag S hS)
  rw [← htop]
  exact Finset.single_le_sum
    (f := fun s => (d.choose s : ℝ) * ∑ S ∈ Ω.powersetCard s,
      ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2)
    (fun s _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun S _ => sq_nonneg _)) (by simp)

end KLS
end
#print axioms KLS.incidence_sum_norm_sq_eq
#print axioms KLS.card_common_double_supersets
#print axioms KLS.subset_incidence_gram_identity
#print axioms KLS.sum_norm_sq_le_subset_incidence
