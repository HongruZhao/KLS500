import SpectralReductionLongIncidence

open Finset
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {α : Type*} [DecidableEq α]

lemma card_common_jump_supersets (Ω F G : Finset α) (d k m : ℕ)
    (hΩ : Ω.card=2*d+m) (hkm : k≤m)
    (hF : F∈Ω.powersetCard d) (hG : G∈Ω.powersetCard d) :
    ((Ω.powersetCard (d+k)).filter fun E => F⊆E ∧ G⊆E).card=
      (m+(F∩G).card).choose (m+d-k) := by
  have hFt := (mem_powersetCard.mp hF).1
  have hGt := (mem_powersetCard.mp hG).1
  have hFc := (mem_powersetCard.mp hF).2
  have hGc := (mem_powersetCard.mp hG).2
  have hu : (F∪G).card+(F∩G).card=2*d := by
    simpa [hFc,hGc,two_mul] using card_union_add_card_inter F G
  have he : (Ω.powersetCard (d+k)).filter (fun E => F⊆E ∧ G⊆E)=
      (Ω.powersetCard (d+k)).filter (F∪G⊆·) := by
    ext E
    simp only [mem_filter, union_subset_iff]
  rw [he]
  by_cases huc : (F∪G).card≤d+k
  · rw [card_filter_powersetCard_subset (F∪G) Ω (d+k) (union_subset hFt hGt) huc,hΩ]
    have hleft : 2*d+m-(F∪G).card=m+(F∩G).card := by omega
    rw [hleft, Nat.choose_symm_of_eq_add (by omega :
      m+(F∩G).card=(d+k-(F∪G).card)+(m+d-k))]
  · have hz : (Ω.powersetCard (d+k)).filter (F∪G⊆·)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro E hE hFE
      have hh := Finset.card_le_card hFE
      rw [(mem_powersetCard.mp hE).2] at hh
      exact huc hh
    rw [hz, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega : m+(F∩G).card<m+d-k)]

theorem vandermonde_intersection_kernel_jump (m r L : ℕ) :
    (m+r).choose L=∑ s∈range (L+1), m.choose (L-s)*r.choose s := by
  rw [Nat.add_comm, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro s _
  rw [Nat.mul_comm]

theorem subset_incidence_gram_identity_jump (Ω : Finset α) (d k m : ℕ)
    (hΩ : Ω.card = 2 * d + m) (hkm : k≤m) (v : Finset α → H) :
    (∑ E ∈ Ω.powersetCard (d+k),
      ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then v F else 0‖ ^ 2) =
    ∑ s ∈ range (m+d-k+1), (m.choose (m+d-k-s) : ℝ) *
      ∑ S ∈ Ω.powersetCard s,
        ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2 := by
  classical
  let I := Ω.powersetCard d
  have hL := incidence_sum_norm_sq_eq (Ω.powersetCard (d+k)) I
    (fun E F => F ⊆ E) v
  have hR (s : ℕ) := incidence_sum_norm_sq_eq (Ω.powersetCard s) I
    (fun S F => S ⊆ F) v
  dsimp only [I] at hR
  rw [hL]
  calc
    _ = ∑ F ∈ I, ∑ G ∈ I,
        (((m + (F ∩ G).card).choose (m+d-k) : ℕ) : ℝ) * inner ℝ (v F) (v G) := by
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro G hG
      rw [card_common_jump_supersets Ω F G d k m hΩ hkm hF hG]
    _ = ∑ F ∈ I, ∑ G ∈ I, ∑ s ∈ range (m+d-k+1),
        (m.choose (m+d-k-s) : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) := by
      simp_rw [vandermonde_intersection_kernel_jump, Nat.cast_sum, Nat.cast_mul,
        Finset.sum_mul]
    _ = ∑ F ∈ I, ∑ s ∈ range (m+d-k+1), ∑ G ∈ I,
        (m.choose (m+d-k-s) : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) := by
      apply Finset.sum_congr rfl
      intro F hF
      exact Finset.sum_comm
    _ = ∑ s ∈ range (m+d-k+1), ∑ F ∈ I, ∑ G ∈ I,
        (m.choose (m+d-k-s) : ℝ) * ((F ∩ G).card.choose s : ℝ) * inner ℝ (v F) (v G) :=
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

theorem sum_norm_sq_le_subset_incidence_jump (Ω : Finset α) (d k m : ℕ)
    (hΩ : Ω.card = 2 * d + m) (hkm : k≤m) (v : Finset α → H) :
    (m.choose k : ℝ) * (∑ F ∈ Ω.powersetCard d, ‖v F‖ ^ 2) ≤
      ∑ E ∈ Ω.powersetCard (d+k),
        ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then v F else 0‖ ^ 2 := by
  classical
  rw [subset_incidence_gram_identity_jump Ω d k m hΩ hkm v]
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
  have htop : (m.choose (m+d-k-d) : ℝ) *
      (∑ S ∈ Ω.powersetCard d,
        ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2) =
      (m.choose k : ℝ) * ∑ S ∈ Ω.powersetCard d, ‖v S‖ ^ 2 := by
    rw [show m+d-k-d=m-k by omega, Nat.choose_symm hkm]
    congr 1
    exact Finset.sum_congr rfl fun S hS => congrArg (fun w : H => ‖w‖ ^ 2) (hdiag S hS)
  rw [← htop]
  exact Finset.single_le_sum
    (f := fun s => (m.choose (m+d-k-s) : ℝ) * ∑ S ∈ Ω.powersetCard s,
      ‖∑ F ∈ Ω.powersetCard d, if S ⊆ F then v F else 0‖ ^ 2)
    (fun s _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun S _ => sq_nonneg _)) (by simp; omega)

end KLS.ConstantReduction
end
