import KLS.SubsetOrbitIsometry
import KLS.FiniteIsometryAverageAlgebra

/-! The incidence row is the actual average over permutations of its block. -/
open Finset
open scoped BigOperators
noncomputable section
namespace KLS
variable {H α : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [DecidableEq α]

lemma perm_ofSubtype_image_self (B : Finset α) (σ : Equiv.Perm B) :
    B.image (Equiv.Perm.ofSubtype σ) = B := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem σ b).mpr hb
  · simp only [Finset.card_image_of_injective _ (Equiv.Perm.ofSubtype σ).injective]
    exact le_rfl

lemma exists_perm_ofSubtype_image (B A F : Finset α) (hA : A ⊆ B) (hF : F ⊆ B)
    (hc : A.card = F.card) :
    ∃ σ : Equiv.Perm B, A.image (Equiv.Perm.ofSubtype σ) = F := by
  let A' := A.subtype (fun a => a ∈ B)
  let F' := F.subtype (fun a => a ∈ B)
  have hmA : A'.map (Function.Embedding.subtype _) = A := Finset.subtype_map_of_mem hA
  have hmF : F'.map (Function.Embedding.subtype _) = F := Finset.subtype_map_of_mem hF
  have hc' : A'.card = F'.card := by
    have ha := congrArg Finset.card hmA
    have hf := congrArg Finset.card hmF
    simpa only [Finset.card_map] using ha.trans (hc.trans hf.symm)
  obtain ⟨σ, hσ⟩ := exists_perm_image_finset_eq A' F' hc'
  refine ⟨σ, ?_⟩
  calc
    A.image (Equiv.Perm.ofSubtype σ) =
        (A'.image σ).map (Function.Embedding.subtype _) := by
      rw [← hmA]
      simp only [Finset.map_eq_image, Finset.image_image]
      congr 1
      funext a
      exact Equiv.Perm.ofSubtype_apply_coe σ a
    _ = F := by rw [hσ, hmF]

theorem finiteIsometryAverage_eq_of_fixed {G : Type*} [Group G] [Fintype G]
    (ρ : G →* (H ≃ₗᵢ[ℝ] H)) (x : H) (hf : ∀ g, ρ g x = x) :
    finiteIsometryAverage ρ x = x := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [finiteIsometryAverage, hf, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN, one_smul]

/-- Separate symmetry in a block and its complement implies precisely the
stabilizer invariance used by the constructed subset orbit. -/
theorem fixed_of_two_block_symmetry
    (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H) (A : Finset α)
    (hA : ∀ σ : Equiv.Perm A, ρ (Equiv.Perm.ofSubtype σ) x = x)
    (hC : ∀ σ : Equiv.Perm {a : α // a ∉ A}, ρ (Equiv.Perm.ofSubtype σ) x = x)
    (σ : Equiv.Perm α) (hσ : A.image σ = A) : ρ σ x = x := by
  have hp (a : α) : σ a ∈ A ↔ a ∈ A := by
    constructor
    · intro ha
      rw [← hσ] at ha
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
      rwa [σ.injective hba] at hb
    · intro ha
      rw [← hσ]
      exact Finset.mem_image_of_mem σ ha
  let τ := σ.subtypePerm hp
  let υ : Equiv.Perm {a : α // a ∉ A} :=
    σ.subtypePerm (fun a => not_congr (hp a))
  have he : (Equiv.Perm.ofSubtype τ) * (Equiv.Perm.ofSubtype υ) = σ := by
    apply Equiv.ext
    intro a
    change Equiv.Perm.ofSubtype τ (Equiv.Perm.ofSubtype υ a) = σ a
    by_cases ha : a ∈ A
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem υ (not_not.mpr ha)]
      exact Equiv.Perm.ofSubtype_subtypePerm_of_mem hp ha
    · have hc : Equiv.Perm.ofSubtype υ a = σ a :=
        Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun a => a ∉ A)
          (fun a => not_congr (hp a)) ha
      rw [hc, Equiv.Perm.ofSubtype_apply_of_not_mem τ ((hp a).not.mpr ha)]
  rw [← he, map_mul]
  change ρ (Equiv.Perm.ofSubtype τ) (ρ (Equiv.Perm.ofSubtype υ) x) = x
  rw [hC υ, hA τ]

variable (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H) (A : Finset α)
  (hfix : ∀ σ : Equiv.Perm α, A.image σ = A → ρ σ x = x)

include hfix

/-- No averaging identity is assumed: the row is invariant under the actual
block group, and averaging each of its orbit summands gives the same average. -/
theorem subsetOrbitSum_eq_choose_smul_average (d : ℕ) (hAd : A.card = d)
    (B : Finset α) (hAB : A ⊆ B) :
    subsetOrbitSum ρ x A d B = (B.card.choose d : ℝ) •
      finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x := by
  let ρB := ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)
  have hrow (σ : Equiv.Perm B) :
      ρB σ (subsetOrbitSum ρ x A d B) = subsetOrbitSum ρ x A d B := by
    change ρ (Equiv.Perm.ofSubtype σ) _ = _
    rw [← subsetOrbitSum_image ρ x A hfix d hAd,
      perm_ofSubtype_image_self]
  have hmean (F : Finset α) (hF : F ∈ B.powersetCard d) :
      finiteIsometryAverage ρB (subsetOrbitVector ρ x A F) = finiteIsometryAverage ρB x := by
    obtain ⟨σ, hσ⟩ := exists_perm_ofSubtype_image B A F hAB (mem_powersetCard.mp hF).1
      (hAd.trans (mem_powersetCard.mp hF).2.symm)
    rw [subsetOrbitVector_eq_of_image ρ x A hfix F _ hσ]
    exact finiteIsometryAverage_right_invariant ρB x σ
  calc
    subsetOrbitSum ρ x A d B = finiteIsometryAverage ρB (subsetOrbitSum ρ x A d B) :=
      (finiteIsometryAverage_eq_of_fixed ρB _ hrow).symm
    _ = ∑ F ∈ B.powersetCard d, finiteIsometryAverage ρB (subsetOrbitVector ρ x A F) :=
      map_sum (finiteIsometryAverageLinearMap ρB) _ _
    _ = ∑ _F ∈ B.powersetCard d, finiteIsometryAverage ρB x :=
      Finset.sum_congr rfl hmean
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, ← Nat.cast_smul_eq_nsmul ℝ]

end KLS
end
#print axioms KLS.subsetOrbitSum_eq_choose_smul_average
