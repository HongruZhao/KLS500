import KLS.SubsetOrbitAverage

/-! BKL Lemma 2.2 for an actual isometric permutation representation. -/
open Finset
open scoped BigOperators
noncomputable section
namespace KLS
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [DecidableEq α]

lemma powersetCard_filter_subset (Ω E : Finset α) (hE : E ⊆ Ω) (d : ℕ) :
    (Ω.powersetCard d).filter (fun F => F ⊆ E) = E.powersetCard d := by
  ext F
  simp only [mem_filter, mem_powersetCard]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hE, h.2⟩, h.1⟩⟩

omit [InnerProductSpace ℝ H] in
lemma sum_incidence_eq_powersetCard (Ω E : Finset α) (hE : E ⊆ Ω)
    (d : ℕ) (v : Finset α → H) :
    (∑ F ∈ Ω.powersetCard d, if F ⊆ E then v F else 0) =
      ∑ F ∈ E.powersetCard d, v F := by
  rw [← Finset.sum_filter, powersetCard_filter_subset Ω E hE d]

/-- The original block stabilizer is the only symmetry premise. The orbit
vectors, incidence rows and the symmetrizer are all constructed from ρ and x. -/
theorem norm_le_choose_mul_blockAverage
    (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (Ω A B : Finset α) (d : ℕ) (hΩ : Ω.card = 3*d)
    (hAd : A.card = d) (hBd : B.card = 2*d)
    (hAB : A ⊆ B) (_hBΩ : B ⊆ Ω)
    (hfix : ∀ σ : Equiv.Perm α, A.image σ = A → ρ σ x = x) :
    ‖x‖ ≤ ((2*d).choose d : ℝ) *
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖ := by
  have hgram := sum_norm_sq_le_subset_incidence Ω d hΩ (subsetOrbitVector ρ x A)
  have hleft : (∑ F ∈ Ω.powersetCard d, ‖subsetOrbitVector ρ x A F‖^2) =
      ((3*d).choose d : ℝ) * ‖x‖^2 := by
    calc
      _ = ∑ _F ∈ Ω.powersetCard d, ‖x‖^2 := Finset.sum_congr rfl fun F hF =>
        congrArg (fun t : ℝ => t^2) (norm_subsetOrbitVector ρ x A F
          (hAd.trans (mem_powersetCard.mp hF).2.symm))
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, hΩ, nsmul_eq_mul]
  have hright : (∑ E ∈ Ω.powersetCard (2*d),
      ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then subsetOrbitVector ρ x A F else 0‖^2) =
      ((3*d).choose (2*d) : ℝ) * ‖subsetOrbitSum ρ x A d B‖^2 := by
    calc
      _ = ∑ _E ∈ Ω.powersetCard (2*d), ‖subsetOrbitSum ρ x A d B‖^2 := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [sum_incidence_eq_powersetCard Ω E (mem_powersetCard.mp hE).1]
        exact congrArg (fun t : ℝ => t^2) (norm_subsetOrbitSum_eq_of_card ρ x A hfix d hAd
          B E (hBd.trans (mem_powersetCard.mp hE).2.symm))
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, hΩ, nsmul_eq_mul]
  have hchoose : (3*d).choose (2*d) = (3*d).choose d := by
    have hsub : 3*d-d = 2*d := by omega
    rw [← hsub, Nat.choose_symm (by omega)]
  have hpos : 0 < ((3*d).choose d : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : d ≤ 3*d)
  rw [hleft, hright, hchoose] at hgram
  have hs : ‖x‖^2 ≤ ‖subsetOrbitSum ρ x A d B‖^2 :=
    (mul_le_mul_iff_right₀ hpos).mp hgram
  have hn := (sq_le_sq₀ (norm_nonneg x) (norm_nonneg (subsetOrbitSum ρ x A d B))).mp hs
  rw [subsetOrbitSum_eq_choose_smul_average ρ x A hfix d hAd B hAB,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), hBd] at hn
  exact hn

/-- Literal finite block-symmetry estimate with the paper's factor 4^d. It
applies equally to larger tensor spaces, since ρ may fix every other index. -/
theorem norm_le_four_pow_mul_blockAverage
    (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (Ω A B : Finset α) (d : ℕ) (hΩ : Ω.card = 3*d)
    (hAd : A.card = d) (hBd : B.card = 2*d)
    (hAB : A ⊆ B) (hBΩ : B ⊆ Ω)
    (hfix : ∀ σ : Equiv.Perm α, A.image σ = A → ρ σ x = x) :
    ‖x‖ ≤ (4 : ℝ)^d *
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖ := by
  have he : (2 : ℕ)^(2*d) = 4^d := by rw [pow_mul]; norm_num
  have hc : ((2*d).choose d : ℝ) ≤ (4 : ℝ)^d := by
    exact_mod_cast (Nat.choose_le_two_pow (2*d) d).trans_eq he
  exact (norm_le_choose_mul_blockAverage ρ x Ω A B d hΩ hAd hBd hAB hBΩ hfix).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

/-- Paper form: symmetry under the two independent block permutation groups
is sufficient. No incidence-row or averaging formula is an input. -/
theorem norm_le_four_pow_mul_blockAverage_of_two_block_symmetry
    (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (Ω A B : Finset α) (d : ℕ) (hΩ : Ω.card = 3*d)
    (hAd : A.card = d) (hBd : B.card = 2*d)
    (hAB : A ⊆ B) (hBΩ : B ⊆ Ω)
    (hA : ∀ σ : Equiv.Perm A, ρ (Equiv.Perm.ofSubtype σ) x = x)
    (hC : ∀ σ : Equiv.Perm {a : α // a ∉ A}, ρ (Equiv.Perm.ofSubtype σ) x = x) :
    ‖x‖ ≤ (4 : ℝ)^d *
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖ :=
  norm_le_four_pow_mul_blockAverage ρ x Ω A B d hΩ hAd hBd hAB hBΩ
    (fixed_of_two_block_symmetry ρ x A hA hC)

end KLS
end
#print axioms KLS.norm_le_choose_mul_blockAverage
#print axioms KLS.norm_le_four_pow_mul_blockAverage
#print axioms KLS.norm_le_four_pow_mul_blockAverage_of_two_block_symmetry
