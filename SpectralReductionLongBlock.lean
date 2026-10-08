import SpectralReductionLongIncidence

open Finset
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [DecidableEq α]

theorem norm_sq_mul_choose_le_long_blockAverage
    (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (Ω A B : Finset α) (d k : ℕ) (hΩ : Ω.card = 2*d+k) (hdk : d≤k)
    (hAd : A.card = d) (hBd : B.card = 2*d)
    (hAB : A ⊆ B) (_hBΩ : B ⊆ Ω)
    (hfix : ∀ σ : Equiv.Perm α, A.image σ = A → ρ σ x = x) :
    (k.choose d : ℝ)*‖x‖^2 ≤ ((d+k).choose d : ℝ)*((2*d).choose d : ℝ) *
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2 := by
  have hgram := sum_norm_sq_le_subset_incidence_long Ω d k hΩ hdk (subsetOrbitVector ρ x A)
  have hleft : (∑ F ∈ Ω.powersetCard d, ‖subsetOrbitVector ρ x A F‖^2) =
      ((2*d+k).choose d : ℝ) * ‖x‖^2 := by
    calc
      _ = ∑ _F ∈ Ω.powersetCard d, ‖x‖^2 := Finset.sum_congr rfl fun F hF =>
        congrArg (fun t : ℝ => t^2) (norm_subsetOrbitVector ρ x A F
          (hAd.trans (mem_powersetCard.mp hF).2.symm))
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, hΩ, nsmul_eq_mul]
  have hright : (∑ E ∈ Ω.powersetCard (2*d),
      ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then subsetOrbitVector ρ x A F else 0‖^2) =
      ((2*d+k).choose (2*d) : ℝ) * ‖subsetOrbitSum ρ x A d B‖^2 := by
    calc
      _ = ∑ _E ∈ Ω.powersetCard (2*d), ‖subsetOrbitSum ρ x A d B‖^2 := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [sum_incidence_eq_powersetCard Ω E (mem_powersetCard.mp hE).1]
        exact congrArg (fun t : ℝ => t^2) (norm_subsetOrbitSum_eq_of_card ρ x A hfix d hAd
          B E (hBd.trans (mem_powersetCard.mp hE).2.symm))
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, hΩ, nsmul_eq_mul]
  have hpos : 0 < ((2*d+k).choose d : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : d ≤ 2*d+k)
  have hprod : ((2*d+k).choose (2*d) : ℝ)*((2*d).choose d : ℝ) =
      ((2*d+k).choose d : ℝ)*((d+k).choose d : ℝ) := by
    have hs1 : 2*d+k-d=d+k := by omega
    have hs2 : 2*d-d=d := by omega
    have hn := Nat.choose_mul (n:=2*d+k) (k:=2*d) (s:=d) (by omega)
    rw [hs1, hs2] at hn
    exact_mod_cast hn
  rw [hleft, hright, subsetOrbitSum_eq_choose_smul_average ρ x A hfix d hAd B hAB,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), hBd, mul_pow] at hgram
  have hrightid : ((2*d+k).choose (2*d) : ℝ)*(((2*d).choose d : ℝ)^2 *
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2) =
      ((2*d+k).choose d : ℝ)*(((d+k).choose d : ℝ)*((2*d).choose d : ℝ)*
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2) := by
    calc
      _ = (((2*d+k).choose (2*d) : ℝ)*((2*d).choose d : ℝ))*
          (((2*d).choose d : ℝ)*‖finiteIsometryAverage
            (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2) := by ring
      _ = _ := by rw [hprod]; ring
  rw [hrightid] at hgram
  have hleftid : (k.choose d : ℝ)*(((2*d+k).choose d : ℝ)*‖x‖^2) =
      ((2*d+k).choose d : ℝ)*((k.choose d : ℝ)*‖x‖^2) := by ring
  rw [hleftid] at hgram
  exact (mul_le_mul_iff_right₀ hpos).mp hgram

theorem norm_sq_le_triple_choose_blockAverage
    (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (Ω A B : Finset α) (d : ℕ) (hΩ : Ω.card = 4*d)
    (hAd : A.card = d) (hBd : B.card = 2*d)
    (hAB : A ⊆ B) (hBΩ : B ⊆ Ω)
    (hfix : ∀ σ : Equiv.Perm α, A.image σ = A → ρ σ x = x) :
    ‖x‖^2 ≤ ((3*d).choose d : ℝ)*
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2 := by
  have hh := norm_sq_mul_choose_le_long_blockAverage ρ x Ω A B d (2*d)
    (by omega) (by omega) hAd hBd hAB hBΩ hfix
  have hc : (0 : ℝ)<((2*d).choose d : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : d≤2*d)
  have he : d+2*d=3*d := by omega
  rw [he] at hh
  have hm : ((3*d).choose d : ℝ)*((2*d).choose d : ℝ)*
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2 =
      ((2*d).choose d : ℝ)*(((3*d).choose d : ℝ)*
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2) := by ring
  rw [hm] at hh
  exact (mul_le_mul_iff_right₀ hc).mp hh

end KLS.ConstantReduction
end
