import SpectralReductionJumpIncidence

open Finset
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [DecidableEq α]

theorem norm_sq_mul_choose_le_jump_blockAverage
    (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (Ω A B : Finset α) (d k m : ℕ) (hΩ : Ω.card = 2*d+m) (hkm : k≤m)
    (hAd : A.card = d) (hBd : B.card = d+k)
    (hAB : A ⊆ B) (_hBΩ : B ⊆ Ω)
    (hfix : ∀ σ : Equiv.Perm α, A.image σ = A → ρ σ x = x) :
    (m.choose k : ℝ)*‖x‖^2 ≤ ((d+m).choose k : ℝ)*((d+k).choose d : ℝ) *
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2 := by
  have hgram := sum_norm_sq_le_subset_incidence_jump Ω d k m hΩ hkm (subsetOrbitVector ρ x A)
  have hleft : (∑ F ∈ Ω.powersetCard d, ‖subsetOrbitVector ρ x A F‖^2) =
      ((2*d+m).choose d : ℝ) * ‖x‖^2 := by
    calc
      _ = ∑ _F ∈ Ω.powersetCard d, ‖x‖^2 := Finset.sum_congr rfl fun F hF =>
        congrArg (fun t : ℝ => t^2) (norm_subsetOrbitVector ρ x A F
          (hAd.trans (mem_powersetCard.mp hF).2.symm))
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, hΩ, nsmul_eq_mul]
  have hright : (∑ E ∈ Ω.powersetCard (d+k),
      ‖∑ F ∈ Ω.powersetCard d, if F ⊆ E then subsetOrbitVector ρ x A F else 0‖^2) =
      ((2*d+m).choose (d+k) : ℝ) * ‖subsetOrbitSum ρ x A d B‖^2 := by
    calc
      _ = ∑ _E ∈ Ω.powersetCard (d+k), ‖subsetOrbitSum ρ x A d B‖^2 := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [sum_incidence_eq_powersetCard Ω E (mem_powersetCard.mp hE).1]
        exact congrArg (fun t : ℝ => t^2) (norm_subsetOrbitSum_eq_of_card ρ x A hfix d hAd
          B E (hBd.trans (mem_powersetCard.mp hE).2.symm))
      _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, hΩ, nsmul_eq_mul]
  have hpos : 0 < ((2*d+m).choose d : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : d ≤ 2*d+m)
  have hprod : ((2*d+m).choose (d+k) : ℝ)*((d+k).choose d : ℝ) =
      ((2*d+m).choose d : ℝ)*((d+m).choose k : ℝ) := by
    have hs1 : 2*d+m-d=d+m := by omega
    have hs2 : d+k-d=k := by omega
    have hn := Nat.choose_mul (n:=2*d+m) (k:=d+k) (s:=d) (by omega)
    rw [hs1, hs2] at hn
    exact_mod_cast hn
  rw [hleft, hright, subsetOrbitSum_eq_choose_smul_average ρ x A hfix d hAd B hAB,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), hBd, mul_pow] at hgram
  have hrightid : ((2*d+m).choose (d+k) : ℝ)*(((d+k).choose d : ℝ)^2 *
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2) =
      ((2*d+m).choose d : ℝ)*(((d+m).choose k : ℝ)*((d+k).choose d : ℝ)*
      ‖finiteIsometryAverage (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2) := by
    calc
      _ = (((2*d+m).choose (d+k) : ℝ)*((d+k).choose d : ℝ))*
          (((d+k).choose d : ℝ)*‖finiteIsometryAverage
            (ρ.comp (Equiv.Perm.ofSubtype : Equiv.Perm B →* Equiv.Perm α)) x‖^2) := by ring
      _ = _ := by rw [hprod]; ring
  rw [hrightid] at hgram
  have hleftid : (m.choose k : ℝ)*(((2*d+m).choose d : ℝ)*‖x‖^2) =
      ((2*d+m).choose d : ℝ)*((m.choose k : ℝ)*‖x‖^2) := by ring
  rw [hleftid] at hgram
  exact (mul_le_mul_iff_right₀ hpos).mp hgram


end KLS.ConstantReduction
end
