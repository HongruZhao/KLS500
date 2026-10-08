import KLS.SubsetIncidenceGram
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.GroupTheory.Perm.Finite

/-! Actual subset orbits of a block-invariant vector under an isometric
permutation representation. The vector is constructed, not posited. -/
open Finset
open scoped BigOperators
noncomputable section
namespace KLS
variable {H α : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [DecidableEq α]

lemma exists_perm_image_finset_eq (A F : Finset α) (h : A.card = F.card) :
    ∃ σ : Equiv.Perm α, A.image σ = F := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq A F h
  exact ⟨σ, by simpa [Finset.map_eq_image] using hσ⟩

lemma perm_image_finset_mul (σ τ : Equiv.Perm α) (A : Finset α) :
    A.image (σ * τ) = (A.image τ).image σ := by
  rw [Finset.image_image]
  rfl

lemma perm_image_finset_inv (σ : Equiv.Perm α) (A : Finset α) :
    (A.image σ).image (σ⁻¹ : Equiv.Perm α) = A := by
  rw [Finset.image_image]
  simp

/-- The actual orbit representative associated with a subset. Off the correct
cardinality it is zero, and that branch is never used by incidence sums. -/
def subsetOrbitVector (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (A F : Finset α) : H :=
  if h : A.card = F.card then
    ρ (Classical.choose (exists_perm_image_finset_eq A F h)) x else 0

variable (ρ : Equiv.Perm α →* (H ≃ₗᵢ[ℝ] H)) (x : H) (A : Finset α)
variable (hfix : ∀ σ : Equiv.Perm α, A.image σ = A → ρ σ x = x)

include hfix

/-- Any permutation carrying the original block to F gives the same vector;
the original two-block invariance discharges the choice dependence. -/
theorem subsetOrbitVector_eq_of_image (F : Finset α) (σ : Equiv.Perm α)
    (hσ : A.image σ = F) : subsetOrbitVector ρ x A F = ρ σ x := by
  have hc : A.card = F.card := by rw [← hσ, Finset.card_image_of_injective _ σ.injective]
  let τ := Classical.choose (exists_perm_image_finset_eq A F hc)
  have hτ : A.image τ = F := Classical.choose_spec (exists_perm_image_finset_eq A F hc)
  have hst : A.image (σ⁻¹ * τ : Equiv.Perm α) = A := by
    rw [perm_image_finset_mul, hτ, ← hσ, perm_image_finset_inv]
  have he := congrArg (fun v : H => ρ σ v) (hfix (σ⁻¹ * τ) hst)
  have hm : ρ σ (ρ (σ⁻¹ * τ) x) = ρ τ x := by
    change (ρ σ * ρ (σ⁻¹ * τ)) x = _
    rw [← map_mul, mul_inv_cancel_left]
  rw [hm] at he
  simpa only [subsetOrbitVector, dite_eq_left hc] using he

/-- The constructed subset orbit is genuinely equivariant. -/
theorem subsetOrbitVector_image (F : Finset α) (hF : A.card = F.card)
    (σ : Equiv.Perm α) : subsetOrbitVector ρ x A (F.image σ) =
      ρ σ (subsetOrbitVector ρ x A F) := by
  obtain ⟨τ, hτ⟩ := exists_perm_image_finset_eq A F hF
  rw [subsetOrbitVector_eq_of_image ρ x A hfix F τ hτ]
  have he : A.image (σ * τ) = F.image σ := by rw [perm_image_finset_mul, hτ]
  rw [subsetOrbitVector_eq_of_image ρ x A hfix _ (σ * τ) he, map_mul]
  rfl

omit hfix in
/-- Every genuine subset orbit vector has the original norm. -/
theorem norm_subsetOrbitVector (F : Finset α) (hF : A.card = F.card) :
    ‖subsetOrbitVector ρ x A F‖ = ‖x‖ := by
  simp only [subsetOrbitVector, dite_eq_left hF, LinearIsometryEquiv.norm_map]

omit hfix in
lemma powersetCard_image_perm (E : Finset α) (d : ℕ) (σ : Equiv.Perm α) :
    (E.image σ).powersetCard d = (E.powersetCard d).image (fun F => F.image σ) := by
  have h := Finset.powersetCard_map σ.toEmbedding d E
  rw [Finset.map_eq_image, Finset.map_eq_image] at h
  change (E.image σ).powersetCard d =
    (E.powersetCard d).image (fun F => F.map σ.toEmbedding) at h
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using h

def subsetOrbitSum (d : ℕ) (E : Finset α) : H :=
  ∑ F ∈ E.powersetCard d, subsetOrbitVector ρ x A F

include hfix

theorem subsetOrbitSum_image (d : ℕ) (hA : A.card = d) (E : Finset α)
    (σ : Equiv.Perm α) : subsetOrbitSum ρ x A d (E.image σ) =
      ρ σ (subsetOrbitSum ρ x A d E) := by
  unfold subsetOrbitSum
  rw [powersetCard_image_perm E d σ]
  rw [Finset.sum_image]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro F hF
    exact subsetOrbitVector_image ρ x A hfix F
      (hA.trans (mem_powersetCard.mp hF).2.symm) σ
  · exact fun F _ G _ h => Finset.image_injective σ.injective h

theorem norm_subsetOrbitSum_eq_of_card (d : ℕ) (hA : A.card = d)
    (B E : Finset α) (hBE : B.card = E.card) :
    ‖subsetOrbitSum ρ x A d E‖ = ‖subsetOrbitSum ρ x A d B‖ := by
  obtain ⟨σ, hσ⟩ := exists_perm_image_finset_eq B E hBE
  rw [← hσ, subsetOrbitSum_image ρ x A hfix d hA, LinearIsometryEquiv.norm_map]

end KLS
end
#print axioms KLS.subsetOrbitVector_eq_of_image
#print axioms KLS.subsetOrbitVector_image
#print axioms KLS.norm_subsetOrbitVector
