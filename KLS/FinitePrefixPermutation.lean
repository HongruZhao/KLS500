import KLS.WeightedIterationTaylorAction

/-! Literal extension of a permutation of the first m positions to p positions,
with every remaining position fixed, and absorption of its tensor average. -/

open scoped BigOperators
noncomputable section
namespace KLS

def prefixFinPermHom {m p : ℕ} (h : m ≤ p) : Equiv.Perm (Fin m) →* Equiv.Perm (Fin p) :=
  Equiv.Perm.extendDomainHom (Fin.castLEquiv h)

@[simp] theorem prefixFinPermHom_apply_castLE {m p : ℕ} (h : m ≤ p)
    (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    prefixFinPermHom h σ (Fin.castLE h i) = Fin.castLE h (σ i) := by
  exact Equiv.Perm.extendDomain_apply_image σ (Fin.castLEquiv h) i

theorem prefixFinPermHom_apply_of_le {m p : ℕ} (h : m ≤ p)
    (σ : Equiv.Perm (Fin m)) (i : Fin p) (hi : m ≤ i.val) :
    prefixFinPermHom h σ i = i := by
  exact Equiv.Perm.extendDomain_apply_not_subtype σ (Fin.castLEquiv h) (not_lt.mpr hi)

theorem prefixFinPermHom_apply_prefix {d q p : ℕ} (h : d + q = p)
    {m : ℕ} (hd : d ≤ m) (hm : m ≤ p) (σ : Equiv.Perm (Fin m)) (i : Fin d) :
    prefixFinPermHom hm σ (Fin.cast h (Fin.castAdd q i)) =
      Fin.castLE hm (σ (Fin.castLE hd i)) := by
  have he : Fin.cast h (Fin.castAdd q i) = Fin.castLE hm (Fin.castLE hd i) := by
    apply Fin.ext
    rfl
  rw [he, prefixFinPermHom_apply_castLE]

theorem prefixFinPermHom_apply_suffix {m q p : ℕ} (h : m + q = p)
    (σ : Equiv.Perm (Fin m)) (i : Fin q) :
    prefixFinPermHom (by omega : m ≤ p) σ (Fin.cast h (Fin.natAdd m i)) =
      Fin.cast h (Fin.natAdd m i) :=
  prefixFinPermHom_apply_of_le _ σ _ (by simp)

theorem prefixFinPermHom_comp {d m p : ℕ} (hd : d ≤ m) (hm : m ≤ p) :
    (prefixFinPermHom hm).comp (prefixFinPermHom hd) = prefixFinPermHom (hd.trans hm) := by
  apply MonoidHom.ext
  intro σ
  apply Equiv.ext
  intro i
  change prefixFinPermHom hm (prefixFinPermHom hd σ) i = prefixFinPermHom (hd.trans hm) σ i
  by_cases hid : i.val < d
  · let j : Fin d := ⟨i.val, hid⟩
    have he : i = Fin.castLE hm (Fin.castLE hd j) := by apply Fin.ext; rfl
    have he' : i = Fin.castLE (hd.trans hm) j := by apply Fin.ext; rfl
    rw [he, prefixFinPermHom_apply_castLE, prefixFinPermHom_apply_castLE]
    rw [← he, he', prefixFinPermHom_apply_castLE]
    rfl
  · by_cases him : i.val < m
    · let j : Fin m := ⟨i.val, him⟩
      have he : i = Fin.castLE hm j := by apply Fin.ext; rfl
      rw [he, prefixFinPermHom_apply_castLE,
        prefixFinPermHom_apply_of_le hd σ j (by exact Nat.le_of_not_gt hid)]
      exact (prefixFinPermHom_apply_of_le (hd.trans hm) σ _ (by exact Nat.le_of_not_gt hid)).symm
    · rw [prefixFinPermHom_apply_of_le hm _ i (Nat.le_of_not_gt him),
        prefixFinPermHom_apply_of_le (hd.trans hm) σ i (Nat.le_of_not_gt hid)]

def realTensorPrefixAction (n p : ℕ) (ι : Type*) [Fintype ι] {m : ℕ} (h : m ≤ p) :
    Equiv.Perm (Fin m) →*
      (EuclideanSpace ℝ ((Fin p → Fin n) × ι) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((Fin p → Fin n) × ι)) :=
  (realCoordinatePermutationAction n p ι).comp (prefixFinPermHom h)

theorem realTensorPrefixAverage_apply (n p : ℕ) (ι : Type*) [Fintype ι]
    {m : ℕ} (h : m ≤ p) (T : EuclideanSpace ℝ ((Fin p → Fin n) × ι))
    (a : Fin p → Fin n) (i : ι) :
    finiteIsometryAverage (realTensorPrefixAction n p ι h) T (a, i) =
      (∑ σ : Equiv.Perm (Fin m), T (a ∘ prefixFinPermHom h σ, i)) / m.factorial := by
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : (Fin p → Fin n) × ι => ℝ) (a, i))
    ((Fintype.card (Equiv.Perm (Fin m)) : ℝ)⁻¹ •
      ∑ σ, realTensorPrefixAction n p ι h σ T) = _
  rw [map_smul, map_sum, Fintype.card_perm, Fintype.card_fin]
  change (m.factorial : ℝ)⁻¹ * (∑ σ : Equiv.Perm (Fin m), T (a ∘ prefixFinPermHom h σ, i)) = _
  ring

theorem realCoordinateAverage_absorb_prefix (n p : ℕ) (ι : Type*) [Fintype ι]
    {m : ℕ} (h : m ≤ p) (T : EuclideanSpace ℝ ((Fin p → Fin n) × ι)) :
    finiteIsometryAverage (realCoordinatePermutationAction n p ι)
      (finiteIsometryAverage (realTensorPrefixAction n p ι h) T) =
        finiteIsometryAverage (realCoordinatePermutationAction n p ι) T :=
  finiteIsometryAverage_absorb (realCoordinatePermutationAction n p ι) (prefixFinPermHom h) T

theorem realTensorPrefixAverage_absorb (n p : ℕ) (ι : Type*) [Fintype ι]
    {d m : ℕ} (hd : d ≤ m) (hm : m ≤ p)
    (T : EuclideanSpace ℝ ((Fin p → Fin n) × ι)) :
    finiteIsometryAverage (realTensorPrefixAction n p ι hm)
      (finiteIsometryAverage (realTensorPrefixAction n p ι (hd.trans hm)) T) =
        finiteIsometryAverage (realTensorPrefixAction n p ι hm) T := by
  have he : (realTensorPrefixAction n p ι hm).comp (prefixFinPermHom hd) =
      realTensorPrefixAction n p ι (hd.trans hm) := by
    unfold realTensorPrefixAction
    rw [MonoidHom.comp_assoc, prefixFinPermHom_comp]
  rw [← he]
  exact finiteIsometryAverage_absorb (realTensorPrefixAction n p ι hm) (prefixFinPermHom hd) T

end KLS
end

#print axioms KLS.prefixFinPermHom_apply_prefix
#print axioms KLS.prefixFinPermHom_apply_suffix
#print axioms KLS.realCoordinateAverage_absorb_prefix
