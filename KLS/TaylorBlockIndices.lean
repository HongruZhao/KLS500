import KLS.FinitePrefixPermutation

/-! Literal contiguous coordinate blocks and their behavior under actual
prefix permutations. All later tensor identifications use these index maps. -/

noncomputable section
namespace KLS

def finBlockTuple {J : Type*} {p : ℕ} (a : Fin p → J) (s q : ℕ) (h : s + q ≤ p) :
    Fin q → J := fun j => a ⟨s + j.val, by omega⟩

theorem finBlockTuple_zero {J : Type*} {p q : ℕ} (a : Fin p → J) (h : 0 + q ≤ p) :
    finBlockTuple a 0 q h = a ∘ Fin.castLE (by omega : q ≤ p) := by
  funext j
  apply congrArg a
  apply Fin.ext
  simp

theorem finBlockTuple_tail {J : Type*} {p s q : ℕ} (a : Fin p → J) (h : s + (q + 1) ≤ p) :
    Fin.tail (finBlockTuple a s (q + 1) h) = finBlockTuple a (s + 1) q (by omega) := by
  funext j
  apply congrArg a
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

theorem finBlockTuple_head {J : Type*} {p s q : ℕ} (a : Fin p → J) (h : s + (q + 1) ≤ p) :
    finBlockTuple a s (q + 1) h 0 = a ⟨s, by omega⟩ := by
  apply congrArg a
  apply Fin.ext
  simp

theorem finBlockTuple_init {J : Type*} {p s q : ℕ} (a : Fin p → J) (h : s + (q + 1) ≤ p) :
    Fin.init (finBlockTuple a s (q + 1) h) = finBlockTuple a s q (by omega) := rfl

theorem finBlockTuple_last {J : Type*} {p s q : ℕ} (a : Fin p → J) (h : s + (q + 1) ≤ p) :
    finBlockTuple a s (q + 1) h (Fin.last q) = a ⟨s + q, by omega⟩ := rfl

theorem finBlockTuple_prefix_permutation {J : Type*} {p d m : ℕ}
    (a : Fin p → J) (hd : d ≤ m) (hm : m ≤ p) (σ : Equiv.Perm (Fin m)) :
    finBlockTuple (a ∘ prefixFinPermHom hm σ) 0 d (by omega) =
      fun j => finBlockTuple a 0 m (by omega) (σ (Fin.castLE hd j)) := by
  funext j
  change a (prefixFinPermHom hm σ ⟨0 + j.val, by omega⟩) = _
  have he : (⟨0 + j.val, by omega⟩ : Fin p) = Fin.castLE hm (Fin.castLE hd j) := by
    apply Fin.ext
    simp
  rw [he, prefixFinPermHom_apply_castLE]
  apply congrArg a
  apply Fin.ext
  simp

theorem finBlockTuple_suffix_permutation {J : Type*} {p s q m : ℕ}
    (a : Fin p → J) (h : s + q ≤ p) (hm : m ≤ p) (hms : m ≤ s)
    (σ : Equiv.Perm (Fin m)) :
    finBlockTuple (a ∘ prefixFinPermHom hm σ) s q h = finBlockTuple a s q h := by
  funext j
  change a (prefixFinPermHom hm σ ⟨s + j.val, by omega⟩) = _
  rw [prefixFinPermHom_apply_of_le hm σ _ (by change m ≤ s + j.val; omega)]
  rfl

theorem finBlockTuple_head_prefix_permutation {J : Type*} {p d : ℕ}
    (a : Fin p → J) (h : d + 1 ≤ p) (σ : Equiv.Perm (Fin (d + 1))) :
    (a ∘ prefixFinPermHom h σ) ⟨d, by omega⟩ =
      finBlockTuple a 0 (d + 1) (by omega) (σ (Fin.last d)) := by
  change a (prefixFinPermHom h σ (Fin.castLE h (Fin.last d))) = _
  rw [prefixFinPermHom_apply_castLE]
  apply congrArg a
  apply Fin.ext
  simp

@[simp] theorem tensorPrefixEquiv_succ_symm_apply (n : ℕ) (ι : Type*) (r q : ℕ)
    (a : Fin (q + 1) → Fin n) (i : WeightedIterationIndex n ι r) :
    (tensorPrefixEquiv n ι r (q + 1)).symm (a, i) =
      (a 0, (tensorPrefixEquiv n ι r q).symm (Fin.tail a, i)) := rfl

end KLS
end

#print axioms KLS.finBlockTuple_prefix_permutation
#print axioms KLS.finBlockTuple_suffix_permutation
#print axioms KLS.tensorPrefixEquiv_succ_symm_apply
