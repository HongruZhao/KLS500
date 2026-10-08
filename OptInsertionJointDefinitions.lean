import OptMeanInsertionWords

/-! Exact first and mixed moments of independent insertion digits. -/
open Equiv
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

def insertionDigitCount (q i : ℕ) : ℝ :=
  (q+1 : ℝ)⁻¹ * ∑ p : Fin (q+1), if i < (p : ℕ) then 1 else 0

def insertionDigitJoint (q i : ℕ) : ℝ :=
  (q+1 : ℝ)⁻¹ * ∑ p : Fin (q+1), (p : ℝ)*(if i < (p : ℕ) then 1 else 0)

def insertionMeanCount : ℕ → ℕ → ℝ
  | 0, _ => 0
  | q+1, i => insertionDigitCount (q+1) i +
      if i = 0 then 0 else insertionMeanCount q (i-1)

def insertionJointMoment : ℕ → ℕ → ℝ
  | 0, _ => 0
  | q+1, i => insertionDigitJoint (q+1) i +
      ((q : ℝ)*(q+1)/4)*insertionDigitCount (q+1) i +
      ((q+1 : ℝ)/2)*(if i = 0 then 0 else insertionMeanCount q (i-1)) +
      (if i = 0 then 0 else insertionJointMoment q (i-1))

theorem insertionDigitCount_sum (q i : ℕ) :
    (∑ p : Fin (q+1), if i < (p : ℕ) then (1 : ℝ) else 0) =
      (q+1 : ℝ)*insertionDigitCount q i := by
  unfold insertionDigitCount
  have h : (q+1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem insertionDigitJoint_sum (q i : ℕ) :
    (∑ p : Fin (q+1), (p : ℝ)*(if i < (p : ℕ) then 1 else 0)) =
      (q+1 : ℝ)*insertionDigitJoint q i := by
  unfold insertionDigitJoint
  have h : (q+1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem exists_adjacentFinSwapWord_send_zero_exact_counts {q : ℕ} (p : Fin (q+1)) :
    ∃ v : List (Fin q), (v.map (adjacentFinSwap q)).prod 0 = p ∧
      v.length = (p : ℕ) ∧ ∀ i, v.count i = if (i : ℕ) < (p : ℕ) then 1 else 0 := by
  induction p using Fin.induction with
  | zero =>
    refine ⟨[], by rfl, rfl, ?_⟩
    intro i
    simp
  | succ i ih =>
    obtain ⟨v, hv, hlen, hcount⟩ := ih
    refine ⟨i :: v, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, hv]
      simp [adjacentFinSwap]
    · simp only [List.length_cons, hlen, Fin.val_castSucc, Fin.val_succ]
    · intro j
      by_cases hj : j = i
      · subst j
        simp [hcount]
      · have hj' : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
        have he : (j : ℕ) < (i : ℕ)+1 ↔ (j : ℕ) < (i : ℕ) := by omega
        simp [hcount, Ne.symm hj, he]

theorem count_map_succ_zero {q : ℕ} (w : List (Fin q)) :
    (w.map Fin.succ).count (0 : Fin (q+1)) = 0 := by
  apply List.count_eq_zero.mpr
  intro hz
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hz
  exact Fin.succ_ne_zero j hj

theorem sum_product_add_moments {A B : Type*} [Fintype A] [Fintype B]
    (u a : A → ℝ) (v b : B → ℝ) :
    (∑ z : A × B, (u z.1+v z.2)*(a z.1+b z.2)) =
      (Fintype.card B : ℝ)*(∑ x, u x*a x) +
      (∑ x, u x)*(∑ y, b y) + (∑ x, a x)*(∑ y, v y) +
      (Fintype.card A : ℝ)*(∑ y, v y*b y) := by
  rw [Fintype.sum_prod_type]
  simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end KLS.ConstantReduction
end
