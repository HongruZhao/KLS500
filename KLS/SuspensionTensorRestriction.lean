import Mathlib

/-! Finite tensor bookkeeping for suspension. These lemmas restrict a genuine
sum of squares to the disjoint pure-copy blocks. The mixed-entry identity is
an explicit input here; the analytic suspension theorem must derive it. -/

open scoped BigOperators
noncomputable section
namespace KLS

variable {I J D : Type*}

def pureSuspensionBlock (p : I × (D → J)) : D → Option (I × J) :=
  fun k => some (p.1, p.2 k)

lemma pureSuspensionBlock_injective [Nonempty D] :
    Function.Injective (pureSuspensionBlock (I := I) (J := J) (D := D)) := by
  intro p q h
  have hh (k : D) : (p.1, p.2 k) = (q.1, q.2 k) :=
    Option.some.inj (congrFun h k)
  apply Prod.ext
  · exact congrArg (fun x : I × J => x.1) (hh Classical.ofNonempty)
  · funext k
    exact congrArg (fun x : I × J => x.2) (hh k)

theorem sum_sq_pureSuspensionBlocks_le [Fintype I] [Fintype J] [Fintype D] [DecidableEq D] [Nonempty D]
    (T : (D → Option (I × J)) → ℝ) :
    (∑ i : I, ∑ a : D → J, T (pureSuspensionBlock (i, a)) ^ 2) ≤
      ∑ b : D → Option (I × J), T b ^ 2 := by
  classical
  have h := Finset.sum_le_sum_of_injOn
    (f := fun p : I × (D → J) => T (pureSuspensionBlock p) ^ 2)
    (g := fun a : D → Option (I × J) => T a ^ 2)
    (s := Finset.univ) (t := Finset.univ) pureSuspensionBlock
    pureSuspensionBlock_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
    (fun a _ _ => sq_nonneg (T a))
  simpa only [Fintype.sum_prod_type] using h

theorem card_mul_sq_sum_le_of_pureSuspensionEntries
    [Fintype I] [Fintype J] [Fintype D] [DecidableEq D] [Nonempty D]
    (T : (D → Option (I × J)) → ℝ) (A : (D → J) → ℝ) (c : ℝ)
    (hentry : ∀ i a, T (pureSuspensionBlock (i, a)) = c * A a) :
    (Fintype.card I : ℝ) * c ^ 2 * (∑ a, A a ^ 2) ≤
      ∑ b : D → Option (I × J), T b ^ 2 := by
  have h := sum_sq_pureSuspensionBlocks_le T
  simp_rw [hentry, mul_pow, ← Finset.mul_sum] at h
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc, mul_left_comm] using h

lemma suspension_normalizing_factor {N σ a : ℝ} (hN : 0 < N) (hσ : σ ≠ 0) :
    N * (a / (σ * Real.sqrt N)) ^ 2 = a ^ 2 / σ ^ 2 := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have hsq := Real.sq_sqrt hN.le
  field_simp
  nlinarith

theorem suspensionTensor_norm_bound {N d n : ℕ} (hN : 0 < N) (hd : 0 < d)
    (T : (Fin d → Option (Fin N × Fin n)) → ℝ) (A : (Fin d → Fin n) → ℝ)
    {σ : ℝ} (hσ : σ ≠ 0)
    (hentry : ∀ i a, T (pureSuspensionBlock (i, a)) =
      ((d.factorial : ℝ) / (σ * Real.sqrt N)) * A a) :
    ((d.factorial : ℝ) ^ 2 / σ ^ 2) * (∑ a, A a ^ 2) ≤
      ∑ b : Fin d → Option (Fin N × Fin n), T b ^ 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h := card_mul_sq_sum_le_of_pureSuspensionEntries T A
    ((d.factorial : ℝ) / (σ * Real.sqrt N)) hentry
  simp only [Fintype.card_fin] at h
  rw [suspension_normalizing_factor (by exact_mod_cast hN) hσ] at h
  exact h

/-- The vanishing Laplace variance removes the auxiliary factor after the
suspension estimate has been established at every positive rate. -/
theorem le_of_all_laplace_variance_factors {q b : ℝ} (hb : 0 ≤ b)
    (h : ∀ β : ℝ, 0 < β → q ≤ (1 + 2 / β ^ 2) * b) : q ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let β := Real.sqrt (2 * b / ε) + 1
  have hrad : 0 ≤ 2 * b / ε := div_nonneg (by positivity) hε.le
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ2 : 0 < β ^ 2 := sq_pos_of_pos hβ
  have hroot := Real.sq_sqrt hrad
  have hεid : (2 * b / ε) * ε = 2 * b := div_mul_cancel₀ _ hε.ne'
  have hbound : 2 * b / β ^ 2 ≤ ε := by
    apply (div_le_iff₀ hβ2).2
    dsimp [β]
    nlinarith [Real.sqrt_nonneg (2 * b / ε)]
  calc
    q ≤ (1 + 2 / β ^ 2) * b := h β hβ
    _ = b + 2 * b / β ^ 2 := by ring
    _ ≤ b + ε := by linarith

end KLS
end
#print axioms KLS.sum_sq_pureSuspensionBlocks_le
#print axioms KLS.suspensionTensor_norm_bound

#print axioms KLS.le_of_all_laplace_variance_factors
