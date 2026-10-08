import OptSymmetricTensorPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Logic.Equiv.Fintype

/-! Diagonal evaluation detects every permutation-symmetric finite tensor. -/
open scoped BigOperators
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

def tensorExponent (a : Fin r → Fin n) : Fin n →₀ ℕ :=
  ∑ s, Finsupp.single (a s) 1

theorem tensorExponent_apply (a : Fin r → Fin n) (i : Fin n) :
    tensorExponent a i = Fintype.card {s : Fin r // a s = i} := by
  classical
  simp [tensorExponent, Finsupp.single_apply, Fintype.card_subtype,
    Finset.sum_boole]

theorem exists_perm_of_tensorExponent_eq {a b : Fin r → Fin n}
    (h : tensorExponent a = tensorExponent b) :
    ∃ σ : Equiv.Perm (Fin r), b ∘ σ = a := by
  classical
  have hc (i : Fin n) : Fintype.card {s : Fin r // a s = i} =
      Fintype.card {s : Fin r // b s = i} := by
    rw [← tensorExponent_apply, ← tensorExponent_apply, h]
  let e (i : Fin n) := Fintype.equivOfCardEq (hc i)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext s
  exact Equiv.ofFiberEquiv_map e s

theorem prod_X_eq_tensorExponent (a : Fin r → Fin n) :
    (∏ s, MvPolynomial.X (a s) : MvPolynomial (Fin n) ℝ) =
      MvPolynomial.monomial (tensorExponent a) 1 := by
  classical
  unfold tensorExponent
  have h (S : Finset (Fin r)) :
      (∏ s ∈ S, MvPolynomial.X (a s) : MvPolynomial (Fin n) ℝ) =
        MvPolynomial.monomial (∑ s ∈ S, Finsupp.single (a s) 1) 1 := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert s S hs ih =>
      rw [Finset.prod_insert hs, Finset.sum_insert hs, ih]
      change MvPolynomial.monomial (Finsupp.single (a s) 1) 1 * _ = _
      rw [MvPolynomial.monomial_mul_monomial, one_mul]
  exact h Finset.univ

theorem tensorPolynomial_eq_zero_of_symmetric
    (T : (Fin r → Fin n) → ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) a, T (a ∘ σ) = T a)
    (hzero : ∀ x : Space n, tensorPolynomial T x = 0) : T = 0 := by
  classical
  let P : MvPolynomial (Fin n) ℝ :=
    ∑ a, MvPolynomial.C (T a) * ∏ s, MvPolynomial.X (a s)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    simpa [P, tensorPolynomial, map_sum, map_mul, map_prod] using
      hzero ((WithLp.equiv 2 (Fin n → ℝ)).symm x)
  funext a
  have hcoef := congrArg (fun p : MvPolynomial (Fin n) ℝ =>
    p.coeff (tensorExponent a)) hP
  have ht (b : Fin r → Fin n) (hb : tensorExponent b = tensorExponent a) : T b = T a := by
    obtain ⟨σ, hσ⟩ := exists_perm_of_tensorExponent_eq hb
    simpa [hσ] using hsym σ a
  let S := Finset.univ.filter (fun b : Fin r → Fin n =>
    tensorExponent b = tensorExponent a)
  have hc0 : (∑ b ∈ S, T b) = 0 := by
    simpa only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      prod_X_eq_tensorExponent, MvPolynomial.coeff_monomial, mul_ite,
      mul_one, mul_zero, ← Finset.sum_filter, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, S] using hcoef
  have heq : (∑ b ∈ S, T b) = ∑ _b ∈ S, T a := by
    apply Finset.sum_congr rfl
    intro b hb
    exact ht b (Finset.mem_filter.mp hb).2
  rw [heq, Finset.sum_const, nsmul_eq_mul] at hc0
  have hn : (0 : ℝ) < (Finset.univ.filter (fun b : Fin r → Fin n =>
      tensorExponent b = tensorExponent a)).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨a, by simp⟩
  exact (mul_eq_zero.mp hc0).resolve_left hn.ne'

theorem tensorPolynomial_injective_of_symmetric
    (T U : (Fin r → Fin n) → ℝ)
    (hT : ∀ (σ : Equiv.Perm (Fin r)) a, T (a ∘ σ) = T a)
    (hU : ∀ (σ : Equiv.Perm (Fin r)) a, U (a ∘ σ) = U a)
    (h : ∀ x : Space n, tensorPolynomial T x = tensorPolynomial U x) : T = U := by
  have hz : T - U = 0 := tensorPolynomial_eq_zero_of_symmetric (T - U)
    (by intro σ a; simp only [Pi.sub_apply, hT, hU]) (by
      intro x
      simp only [tensorPolynomial, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (h x))
  exact sub_eq_zero.mp hz

theorem exists_tensorPolynomial_ne_zero_of_symmetric
    (T : (Fin r → Fin n) → ℝ)
    (hT : ∀ (σ : Equiv.Perm (Fin r)) a, T (a ∘ σ) = T a)
    (hne : T ≠ 0) : ∃ x : Space n, tensorPolynomial T x ≠ 0 := by
  by_contra! h
  exact hne (tensorPolynomial_eq_zero_of_symmetric T hT h)

end KLS.TensorEnergy
end
