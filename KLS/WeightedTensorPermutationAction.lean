import KLS.WeightedIterationAdjacentSwap
import KLS.FinitePermutationWords
import Mathlib.Data.Fin.Tuple.Basic

/-! The genuine action of coordinate permutations on a prefix of the actual
nested tensor index. The remaining suffix is fixed. -/

open MeasureTheory
noncomputable section
namespace KLS

def tensorPrefixEquiv (n : ℕ) (ι : Type*) (r : ℕ) :
    (q : ℕ) → WeightedIterationIndex n ι (r + q) ≃
      (Fin q → Fin n) × WeightedIterationIndex n ι r
  | 0 =>
    { toFun := fun i => (Fin.elim0, i)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := fun _ => Prod.ext (Subsingleton.elim _ _) rfl }
  | q + 1 =>
    (Equiv.prodCongr (Equiv.refl (Fin n)) (tensorPrefixEquiv n ι r q)).trans
      ((Equiv.prodAssoc (Fin n) (Fin q → Fin n) (WeightedIterationIndex n ι r)).symm.trans
        (Equiv.prodCongr (Fin.consEquiv (fun _ : Fin (q + 1) => Fin n)) (Equiv.refl _)))

@[simp] theorem tensorPrefixEquiv_zero_apply (n : ℕ) (ι : Type*) (r : ℕ)
    (i : WeightedIterationIndex n ι r) : tensorPrefixEquiv n ι r 0 i = (Fin.elim0, i) := rfl

@[simp] theorem tensorPrefixEquiv_succ_apply (n : ℕ) (ι : Type*) (r q : ℕ)
    (j : Fin n) (i : WeightedIterationIndex n ι (r + q)) :
    tensorPrefixEquiv n ι r (q + 1) (j, i) =
      (Fin.cons j (tensorPrefixEquiv n ι r q i).1, (tensorPrefixEquiv n ι r q i).2) := rfl

def tensorCoordinatePermHom (J T : Type*) (q : ℕ) :
    Equiv.Perm (Fin q) →* Equiv.Perm ((Fin q → J) × T) where
  toFun σ := Equiv.prodCongr (Equiv.arrowCongr σ (Equiv.refl J)) (Equiv.refl T)
  map_one' := by
    ext x <;> rfl
  map_mul' σ τ := by
    ext x <;> rfl

@[simp] theorem tensorCoordinatePermHom_apply {J T : Type*} {q : ℕ}
    (σ : Equiv.Perm (Fin q)) (x : (Fin q → J) × T) :
    tensorCoordinatePermHom J T q σ x = (fun j => x.1 (σ.symm j), x.2) := rfl

def tensorPrefixPermutationHom (n : ℕ) (ι : Type*) (r q : ℕ) :
    Equiv.Perm (Fin q) →* Equiv.Perm (WeightedIterationIndex n ι (r + q)) :=
  (tensorPrefixEquiv n ι r q).symm.permCongrHom.toMonoidHom.comp
    (tensorCoordinatePermHom (Fin n) (WeightedIterationIndex n ι r) q)

@[simp] theorem tensorPrefixPermutationHom_apply (n : ℕ) (ι : Type*) (r q : ℕ)
    (σ : Equiv.Perm (Fin q)) (x : WeightedIterationIndex n ι (r + q)) :
    tensorPrefixPermutationHom n ι r q σ x = (tensorPrefixEquiv n ι r q).symm
      (fun j => (tensorPrefixEquiv n ι r q x).1 (σ.symm j), (tensorPrefixEquiv n ι r q x).2) := rfl

variable {Ω : Type*} [MeasurableSpace Ω]

def finiteL2ReindexHom (μ : Measure Ω) (ι : Type*) [Fintype ι] :
    Equiv.Perm ι →* (CenteredL2.Family μ ι ≃ₗᵢ[ℝ] CenteredL2.Family μ ι) where
  toFun e := finiteL2Reindex e
  map_one' := by
    ext g i
    rfl
  map_mul' e f := by
    ext g i
    rfl

/-- The concrete-product wrapper chooses the actual centered-gradient carrier. -/
def weightedGradientPrefixPermutationHom (n : ℕ) (ι : Type*) (r q : ℕ) :
    Equiv.Perm (Fin (q + 1)) →* Equiv.Perm (Fin n × WeightedIterationIndex n ι (r + q)) :=
  tensorPrefixPermutationHom n ι r (q + 1)

def weightedGradientPermutationAction (μ : Measure Ω) (n : ℕ) (ι : Type*) [Fintype ι]
    (r q : ℕ) :
    Equiv.Perm (Fin (q + 1)) →*
      (CenteredL2.Family μ (Fin n × WeightedIterationIndex n ι (r + q)) ≃ₗᵢ[ℝ]
        CenteredL2.Family μ (Fin n × WeightedIterationIndex n ι (r + q))) :=
  (finiteL2ReindexHom μ _).comp (weightedGradientPrefixPermutationHom n ι r q)

end KLS
end

#print axioms KLS.tensorPrefixEquiv
#print axioms KLS.weightedGradientPermutationAction
