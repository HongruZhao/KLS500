import KLS.WeightedDiffusionCommutator

/-!
# Third and fourth coordinate derivative permutations

These identities use actual iterated Fréchet derivatives and explicit C³ or
C⁴ regularity. They supply the derivative permutations in Hessian evolution.
-/

open InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Exchange the outer derivative with the first Hessian coordinate. -/
lemma coordinateDerivative_hessian_swap {φ : Space n → ℝ} (hφ : ContDiff ℝ 3 φ)
    (i a b : Fin n) (x : Space n) :
    coordinateDerivative (fun y => coordinateHessian φ y a b) i x =
      coordinateDerivative (fun y => coordinateHessian φ y i b) a x := by
  have hb : ContDiff ℝ 2 (coordinateDerivative φ b) :=
    contDiff_coordinateDerivative hφ (by norm_num) b
  exact ((coordinateHessian_symmetric hb x).apply i a).symm

/-- Move an outer derivative to the second Hessian coordinate. -/
lemma coordinateDerivative_hessian_cycle {φ : Space n → ℝ} (hφ : ContDiff ℝ 3 φ)
    (i a b : Fin n) (x : Space n) :
    coordinateDerivative (fun y => coordinateHessian φ y a b) i x =
      coordinateDerivative (fun y => coordinateHessian φ y i a) b x := by
  have hab : (fun y => coordinateHessian φ y a b) =
      fun y => coordinateHessian φ y b a := by
    funext y
    exact ((coordinateHessian_symmetric (hφ.of_le (by norm_num)) y).apply a b).symm
  rw [hab]
  exact coordinateDerivative_hessian_swap hφ i b a x

/-- Exchange the Hessian of a Hessian entry with the original coordinate pair. -/
lemma coordinateHessian_hessian_exchange {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (i j a b : Fin n) (x : Space n) :
    coordinateHessian (fun y => coordinateHessian φ y a b) x i j =
      coordinateHessian (fun y => coordinateHessian φ y i j) x a b := by
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by norm_num)
  have hfirst : coordinateDerivative (fun y => coordinateHessian φ y a b) j =
      coordinateDerivative (fun y => coordinateHessian φ y j b) a :=
    funext (coordinateDerivative_hessian_swap hφ3 j a b)
  change coordinateDerivative (coordinateDerivative (fun y => coordinateHessian φ y a b) j) i x = _
  rw [hfirst]
  have hentry : ContDiff ℝ 2 (fun y => coordinateHessian φ y j b) :=
    contDiff_coordinateHessian hφ (by norm_num) j b
  have hs := ((coordinateHessian_symmetric hentry x).apply i a).symm
  change coordinateDerivative (coordinateDerivative (fun y => coordinateHessian φ y j b) a) i x =
    coordinateDerivative (coordinateDerivative (fun y => coordinateHessian φ y j b) i) a x at hs
  rw [hs]
  have hsecond : coordinateDerivative (fun y => coordinateHessian φ y j b) i =
      coordinateDerivative (fun y => coordinateHessian φ y i j) b :=
    funext (coordinateDerivative_hessian_cycle hφ3 i j b)
  rw [hsecond]
  rfl

end KLS
end

#print axioms KLS.coordinateDerivative_hessian_swap
#print axioms KLS.coordinateDerivative_hessian_cycle
#print axioms KLS.coordinateHessian_hessian_exchange
