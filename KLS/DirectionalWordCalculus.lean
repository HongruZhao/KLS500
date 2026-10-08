import KLS.WeightedDiffusionCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Data.List.GetD

/-! Actual iterated directional derivatives and the exact finite Leibniz
formula for one linear factor. The omitted-direction sum retains the order
of every remaining derivative. No commutation or Taylor premise is assumed. -/

open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : Inhabited E := ⟨0⟩

def directionalWordDerivative (f : E → ℝ) : List E → E → ℝ
  | [] => f
  | v :: vs => fun x => fderiv ℝ (directionalWordDerivative f vs) x v

@[simp] theorem directionalWordDerivative_nil (f : E → ℝ) :
    directionalWordDerivative f [] = f := rfl

@[simp] theorem directionalWordDerivative_cons (f : E → ℝ) (v : E) (vs : List E) (x : E) :
    directionalWordDerivative f (v :: vs) x =
      fderiv ℝ (directionalWordDerivative f vs) x v := rfl

theorem contDiff_directionalWordDerivative {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (vs : List E) :
    ContDiff ℝ (⊤ : ℕ∞) (directionalWordDerivative f vs) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem directionalWordDerivative_linear_mul {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : E →L[ℝ] ℝ) (vs : List E) (x : E) :
    directionalWordDerivative (fun y => l y * f y) vs x =
      l x * directionalWordDerivative f vs x +
        ∑ k ∈ Finset.range vs.length,
          l (vs[k]!) * directionalWordDerivative f (vs.eraseIdx k) x := by
  induction vs generalizing x with
  | nil => simp
  | cons v vs ih =>
    have hD := contDiff_directionalWordDerivative hf vs
    have hR (k : ℕ) := contDiff_directionalWordDerivative hf (vs.eraseIdx k)
    have he : directionalWordDerivative (fun y => l y * f y) vs =
        fun y => l y * directionalWordDerivative f vs y +
          ∑ k ∈ Finset.range vs.length,
            l (vs[k]!) * directionalWordDerivative f (vs.eraseIdx k) y := funext ih
    rw [directionalWordDerivative_cons, he]
    have hd := (l.hasFDerivAt.mul
      ((hD.differentiable (by simp)) x).hasFDerivAt).add
        (HasFDerivAt.fun_sum (u := Finset.range vs.length) (fun k _ =>
          (((hR k).differentiable (by simp)) x).hasFDerivAt.const_mul (l (vs[k]!))))
    change HasFDerivAt (fun y => l y * directionalWordDerivative f vs y +
      ∑ k ∈ Finset.range vs.length,
        l (vs[k]!) * directionalWordDerivative f (vs.eraseIdx k) y) _ x at hd
    rw [hd.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, _root_.sum_apply,
      smul_eq_mul, directionalWordDerivative_cons, List.length_cons,
      Finset.sum_range_succ', List.getElem!_cons_zero, List.eraseIdx_cons_zero,
      List.getElem!_cons_succ, List.eraseIdx_cons_succ]
    ring

/-- At zero exactly one derivative hits the linear factor. The full mixed
direction formula is an actual omitted-direction sum. -/
theorem directionalWordDerivative_linear_mul_zero {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : E →L[ℝ] ℝ) (vs : List E) :
    directionalWordDerivative (fun y => l y * f y) vs 0 =
      ∑ k ∈ Finset.range vs.length,
        l (vs[k]!) * directionalWordDerivative f (vs.eraseIdx k) 0 := by
  simpa using directionalWordDerivative_linear_mul hf l vs (0 : E)

end KLS
end

#print axioms KLS.directionalWordDerivative_linear_mul
#print axioms KLS.directionalWordDerivative_linear_mul_zero
