import Mathlib

/-! Local mixed derivative identities. Only smoothness near the evaluation
point is required; the function need not have a global convergence domain. -/

open Set
open scoped ContDiff
noncomputable section
namespace KLS

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma iteratedFDeriv_comp_clm_of_contDiffAt {d : ℕ} {f : F → H}
    (L : E →L[ℝ] F) (x : E) (hf : ContDiffAt ℝ d f (L x)) :
    iteratedFDeriv ℝ d (f ∘ L) x =
      (iteratedFDeriv ℝ d f (L x)).compContinuousLinearMap (fun _ => L) := by
  have hw : ContDiffWithinAt ℝ d f univ (L x) := hf.contDiffWithinAt
  obtain ⟨U, hU, hxU, hfU⟩ := hw.contDiffOn' (m := (d : ℕ∞ω)) le_rfl (by simp)
  have hfU' : ContDiffOn ℝ d f U := by simpa using hfU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hh := L.iteratedFDerivWithin_comp_right hfU' hU.uniqueDiffOn hpre.uniqueDiffOn hxU
    (i := d) le_rfl
  rw [iteratedFDerivWithin_of_isOpen d hpre (show x ∈ L ⁻¹' U from hxU),
    iteratedFDerivWithin_of_isOpen d hU hxU] at hh
  exact hh

lemma iteratedFDeriv_directional_comp {d : ℕ} {f : F → ℝ}
    (L : E →L[ℝ] F) (x : E) (v : F) (hf : ContDiffAt ℝ (d + 1) f (L x))
    (m : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => fderiv ℝ f (L z) v) x m =
      iteratedFDeriv ℝ (d + 1) f (L x) (Fin.snoc (fun j => L (m j)) v) := by
  have hD : ContDiffAt ℝ d (fderiv ℝ f) (L x) := hf.fderiv_right (by simp)
  have hc : ContDiffAt ℝ d ((fderiv ℝ f) ∘ L) x :=
    hD.comp x L.contDiff.contDiffAt
  have he := (ContinuousLinearMap.apply ℝ ℝ v).iteratedFDeriv_comp_left hc (i := d) le_rfl
  change iteratedFDeriv ℝ d ((ContinuousLinearMap.apply ℝ ℝ v) ∘ ((fderiv ℝ f) ∘ L)) x m = _
  rw [he, iteratedFDeriv_comp_clm_of_contDiffAt L x hD,
    iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]
  rfl

end KLS
end
#print axioms KLS.iteratedFDeriv_comp_clm_of_contDiffAt
#print axioms KLS.iteratedFDeriv_directional_comp
