import KLS.TiltCumulantHierarchy
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Finite composition jets depend continuously on the actual inner jets.
The outer derivatives are evaluated at a common actual value. -/

open Filter
open scoped Topology ContDiff BigOperators
noncomputable section
namespace KLS

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem tendsto_taylorComp_fixed_outer {l : Filter ι}
    {p : ι → FormalMultilinearSeries ℝ E F} {p₀ : FormalMultilinearSeries ℝ E F}
    (q : FormalMultilinearSeries ℝ F G) {m : ℕ}
    (hp : ∀ k ≤ m, Tendsto (fun a => p a k) l (𝓝 (p₀ k))) :
    Tendsto (fun a => q.taylorComp (p a) m) l (𝓝 (q.taylorComp p₀ m)) := by
  unfold FormalMultilinearSeries.taylorComp
  apply tendsto_finsetSum
  intro c _
  have hparts : Tendsto (fun a j => p a (c.partSize j)) l
      (𝓝 (fun j => p₀ (c.partSize j))) :=
    tendsto_pi_nhds.mpr (fun j => hp _ (c.partSize_le j))
  exact ((c.compAlongOrderedFinpartitionL ℝ E F G (q c.length)).cont.tendsto _).comp hparts

theorem tendsto_iteratedFDeriv_comp_common_value {l : Filter ι}
    {f : ι → E → F} {f₀ : E → F} {g : F → G} {x : E} {y : F} {m : ℕ}
    (hf : ∀ a, ContDiffAt ℝ m (f a) x) (hf₀ : ContDiffAt ℝ m f₀ x)
    (hg : ContDiffAt ℝ m g y) (hvalue : ∀ a, f a x = y) (hvalue₀ : f₀ x = y)
    (hjets : ∀ k ≤ m, Tendsto (fun a => iteratedFDeriv ℝ k (f a) x) l
      (𝓝 (iteratedFDeriv ℝ k f₀ x))) :
    Tendsto (fun a => iteratedFDeriv ℝ m (g ∘ f a) x) l
      (𝓝 (iteratedFDeriv ℝ m (g ∘ f₀) x)) := by
  have hcomp (a : ι) : iteratedFDeriv ℝ m (g ∘ f a) x =
      (ftaylorSeries ℝ g y).taylorComp (ftaylorSeries ℝ (f a) x) m := by
    have hga : ContDiffAt ℝ m g (f a x) := by simpa only [hvalue a] using hg
    simpa only [hvalue a] using iteratedFDeriv_comp hga (hf a) (by exact_mod_cast le_refl m)
  have hcomp₀ : iteratedFDeriv ℝ m (g ∘ f₀) x =
      (ftaylorSeries ℝ g y).taylorComp (ftaylorSeries ℝ f₀ x) m := by
    have hg₀ : ContDiffAt ℝ m g (f₀ x) := by simpa only [hvalue₀] using hg
    simpa only [hvalue₀] using iteratedFDeriv_comp hg₀ hf₀ (by exact_mod_cast le_refl m)
  simp_rw [hcomp, hcomp₀]
  exact tendsto_taylorComp_fixed_outer (ftaylorSeries ℝ g y) hjets

end KLS
end
