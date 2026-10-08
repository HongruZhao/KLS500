import KLS.MomentBoundedUniformHarmonicLimit

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS

/-- Sequential compactness at zero scale yields an actual small-scale
uniform approximation threshold. All approximants preserve the predicate P. -/
theorem exists_uniform_approximation_threshold
    {X α : Type*} (scale : X → ℝ) (F : X → α → ℝ) (S : Set α) (P : (α → ℝ) → Prop)
    (hpos : ∀ d, 0 < scale d)
    (hcompact : ∀ d : ℕ → X, Tendsto (fun j => scale (d j)) atTop (𝓝 0) →
      ∃ (h : α → ℝ) (σ : ℕ → ℕ), StrictMono σ ∧ P h ∧
        TendstoUniformlyOn (fun j => F (d (σ j))) h atTop S)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : X, scale d < δ →
      ∃ h : α → ℝ, P h ∧ ∀ x ∈ S, |F d x - h x| ≤ η := by
  classical
  by_contra hh
  push Not at hh
  choose d hd hf using fun j : ℕ => hh (1 / ((j : ℝ) + 1)) (by positivity)
  have hlim : Tendsto (fun j => scale (d j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => (hpos (d j)).le) (fun j => (hd j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨h, σ, hσ, hP, hconv⟩ := hcompact d hlim
  have hnear := Metric.tendstoUniformlyOn_iff.mp hconv η hη
  obtain ⟨j, hj⟩ := hnear.exists
  obtain ⟨x, hx, hbad⟩ := hf (σ j) h hP
  have hgood := hj x hx
  rw [Real.dist_eq, abs_sub_comm] at hgood
  linarith

end KLS
end
