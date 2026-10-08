import OptVarianceEnergy

/-! Global positivity rules out a positive variance energy. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace KLS.ConstantReduction

theorem varianceODEEnergy_nonpos_of_initial_deriv_neg {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hpos : ∀ t, 0<v t)
    (hsecond : ∀ t, deriv (deriv v) t≤6*(v t)^2)
    (hderiv : deriv v 0<0) : varianceODEEnergy v 0≤0 := by
  by_contra hn
  have hE0 : 0<varianceODEEnergy v 0 := lt_of_not_ge hn
  have hglobal : ∀ t, 0≤t → deriv v t<0 := by
    intro t ht
    by_contra hd
    obtain ⟨b, hb0, hbt, hbzero, hbefore⟩ := exists_first_zero_of_nonneg
      (hv.continuous_deriv (by norm_num)) hderiv ht (le_of_not_gt hd)
    have hmono := varianceODEEnergy_monotoneOn hv hsecond (a:=0) (b:=b) (by
      intro s hs
      rcases lt_or_eq_of_le hs.2 with hsb|rfl
      · exact (hbefore s ⟨hs.1, hsb⟩).le
      · exact hbzero.le)
    have hE := hmono ⟨le_rfl,hb0.le⟩ ⟨hb0.le,le_rfl⟩ hb0.le
    dsimp only [varianceODEEnergy] at hE hE0
    rw [hbzero] at hE
    nlinarith [pow_pos (hpos b) 3]
  have henergy : ∀ t, 0≤t → varianceODEEnergy v 0≤varianceODEEnergy v t := by
    intro t ht
    exact (varianceODEEnergy_monotoneOn hv hsecond (a:=0) (b:=t)
      (fun s hs => (hglobal s hs.1).le)) ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩ ht
  let δ : ℝ := Real.sqrt (varianceODEEnergy v 0)
  have hδ : 0<δ := Real.sqrt_pos.mpr hE0
  have hδsq : δ^2=varianceODEEnergy v 0 := Real.sq_sqrt hE0.le
  have hslope : ∀ t, 0≤t → deriv v t≤-δ := by
    intro t ht
    have hE := henergy t ht
    have hd := hglobal t ht
    have hds : δ^2≤(-deriv v t)^2 := by
      dsimp only [varianceODEEnergy] at hE hδsq
      nlinarith [pow_pos (hpos t) 3]
    have hh := (sq_le_sq₀ hδ.le (neg_nonneg.mpr hd.le)).mp hds
    linarith
  let g : ℝ → ℝ := fun t => v t+δ*t
  have hg : ∀ t, HasDerivAt g (deriv v t+δ) t := by
    intro t
    convert (hv.differentiable (by norm_num) t).hasDerivAt.add
      ((hasDerivAt_id t).const_mul δ) using 1 <;> simp [g, funext_iff]
  have hanti : AntitoneOn g (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hg t).deriv]
    have hh := hslope t (interior_subset ht)
    linarith
  let T : ℝ := v 0/δ+1
  have hT : 0≤T := by have hv0 := hpos 0; dsimp [T]; positivity
  have hbound := hanti (by simp : (0 : ℝ)∈Ici 0) (show T∈Ici 0 from hT) hT
  have hmul : δ*T=v 0+δ := by
    dsimp [T]
    field_simp
  have hp := hpos T
  dsimp only [g] at hbound
  rw [hmul] at hbound
  nlinarith

end KLS.ConstantReduction
end
