import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! An energy identity for a positive variance satisfying the quadratic
variance differential inequality. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace KLS.ConstantReduction

def varianceODEEnergy (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  (deriv v t)^2 - 4*(v t)^3

theorem hasDerivAt_varianceODEEnergy {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (t : ℝ) :
    HasDerivAt (varianceODEEnergy v)
      (2*deriv v t*(deriv (deriv v) t-6*(v t)^2)) t := by
  have hD := (hv.differentiable_deriv_two t).hasDerivAt
  have hV := (hv.differentiable (by norm_num) t).hasDerivAt
  convert (hD.pow 2).sub ((hV.pow 3).const_mul 4) using 1
  · funext s
    dsimp only [varianceODEEnergy, Pi.sub_apply, Pi.pow_apply]
  · ring

theorem varianceODEEnergy_monotoneOn {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hsecond : ∀ t, deriv (deriv v) t ≤ 6*(v t)^2)
    {a b : ℝ} (hneg : ∀ t ∈ Icc a b, deriv v t ≤ 0) :
    MonotoneOn (varianceODEEnergy v) (Icc a b) := by
  have hd : Differentiable ℝ (varianceODEEnergy v) :=
    fun t => (hasDerivAt_varianceODEEnergy hv t).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hd.continuous.continuousOn
    hd.differentiableOn
  intro t ht
  rw [(hasDerivAt_varianceODEEnergy hv t).deriv]
  have ht' : t ∈ Icc a b := interior_subset ht
  exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
    (by norm_num) (hneg t ht')) (sub_nonpos.mpr (hsecond t))

/-- The first zero of a continuous derivative on a compact interval. -/
theorem exists_first_zero_of_nonneg {d : ℝ → ℝ} (hd : Continuous d)
    (h0 : d 0 < 0) {T : ℝ} (hT : 0 ≤ T) (hpos : 0 ≤ d T) :
    ∃ b, 0 < b ∧ b ≤ T ∧ d b=0 ∧ ∀ t ∈ Ico 0 b, d t<0 := by
  let s : Set ℝ := Icc 0 T ∩ d ⁻¹' Ici 0
  have hs : IsCompact s := isCompact_Icc.inter_right (isClosed_Ici.preimage hd)
  have hsne : s.Nonempty := ⟨T, ⟨⟨hT, le_rfl⟩, hpos⟩⟩
  obtain ⟨b, hb⟩ := hs.exists_isLeast hsne
  have hb0 : 0 < b := by
    have hbn := hb.1.1.1
    have hbne : b≠0 := by
      intro hz
      have hh : 0≤d b := hb.1.2
      rw [hz] at hh
      linarith
    exact lt_of_le_of_ne hbn (Ne.symm hbne)
  have hbefore : ∀ t ∈ Ico 0 b, d t<0 := by
    intro t ht
    by_contra hn
    have hts : t∈s := ⟨⟨ht.1, ht.2.le.trans hb.1.1.2⟩, le_of_not_gt hn⟩
    have hh := hb.2 hts
    exact (not_le_of_gt ht.2) hh
  have hbzero : d b=0 := by
    apply le_antisymm _ hb.1.2
    by_contra hn
    have hbpos : 0<d b := lt_of_not_ge hn
    have hevent : ∀ᶠ t in 𝓝 b, 0<d t := hd.continuousAt.eventually (lt_mem_nhds hbpos)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp hevent
    let t : ℝ := b - min b δ / 2
    have hm : 0<min b δ := lt_min hb0 hδ
    have htb : t<b := by dsimp [t]; linarith
    have ht0 : 0≤t := by dsimp [t]; have := min_le_left b δ; linarith
    have hdist : dist t b<δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr htb.le)]
      dsimp [t]
      have := min_le_right b δ
      linarith
    have hp := hδsub hdist
    have hn' := hbefore t ⟨ht0, htb⟩
    linarith
  exact ⟨b, hb0, hb.1.1.2, hbzero, hbefore⟩

end KLS.ConstantReduction
end
