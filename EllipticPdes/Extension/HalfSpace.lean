/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Cutoff
public import EllipticPdes.Extension.Reflect
public import EllipticPdes.Embedding.GagliardoNirenberg
public import EllipticPdes.Extension.Basic

/-!
# Half space and its interface

The extension of a Sobolev class across a flat boundary is by reflection, and what has to be
proved is that the reflected class has a weak gradient across the interface. The identity of a
weak gradient on the open half space applies only to test functions supported strictly inside
it, so the test function is first multiplied by `slabCut ℓ ε`, with `ℓ` the `j`-th coordinate,
and the slab is then let shrink.

Two terms survive the product rule. The one with the cutoff's own derivative vanishes
identically in the directions along the interface, since the cutoff depends on the `j`-th
coordinate alone. In the remaining direction it is the boundary term, and it vanishes in the
limit whenever the test function vanishes on the interface, which is exactly what the odd part
of a reflection does.

## Main declarations

* `EllipticPdes.Extension.halfSpace`: the open half space `{xⱼ > 0}`.
* `EllipticPdes.Extension.volume_interface`: the interface is null.
* `EllipticPdes.Extension.integral_partialD_of_ne`: no boundary term along the interface.
* `EllipticPdes.Extension.integral_partialD_of_eq`: none in the remaining direction either,
  for a test function vanishing on the interface.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)
open EllipticPdes.Embedding (HasWeakGradOn partialD_mul)

variable {d : ℕ}

/-- **Open half space above the interface `{xⱼ = 0}`.** -/
def halfSpace (j : Fin d) : Set (EuclideanSpace ℝ (Fin d)) := {x | 0 < x j}

/-- `halfSpace j` is open. -/
theorem isOpen_halfSpace (j : Fin d) : IsOpen (halfSpace j) :=
  isOpen_lt continuous_const (EuclideanSpace.proj j).continuous

/-- `halfSpace j` is measurable. -/
theorem measurableSet_halfSpace (j : Fin d) : MeasurableSet (halfSpace j) :=
  (isOpen_halfSpace j).measurableSet

/-- **A hyperplane is null.** The kernel of a nonzero linear functional is a proper subspace,
and a proper subspace has measure zero for an additive Haar measure. -/
theorem measure_ker_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) : μ {x | ℓ x = 0} = 0 :=
  Measure.addHaar_submodule μ (LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)) fun h =>
    hℓ (ContinuousLinearMap.coe_injective (LinearMap.ker_eq_top.1 h))

/-- **Nullity of the interface**, being a hyperplane. -/
theorem volume_interface (j : Fin d) :
    volume {x : EuclideanSpace ℝ (Fin d) | x j = 0} = 0 :=
  measure_ker_eq_zero volume (ℓ := EuclideanSpace.proj j) fun h => by
    simpa using DFunLike.congr_fun h (EuclideanSpace.single j (1 : ℝ))

/-! ### No boundary term -/

variable {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ}
  {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **A `C¹` function vanishing on a hyperplane is bounded by its gradient and the distance to
it.** This is what makes the boundary term vanish in the limit. -/
theorem abs_le_of_vanishes_on_hyperplane {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : E → ℝ} (hψ : Differentiable ℝ ψ) {M : ℝ} (hM : ∀ z, ‖fderiv ℝ ψ z‖ ≤ M)
    {ℓ : E →L[ℝ] ℝ} {v : E} (hv : ℓ v = 1) (hzero : ∀ z, ℓ z = 0 → ψ z = 0) (x : E) :
    |ψ x| ≤ M * ‖v‖ * |ℓ x| := by
  have h := (convex_univ (𝕜 := ℝ) (E := E)).norm_image_sub_le_of_norm_fderiv_le (f := ψ)
    (fun z _ => hψ z) (fun z _ => hM z) (mem_univ (x - ℓ x • v)) (mem_univ x)
  rw [hzero (x - ℓ x • v) (by simp [hv]), sub_zero, sub_sub_cancel, norm_smul,
    Real.norm_eq_abs] at h
  calc |ψ x| ≤ M * (|ℓ x| * ‖v‖) := by simpa using h
    _ = M * ‖v‖ * |ℓ x| := by ring

/-- The identity at each `ε`: multiplied by the cutoff, the test function is supported strictly
inside the half space, where the weak gradient applies. -/
private theorem cutoff_identity (hwg : HasWeakGradOn (halfSpace j) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) (k : Fin d) :
    ∫ x in halfSpace j, u x * (partialD k (slabCut (EuclideanSpace.proj j) ε) x * ψ x
        + slabCut (EuclideanSpace.proj j) ε x * partialD k ψ x)
      = - ∫ x in halfSpace j, g k x * (slabCut (EuclideanSpace.proj j) ε x * ψ x) := by
  have h := hwg (fun x => slabCut (EuclideanSpace.proj j) ε x * ψ x)
    ((contDiff_slabCut _ ε).mul hψ) hψcs.mul_left (tsupport_mul_slabCut_subset hε ψ) k
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change _ = u x * partialD k (fun y => slabCut (EuclideanSpace.proj j) ε y * ψ y) x
  rw [partialD_mul k ((contDiff_slabCut _ ε).differentiable (by simp) x)
    (hψ.differentiable (by simp) x)]

/-- The cutoffs of width `1 / (n + 1)` converge to `1` on the open half space. -/
private theorem tendsto_slabCut {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ halfSpace j) :
    Tendsto (fun n : ℕ => slabCut (EuclideanSpace.proj j) ((n + 1 : ℝ)⁻¹) x) atTop (𝓝 1) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / x j)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  refine (slabCut_eq_one (by positivity) ?_).symm
  have hmn : (2 : ℝ) / x j < (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [div_lt_iff₀ hx] at hmn
  change 2 * ((n : ℝ) + 1)⁻¹ ≤ x j
  rw [inv_eq_one_div, mul_one_div, div_le_iff₀ (by positivity)]
  linarith

/-- **Weak-gradient identity against a test function that need not vanish near the
interface**, given that the boundary term it leaves goes to zero. -/
private theorem integral_partialD_aux {k : Fin d} (hu : IntegrableOn u (halfSpace j) volume)
    (hg : IntegrableOn (g k) (halfSpace j) volume) (hwg : HasWeakGradOn (halfSpace j) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hbdry : Tendsto (fun n : ℕ => ∫ x in halfSpace j,
        u x * (partialD k (slabCut (EuclideanSpace.proj j) ((n + 1 : ℝ)⁻¹)) x * ψ x)) atTop
        (𝓝 0)) :
    ∫ x in halfSpace j, u x * partialD k ψ x = - ∫ x in halfSpace j, g k x * ψ x := by
  set cut : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => slabCut (EuclideanSpace.proj j) ((n + 1 : ℝ)⁻¹) with hcut
  have hcc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (cut n) := fun n => contDiff_slabCut _ _
  have hdψ : Continuous (partialD k ψ) := hψ.continuous_partialD (by simp) k
  have hdψcs : HasCompactSupport (partialD k ψ) := hψcs.partialD k
  obtain ⟨M, hM⟩ := hψcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨N, hN⟩ := hdψcs.exists_bound_of_continuous hdψ
  have hlim1 := tendsto_setIntegral_mul (measurableSet_halfSpace j) hu
    (f := fun n x => cut n x * partialD k ψ x) (f' := partialD k ψ)
    (fun n => (hcc n).continuous.mul hdψ) (C := N)
    (fun n x => by simpa using norm_mul_le_of_le (norm_slabCut_le_one _ _ x) (hN x))
    (fun x hx => by simpa using (tendsto_slabCut hx).mul_const (partialD k ψ x))
  have hlim2 := tendsto_setIntegral_mul (measurableSet_halfSpace j) hg
    (f := fun n x => cut n x * ψ x) (f' := ψ)
    (fun n => (hcc n).continuous.mul hψ.continuous) (C := M)
    (fun n x => by simpa using norm_mul_le_of_le (norm_slabCut_le_one _ _ x) (hM x))
    (fun x hx => by simpa using (tendsto_slabCut hx).mul_const (ψ x))
  -- Each `ε` gives the identity, and the limit gives the statement.
  have hsplit : ∀ n : ℕ, (∫ x in halfSpace j, u x * (partialD k (cut n) x * ψ x))
      + (∫ x in halfSpace j, u x * (cut n x * partialD k ψ x))
      = - ∫ x in halfSpace j, g k x * (cut n x * ψ x) := fun n => by
    have hb1 : IntegrableOn (fun x => u x * (partialD k (cut n) x * ψ x)) (halfSpace j) volume :=
      hu.mul_of_hasCompactSupport (((hcc n).continuous_partialD (by simp) k).mul hψ.continuous)
        hψcs.mul_left
    have hb2 : IntegrableOn (fun x => u x * (cut n x * partialD k ψ x)) (halfSpace j) volume :=
      hu.mul_of_hasCompactSupport ((hcc n).continuous.mul hdψ) hdψcs.mul_left
    rw [← integral_add hb1 hb2, ← cutoff_identity hwg hψ hψcs (by positivity) k]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  exact tendsto_nhds_unique
    ((by simpa using hbdry.add hlim1 : Tendsto _ atTop _).congr hsplit) hlim2.neg

/-- **No boundary term along the interface.** The cutoff depends on the `j`-th coordinate
alone, so in every other direction its derivative vanishes and the identity passes to a test
function that need not vanish near the interface. -/
theorem integral_partialD_of_ne {k : Fin d} (hk : k ≠ j)
    (hu : IntegrableOn u (halfSpace j) volume) (hg : IntegrableOn (g k) (halfSpace j) volume)
    (hwg : HasWeakGradOn (halfSpace j) u g) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) :
    ∫ x in halfSpace j, u x * partialD k ψ x = - ∫ x in halfSpace j, g k x * ψ x := by
  refine integral_partialD_aux hu hg hwg hψ hψcs ?_
  have hpd : ∀ (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)),
      partialD k (slabCut (EuclideanSpace.proj j) ε) x = 0 := fun ε x => by
    rw [partialD, fderiv_slabCut]
    simp [hk.symm]
  simp [hpd]

/-- **No boundary term in the remaining direction either**, for a test function vanishing on the
interface. Where the cutoff's derivative is `C/ε` the test function is at most `2ε` times its
gradient, so the product is bounded uniformly and supported in a slab that shrinks to nothing. -/
theorem integral_partialD_of_eq (hu : IntegrableOn u (halfSpace j) volume)
    (hg : IntegrableOn (g j) (halfSpace j) volume) (hwg : HasWeakGradOn (halfSpace j) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hzero : ∀ z : EuclideanSpace ℝ (Fin d), z j = 0 → ψ z = 0) :
    ∫ x in halfSpace j, u x * partialD j ψ x = - ∫ x in halfSpace j, g j x * ψ x := by
  refine integral_partialD_aux hu hg hwg hψ hψcs ?_
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨M, hM⟩ := (hψcs.fderiv ℝ).exists_bound_of_continuous
    (hψ.continuous_fderiv (by simp))
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hcut : ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      ‖partialD j (slabCut (EuclideanSpace.proj j) ((n + 1 : ℝ)⁻¹)) x * ψ x‖ ≤ 2 * C * M := by
    intro n x
    have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    rw [norm_mul, partialD]
    by_cases hcase : x j ∈ Icc ((n + 1 : ℝ)⁻¹) (2 * (n + 1 : ℝ)⁻¹)
    · have hx : 0 < x j := hε.trans_le hcase.1
      have h1 : |fderiv ℝ (slabCut (EuclideanSpace.proj j) ((n + 1 : ℝ)⁻¹)) x
          (EuclideanSpace.single j (1 : ℝ))| ≤ C / ((n : ℝ) + 1)⁻¹ := by
        simpa using abs_fderiv_slabCut_le (ℓ := EuclideanSpace.proj j) hε hC x
          (EuclideanSpace.single j (1 : ℝ))
      have h2 : |ψ x| ≤ M * (2 * ((n : ℝ) + 1)⁻¹) := by
        have := abs_le_of_vanishes_on_hyperplane (hψ.differentiable (by simp)) hM
          (ℓ := EuclideanSpace.proj j) (v := EuclideanSpace.single j (1 : ℝ)) (by simp) hzero x
        simp only [PiLp.norm_single, norm_one, mul_one, PiLp.proj_apply, abs_of_pos hx] at this
        exact this.trans (by gcongr; exact hcase.2)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc _ ≤ C / ((n : ℝ) + 1)⁻¹ * (M * (2 * ((n : ℝ) + 1)⁻¹)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 2 * C * M := by field_simp
    · rw [fderiv_slabCut_eq_zero_of_notMem hε hcase]
      simp only [norm_zero, zero_mul]
      positivity
  have h := tendsto_setIntegral_mul (measurableSet_halfSpace j) hu
    (f := fun (n : ℕ) x => partialD j (slabCut (EuclideanSpace.proj j) ((n + 1 : ℝ)⁻¹)) x * ψ x)
    (f' := fun _ => 0)
    (fun n => (((contDiff_slabCut _ _).continuous_partialD (by simp) j)).mul hψ.continuous)
    (C := 2 * C * M) hcut fun x hx => ?_
  · simpa using h
  · obtain ⟨m, hm⟩ := exists_nat_gt (2 / x j)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmn : (2 : ℝ) / x j < (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hx] at hmn
    have hgt : 2 * ((n : ℝ) + 1)⁻¹ < x j := by
      rw [inv_eq_one_div, mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
    rw [partialD, fderiv_slabCut_eq_zero_of_notMem (by positivity) (fun h => h.2.not_gt hgt),
      zero_mul]

end EllipticPdes.Extension
