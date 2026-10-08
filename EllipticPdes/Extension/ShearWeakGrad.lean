/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Shear
public import EllipticPdes.Embedding.GagliardoNirenberg

/-!
# Weak gradient through a shear

Flattening a `C¹` boundary is a shear, and a Sobolev class has to travel through it. The test
function travels the other way, and a smooth test function pulled back through a `C¹` shear is
`C¹` and no better, which is the class `hasWeakGradOn_contDiffOne` integrates by parts against.

One term of the chain rule asks for more. The pull-back multiplies the test function by a
partial derivative of the chart, which for a `C¹` chart is continuous and no better, so the
product sits outside the `C¹` class. That factor does not depend on the `j`-th coordinate,
mollification preserves that independence, and a mollified factor is smooth, so the product rule
in the `j`-th direction leaves only the term the weak gradient names. Dominated convergence
returns the identity as the mollification shrinks.

## Main declarations

* `EllipticPdes.Extension.fderiv_eq_of_indepCoord`: the derivative of a chart independent of the
  `j`-th coordinate is itself independent of it.
* `EllipticPdes.Extension.indepCoord_partialD`: the same for a partial derivative.
* `EllipticPdes.Extension.indepCoord_convolution`: mollification preserves that independence.
* `EllipticPdes.Extension.integral_mul_indepCoord`: the identity of a weak gradient in the
  `j`-th direction, against a test function scaled by such a factor.
* `EllipticPdes.Extension.hasWeakGradOn_comp_shear`: the weak gradient of a class composed with
  a shear, the transpose of the shear's derivative applied to the gradient.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal Convolution Pointwise

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn partialD_mul tsupport_comp_homeomorph)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

local notation "Lsm" => ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)

/-! ### Independence of a coordinate, under differentiation and under mollification -/

/-- **Independence of the `j`-th coordinate passes to a partial derivative.** Translating along
`eⱼ` leaves the chart alone, so it leaves the derivative alone. -/
theorem fderiv_eq_of_indepCoord {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    fderiv ℝ γ (y + t • EuclideanSpace.single j (1 : ℝ)) = fderiv ℝ γ y := by
  set c : EuclideanSpace ℝ (Fin d) := t • EuclideanSpace.single j (1 : ℝ) with hc
  have hfun : (fun z => γ (z + c)) = γ := funext fun z => hind z t
  have h1 : HasFDerivAt (fun z => γ (z + c)) (fderiv ℝ γ (y + c)) y := by
    have h := (hγ (y + c)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const c)
    simpa [Function.comp_def] using h
  rw [hfun] at h1
  exact h1.fderiv.symm

/-- The partial derivative `partialD k γ` of a differentiable `γ` independent of the `j`-th
coordinate is again independent of it. -/
theorem indepCoord_partialD {j k : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : Differentiable ℝ γ) (hind : IndepCoord j γ) : IndepCoord j (partialD k γ) := by
  intro y t
  simp only [partialD, fderiv_eq_of_indepCoord hγ hind y t]

/-- **Mollification preserves independence of a coordinate.** The convolution averages the
factor over translations, each of which leaves it alone. -/
theorem indepCoord_convolution {j : Fin d} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (hind : IndepCoord j c) (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) :
    IndepCoord j (ρ.normed volume ⋆[Lsm, volume] c) := by
  intro y t
  simp only [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  have hshift : y + t • EuclideanSpace.single j (1 : ℝ) - s
      = (y - s) + t • EuclideanSpace.single j (1 : ℝ) := by abel
  rw [hshift, hind (y - s) t]

/-! ### Integration by parts against a scaled test function -/

/-- **Integration by parts against a bounded factor independent of the `j`-th coordinate.** The
identity of a weak gradient in the `j`-th direction survives multiplication of the test function
by such a factor, which need only be continuous. Mollification makes the factor smooth and
leaves it independent of the `j`-th coordinate, so the product rule contributes nothing beyond
the term the identity names, and dominated convergence takes the mollification away. -/
theorem integral_mul_indepCoord {B : Set (EuclideanSpace ℝ (Fin d))} (hBopen : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g) {j : Fin d} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous c) (hcind : IndepCoord j c) {M : ℝ} (hcb : ∀ y, ‖c y‖ ≤ M)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ B) :
    ∫ x in B, u x * (c x * partialD j ψ x) = - ∫ x in B, g j x * (c x * ψ x) := by
  obtain ⟨P, hP⟩ := hψcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨N, hN⟩ := (hψcs.partialD j).exists_bound_of_continuous
    (hψ.continuous_partialD one_ne_zero j)
  set ρ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := mollifier 1 one_pos
  set cn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n => (ρ n).normed volume ⋆[Lsm, volume] c
  have hsm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (cn n) := fun n =>
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (L := Lsm) (ρ n).contDiff_normed
      hc.locallyIntegrable
  have hrOut := tendsto_rOut_mollifier (E := EuclideanSpace ℝ (Fin d)) 1 one_pos
  refine integral_eq_neg_integral_of_tendsto hBopen.measurableSet hu (hgi j)
    (F := fun n x => cn n x * partialD j ψ x) (G := fun n x => cn n x * ψ x)
    (fun n => (hsm n).continuous.mul (hψ.continuous_partialD one_ne_zero j))
    (fun n => (hsm n).continuous.mul hψ.continuous)
    (N := M * N) (P := M * P)
    (fun n x => norm_mul_le_of_le (norm_normed_convolution_le (ρ n) hc hcb x) (hN x))
    (fun n x => norm_mul_le_of_le (norm_normed_convolution_le (ρ n) hc hcb x) (hP x))
    (fun x _ => (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hrOut hc
      x).mul_const _)
    (fun x _ => (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hrOut hc
      x).mul_const _) fun n => ?_
  have hθd : ∀ x, partialD j (fun z => cn n z * ψ z) x = cn n x * partialD j ψ x := fun x => by
    rw [partialD_mul j ((hsm n).differentiable (by simp) x) (hψ.differentiable (by simp) x),
      partialD_eq_zero_of_indepCoord ((hsm n).differentiable (by simp))
        (indepCoord_convolution hcind (ρ n)) x, zero_mul, zero_add]
  simpa only [hθd] using hasWeakGradOn_contDiffOne hBopen hu hgi hwg
    (((hsm n).of_le (by exact_mod_cast le_top)).mul hψ) hψcs.mul_left
    (tsupport_mul_subset_right.trans hψs) j

/-! ### The weak gradient of a composition with a shear -/

/-- **A test function pulled back through the inverse shear.** A smooth test function supported in
the preimage of `B` under the shear is the composite of the shear with a `C¹` function of compact
support in `B`. -/
theorem exists_shear_pullback {B : Set (EuclideanSpace ℝ (Fin d))} {j : Fin d}
    {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ shear j γ ⁻¹' B) :
    ∃ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ ∧
      tsupport Ψ ⊆ B ∧ ∀ y, Ψ (shear j γ y) = φ y := by
  have hnegcont : Continuous fun z => -γ z := hγ.continuous.neg
  refine ⟨φ ∘ shearHomeomorph hnegcont hind.neg,
    (hφ.of_le (by exact_mod_cast le_top)).comp (contDiff_shear hγ.neg),
    hφcs.comp_homeomorph _, fun x hx => ?_, fun y => congrArg φ (shear_shear_neg hind y)⟩
  rw [tsupport_comp_homeomorph] at hx
  simpa [shearHomeomorph, shear_neg_shear hind x] using hφs hx

/-- **Weak gradient through a shear.** If `u` has weak gradient `g` on `B`, then `u ∘ S` has
weak gradient `k ↦ gₖ ∘ S + (g_j ∘ S) ∂ₖγ` on the preimage of `B`, which is the transpose of the
shear's derivative applied to the gradient.

A smooth test function pulled back through the inverse shear is `C¹`, and the chain rule splits
the identity in two. The first half is the weak gradient tested against that pull-back. The
second has the chart's `k`-th partial as a factor on the test function, and that factor is
independent of the `j`-th coordinate, which is what `integral_mul_indepCoord` asks of it. -/
theorem hasWeakGradOn_comp_shear {B : Set (EuclideanSpace ℝ (Fin d))} (hBopen : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g) {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) {M : ℝ}
    (hγb : ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ y‖ ≤ M) :
    HasWeakGradOn (shear j γ ⁻¹' B) (fun y => u (shear j γ y))
      (fun k y => g k (shear j γ y) + g j (shear j γ y) * partialD k γ y) := by
  intro φ hφ hφcs hφs k
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hckc : Continuous (partialD k γ) := hγ.continuous_partialD one_ne_zero k
  have hckind : IndepCoord j (partialD k γ) := indepCoord_partialD hγd hind
  -- the chart's partial derivative sees no change along the shear
  have hckS : ∀ (m : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      partialD m γ (shear j γ y) = partialD m γ y := fun m y =>
    indepCoord_partialD (k := m) hγd hind y (γ y)
  -- the test function, pulled back through the inverse shear
  obtain ⟨Ψ, hΨC1, hΨcs, hΨs, hΨS⟩ := exists_shear_pullback hγ hind hφ hφcs hφs
  -- the chain rule for the smooth test function
  have hchain : ∀ y, partialD k φ y
      = partialD k Ψ (shear j γ y) + partialD j Ψ (shear j γ y) * partialD k γ y := fun y => by
    have hcomp := partialD_comp_shear (j := j) (γ := γ) (φ := Ψ) hγd
      (hΨC1.differentiable (by simp)) k y
    rwa [show (fun z => Ψ (shear j γ z)) = φ from funext hΨS] at hcomp
  -- the change of variables, in both directions
  have hmp : MeasurePreserving (shear j γ) volume volume := measurePreserving_shear hγd hind
  have hme : MeasurableEmbedding (shear j γ) := measurableEmbedding_shear hγd.continuous hind
  have hcv : ∀ F : EuclideanSpace ℝ (Fin d) → ℝ,
      ∫ y in shear j γ ⁻¹' B, F (shear j γ y) = ∫ x in B, F x :=
    fun F => hmp.setIntegral_preimage_emb hme F B
  -- integrability of the four pieces
  have hdj : Continuous (partialD j Ψ) := hΨC1.continuous_partialD one_ne_zero j
  have hi1 : IntegrableOn (fun x => u x * partialD k Ψ x) B volume :=
    hu.mul_of_hasCompactSupport (hΨC1.continuous_partialD one_ne_zero k) (hΨcs.partialD k)
  have hi2 : IntegrableOn (fun x => u x * (partialD k γ x * partialD j Ψ x)) B volume :=
    hu.mul_of_hasCompactSupport (hckc.mul hdj) (hΨcs.partialD j).mul_left
  have hi3 : IntegrableOn (fun x => g k x * Ψ x) B volume :=
    (hgi k).mul_of_hasCompactSupport hΨC1.continuous hΨcs
  have hi4 : IntegrableOn (fun x => g j x * (partialD k γ x * Ψ x)) B volume :=
    (hgi j).mul_of_hasCompactSupport (hckc.mul hΨC1.continuous) hΨcs.mul_left
  -- both sides, moved onto `B` and split
  have hLeq : ∫ y in shear j γ ⁻¹' B, u (shear j γ y) * partialD k φ y
      = (∫ x in B, u x * partialD k Ψ x)
        + ∫ x in B, u x * (partialD k γ x * partialD j Ψ x) := by
    rw [← integral_add hi1 hi2,
      ← hcv fun x => u x * partialD k Ψ x + u x * (partialD k γ x * partialD j Ψ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hchain y, hckS k y]
    ring
  have hReq : ∫ y in shear j γ ⁻¹' B,
        (g k (shear j γ y) + g j (shear j γ y) * partialD k γ y) * φ y
      = (∫ x in B, g k x * Ψ x) + ∫ x in B, g j x * (partialD k γ x * Ψ x) := by
    rw [← integral_add hi3 hi4,
      ← hcv fun x => g k x * Ψ x + g j x * (partialD k γ x * Ψ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hckS k y, hΨS y]
    ring
  rw [hLeq, hReq, hasWeakGradOn_contDiffOne hBopen hu hgi hwg hΨC1 hΨcs hΨs k,
    integral_mul_indepCoord hBopen hu hgi hwg hckc hckind (hγb k) hΨC1 hΨcs hΨs]
  ring

end EllipticPdes.Extension
