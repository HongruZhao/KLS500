/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

public import EllipticPdes.Regularity.ClassicalSolvability
public import EllipticPdes.Regularity.LocalWeakForm
public import EllipticPdes.Embedding.WeakGradUnique
public import EllipticPdes.Extension.GlobalApproximation

/-!
# Pointwise equation of a smooth representative

A weak solution with a representative that is twice continuously differentiable on an open
subset of the domain satisfies the equation there, almost everywhere and in the classical
divergence form
`-∑ᵢⱼ ∂ⱼ(aᵢⱼ ∂ᵢu) + ∑ᵢ bᵢ ∂ᵢu + c u = f`,
the diffusion being `C¹`. This is the step the interior theory leaves to the fundamental lemma
of the calculus of variations: the weak formulation tested against a function supported in the
open set, integrated by parts once more with the classical derivatives of the representative in
place of the weak ones, says that the residual of the equation integrates to zero against every
test function, so it vanishes almost everywhere.

Two identifications feed the argument. The classical gradient of a `C¹` function on an open
set is a weak gradient there, by the integration by parts a test function's compact support
allows, and the weak gradient on an open set is unique, so the gradient coordinates of the
solution agree almost everywhere with the classical partials of the representative on every
ball whose closure lies in the set, and a countable subcover of the set by such balls makes
that agreement hold on the whole set.

## Main declarations

* `EllipticPdes.Regularity.hasWeakGradOn_of_contDiffOn`: the classical gradient of a `C¹`
  function on an open set is a weak gradient there.
* `EllipticPdes.Regularity.ae_restrict_of_forall_closedBall_subset`: a property true almost
  everywhere on every ball whose closure lies in an open set is true almost everywhere on it.
* `EllipticPdes.Regularity.weakSolution_ae_eq_of_contDiffOn`: the pointwise equation.
* `EllipticPdes.Regularity.exists_weakSolution_interior_classical`: solvability with a smooth
  interior representative satisfying the equation there.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Lemma I.2.4 (p. 3);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.1.2 (pp. 313–315) and §6.3.1
Theorem 3 (p. 334).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev
open EllipticPdes.Embedding (HasWeakGradOn hasWeakGradOn_unique_ae integrableOn_mul_bounded)
open EllipticPdes.Extension (hasWeakGradOn_of_mem_W12)

variable {d : ℕ}

/-! ### From balls to an open set -/

/-- **From balls to the open set.** A property true almost everywhere on every ball whose
closure lies in an open set is true almost everywhere on the set, by a countable subcover. -/
theorem ae_restrict_of_forall_closedBall_subset {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) {p : EuclideanSpace ℝ (Fin d) → Prop}
    (h : ∀ x ∈ W, ∀ r : ℝ, 0 < r → closedBall x r ⊆ W →
      ∀ᵐ y ∂(volume.restrict (ball x r)), p y) :
    ∀ᵐ y ∂(volume.restrict W), p y := by
  classical
  have key : ∀ x, x ∈ W → ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ W := by
    intro x hx
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x hx
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεW⟩
  choose! r hr hrW using key
  obtain ⟨t, htW, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (r x)) (s := W) fun x hx =>
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr x hx))
  refine ae_restrict_of_ae_restrict_of_subset hcover ?_
  rw [ae_restrict_biUnion_iff _ htc]
  intro x hx
  exact h x (htW hx) (r x) (hr x (htW hx)) (hrW x (htW hx))

/-! ### The classical gradient as a weak gradient -/

/-- **Classical gradient of a `C¹` function on an open set is a weak gradient there.** A test
function supported in the set has compact support, so the integration by parts has no boundary
term, and the function need only be differentiable on that support. -/
theorem hasWeakGradOn_of_contDiffOn {W : Set (EuclideanSpace ℝ (Fin d))} (hW : IsOpen W)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : ContDiffOn ℝ 1 v W) :
    HasWeakGradOn W v fun k => partialD k v :=
  fun _ hφc hφcs hφW k => setIntegral_mul_partialD_eq_neg hW hv hφc hφcs hφW k

/-- On every ball whose closure lies in an open set `W`, the weak gradient of a `W^{1,2}`
function agrees almost everywhere with the classical gradient of a `C²` representative, hence
on `W`. -/
private lemma grad_ae_eq_partialD {Ω W : Set (EuclideanSpace ℝ (Fin d))} (u : H01 Ω)
    (hWo : IsOpen W) (hWΩ : W ⊆ Ω) {u' : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu' : u' =ᵐ[volume.restrict W] fun x => ((u : H1amb Ω) 0 : L2D Ω) x)
    (hsm : ContDiffOn ℝ 2 u' W) (i : Fin d) :
    (fun x => ((u : H1amb Ω) i.succ : L2D Ω) x) =ᵐ[volume.restrict W] partialD i u' := by
  have hgrad1 : ∀ i, ContDiffOn ℝ 1 (partialD i u') W := fun i =>
    (hsm.fderiv_of_isOpen hWo (by norm_num)).clm_apply contDiffOn_const
  have hgradc : ∀ i, ContinuousOn (partialD i u') W := fun i => (hgrad1 i).continuousOn
  have hweak : HasWeakGradOn W (fun x => ((u : H1amb Ω) 0 : L2D Ω) x)
      (fun i x => ((u : H1amb Ω) i.succ : L2D Ω) x) :=
    (hasWeakGradOn_of_mem_W12 (H01_le_W12 Ω u.2)).mono hWΩ
  have hclass : HasWeakGradOn W (fun x => ((u : H1amb Ω) 0 : L2D Ω) x)
      (fun i => partialD i u') :=
    (hasWeakGradOn_of_contDiffOn hWo (hsm.of_le one_le_two)).congr_ae hu' fun _ =>
      EventuallyEq.rfl
  refine ae_restrict_of_forall_closedBall_subset hWo fun x hx r hr hrW => ?_
  have hball : ball x r ⊆ W := ball_subset_closedBall.trans hrW
  refine hasWeakGradOn_unique_ae isOpen_ball measurableSet_ball ?_ ?_ (hweak.mono hball)
    (hclass.mono hball) i
  · intro k
    exact ((Lp.memLp ((u : H1amb Ω) k.succ)).mono_measure
      (Measure.restrict_mono (hball.trans hWΩ) le_rfl)).integrable one_le_two
  · intro k
    exact (((hgradc k).mono hrW).integrableOn_compact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall

/-! ### The pointwise equation -/

/-- The residual of the equation for a `C²` representative on an open set is locally
integrable there. -/
private lemma locallyIntegrableOn_residual (Op : FullEllipticOp d)
    {Ω W : Set (EuclideanSpace ℝ (Fin d))} (hWo : IsOpen W) (hWΩ : W ⊆ Ω)
    {u' : EuclideanSpace ℝ (Fin d) → ℝ} (hsm : ContDiffOn ℝ 2 u' W)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (f : L2D Ω) :
    LocallyIntegrableOn (fun x => -(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
      + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x - f x) W volume := by
  have hgrad1 : ∀ i, ContDiffOn ℝ 1 (partialD i u') W := fun i =>
    (hsm.fderiv_of_isOpen hWo (by norm_num)).clm_apply contDiffOn_const
  have hdivc : ∀ i j, ContinuousOn (partialD j fun y => Op.a y i j * partialD i u' y) W :=
    fun i j => (((hA1.contDiff i j).contDiffOn.mul (hgrad1 i)).continuousOn_fderiv_of_isOpen
      hWo le_rfl).clm_apply continuousOn_const
  rw [locallyIntegrableOn_iff hWo.isLocallyClosed]
  intro K hKW hK
  have hbb : ∀ i, ∀ᵐ x ∂(volume.restrict K), ‖Op.b x i‖ ≤ Op.Bsup := fun i =>
    ae_restrict_of_ae ((Op.b_bdd i).mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have hcb : ∀ᵐ x ∂(volume.restrict K), ‖Op.c x‖ ≤ Op.Csup :=
    ae_restrict_of_ae (Op.c_bdd.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have h1 : IntegrableOn (fun x => ∑ i, ∑ j,
      partialD j (fun y => Op.a y i j * partialD i u' y) x) K volume :=
    ((continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      hdivc i j).mono hKW).integrableOn_compact hK
  have h2 : IntegrableOn (fun x => ∑ i, Op.b x i * partialD i u' x) K volume :=
    integrable_finsetSum _ fun i _ => Integrable.bdd_mul
      ((((hgrad1 i).continuousOn).mono hKW).integrableOn_compact hK)
      (Op.b_meas i).aestronglyMeasurable (hbb i)
  have h3 : IntegrableOn (fun x => Op.c x * u' x) K volume :=
    Integrable.bdd_mul ((hsm.continuousOn.mono hKW).integrableOn_compact hK)
      Op.c_meas.aestronglyMeasurable hcb
  have h4 : IntegrableOn (f : EuclideanSpace ℝ (Fin d) → ℝ) K volume := by
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact ((Lp.memLp f).mono_measure (Measure.restrict_mono (hKW.trans hWΩ) le_rfl)).integrable
      one_le_two
  exact ((h1.neg.add h2).add h3).sub h4

/-- **The residual integrates to zero.** If the weak formulation, read against a `C²`
representative `u'` on an open set `W`, holds against a test function `φ` supported in `W`, then
the residual of the equation integrates to zero against `φ`. The principal term is integrated by
parts once more. -/
private lemma integral_residual_eq_zero (Op : FullEllipticOp d)
    {Ω W : Set (EuclideanSpace ℝ (Fin d))} (hWo : IsOpen W) (hWΩ : W ⊆ Ω)
    {u' : EuclideanSpace ℝ (Fin d) → ℝ} (hsm : ContDiffOn ℝ 2 u' W)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (f : L2D Ω)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ)
    (hφW : tsupport φ ⊆ W)
    (hloc : (∑ i, ∑ j, ∫ x in W, Op.a x i j * partialD i u' x * partialD j φ x)
      + (∑ i, ∫ x in W, Op.b x i * (φ x * partialD i u' x))
      + (∫ x in W, Op.c x * (φ x * u' x)) = ∫ x in W, (f x : ℝ) * φ x) :
    ∫ x, φ x • (-(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
      + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x - f x) ∂volume = 0 := by
  classical
  have hWm := hWo.measurableSet
  have hu'c : ContinuousOn u' W := hsm.continuousOn
  have hgrad1 : ∀ i, ContDiffOn ℝ 1 (partialD i u') W := fun i =>
    (hsm.fderiv_of_isOpen hWo (by norm_num)).clm_apply contDiffOn_const
  have hgradc : ∀ i, ContinuousOn (partialD i u') W := fun i => (hgrad1 i).continuousOn
  have hprod1 : ∀ i j, ContDiffOn ℝ 1 (fun y => Op.a y i j * partialD i u' y) W := fun i j =>
    (hA1.contDiff i j).contDiffOn.mul (hgrad1 i)
  have hdivc : ∀ i j, ContinuousOn (partialD j fun y => Op.a y i j * partialD i u' y) W :=
    fun i j => ((hprod1 i j).continuousOn_fderiv_of_isOpen hWo le_rfl).clm_apply
      continuousOn_const
  have hφcont : Continuous φ := hφc.continuous
  have hoff : ∀ G : EuclideanSpace ℝ (Fin d) → ℝ, ∀ x, x ∉ tsupport φ → φ x * G x = 0 :=
    fun G x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hint : ∀ G : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn G W →
      Integrable (fun x => φ x * G x) (volume.restrict W) := fun G hG =>
    (integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
      (hφcont.continuousOn.mul hG) (hoff _)).integrableOn
  have hint_div := fun i j => hint _ (hdivc i j)
  have hint_b : ∀ i, Integrable (fun x => Op.b x i * (φ x * partialD i u' x))
      (volume.restrict W) := fun i =>
    Integrable.bdd_mul (hint _ (hgradc i)) (Op.b_meas i).aestronglyMeasurable
      (ae_restrict_of_ae ((Op.b_bdd i).mono fun x hx => by simpa [Real.norm_eq_abs] using hx))
  have hint_c : Integrable (fun x => Op.c x * (φ x * u' x)) (volume.restrict W) :=
    Integrable.bdd_mul (hint _ hu'c) Op.c_meas.aestronglyMeasurable
      (ae_restrict_of_ae (Op.c_bdd.mono fun x hx => by simpa [Real.norm_eq_abs] using hx))
  have hint_f : Integrable (fun x => (f x : ℝ) * φ x) (volume.restrict W) := by
    obtain ⟨M, hM⟩ := hφcs.exists_bound_of_continuous hφcont
    have hfK : IntegrableOn (f : EuclideanSpace ℝ (Fin d) → ℝ) (tsupport φ) volume := by
      have : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hφcs.isCompact.measure_lt_top⟩
      exact ((Lp.memLp f).mono_measure
        (Measure.restrict_mono (hφW.trans hWΩ) le_rfl)).integrable one_le_two
    exact IntegrableOn.of_forall_sdiff_eq_zero (integrableOn_mul_bounded hfK hφcont hM) hWm
      fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx.2, mul_zero]
  -- integration by parts on the principal term
  have hibp : ∀ i j, ∫ x in W, Op.a x i j * partialD i u' x * partialD j φ x
      = -∫ x in W, φ x * partialD j (fun y => Op.a y i j * partialD i u' y) x := fun i j => by
    rw [setIntegral_mul_partialD_eq_neg hWo (hprod1 i j) hφc hφcs hφW j]
    exact congrArg Neg.neg (integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _))
  simp only [hibp, Finset.sum_neg_distrib] at hloc
  -- assemble the integral of the residual
  have hpt : ∀ x, φ x • (-(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
      + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x - f x) = -(∑ i, ∑ j, φ x *
      partialD j (fun y => Op.a y i j * partialD i u' y) x)
      + ∑ i, Op.b x i * (φ x * partialD i u' x) + Op.c x * (φ x * u' x) - (f x : ℝ) * φ x := by
    intro x
    simp only [smul_eq_mul, mul_add, mul_sub, mul_neg, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => (by ring : φ x * (Op.b x i * partialD i u' x)
      = Op.b x i * (φ x * partialD i u' x))]
    ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) (fun x hx => by
    rw [smul_eq_mul, image_eq_zero_of_notMem_tsupport fun hc => hx (hφW hc), zero_mul])]
  simp_rw [hpt]
  have hD : Integrable (fun x => ∑ i, ∑ j, φ x *
      partialD j (fun y => Op.a y i j * partialD i u' y) x) (volume.restrict W) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_div i j
  have hB : Integrable (fun x => ∑ i, Op.b x i * (φ x * partialD i u' x)) (volume.restrict W) :=
    integrable_finsetSum _ fun i _ => hint_b i
  rw [integral_sub, integral_add, integral_add, integral_neg,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_div i j,
    integral_finsetSum _ fun i _ => hint_b i]
  · simp only [integral_finsetSum _ fun j _ => hint_div _ j]
    linarith only [hloc]
  · exact hD.neg
  · exact hB
  · exact hD.neg.add hB
  · exact hint_c
  · exact (hD.neg.add hB).add hint_c
  · exact hint_f

/-- **Pointwise equation of a smooth representative.** A weak solution of the Dirichlet
problem whose function coordinate has a representative that is `C²` on an open subset of the
domain satisfies the equation there almost everywhere, in the classical divergence form, the
diffusion being `C¹`. The weak gradient of the solution on the open set is the classical
gradient of the representative, the weak formulation tested against a function supported
there is integrated by parts once more, and the fundamental lemma of the calculus of variations
(Guo Lemma I.2.4) makes the residual vanish almost everywhere. -/
theorem weakSolution_ae_eq_of_contDiffOn (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    {W : Set (EuclideanSpace ℝ (Fin d))} (hWo : IsOpen W) (hWΩ : W ⊆ Ω)
    {u' : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu' : u' =ᵐ[volume.restrict W] fun x => ((u : H1amb Ω) 0 : L2D Ω) x)
    (hsm : ContDiffOn ℝ 2 u' W) :
    ∀ᵐ x ∂volume, x ∈ W →
      -(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
        + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x = f x := by
  classical
  have hWm := hWo.measurableSet
  have hgrad_eq := grad_ae_eq_partialD u hWo hWΩ hu' hsm
  have hres : ∀ g : L2D Ω,
      (restrictL2 (Ω := W) (extendL2 hΩm g) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict W] (g : EuclideanSpace ℝ (Fin d) → ℝ) :=
    coeFn_restrictL2_extendL2_of_subset hΩm hWm hWΩ
  have htest : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, φ x • (-(∑ i, ∑ j, partialD j (fun y => Op.a y i j *
        partialD i u' y) x) + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x - f x) ∂volume
        = 0 := by
    intro φ hφc hφcs hφW
    refine integral_residual_eq_zero Op hWo hWΩ hsm hA1 f hφc hφcs hφW ?_
    have hloc := localWeakForm_of_fullBilin Op hΩm hWm hWΩ u f hu φ hφc hφcs hφW
    have e1 : ∀ i j, ∫ x in W, Op.a x i j
        * (restrictL2 (Ω := W) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * partialD j φ x
        = ∫ x in W, Op.a x i j * partialD i u' x * partialD j φ x := fun i j =>
      integral_congr_ae (by
        filter_upwards [hres ((u : H1amb Ω) i.succ), hgrad_eq i] with x h1 h2
        rw [h1, h2])
    have e2 : ∀ i, ∫ x in W, Op.b x i
        * (restrictL2 (Ω := W) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * φ x
        = ∫ x in W, Op.b x i * (φ x * partialD i u' x) := fun i =>
      integral_congr_ae (by
        filter_upwards [hres ((u : H1amb Ω) i.succ), hgrad_eq i] with x h1 h2
        rw [h1, h2]; ring)
    have e3 : ∫ x in W, Op.c x
        * (restrictL2 (Ω := W) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ) * φ x
        = ∫ x in W, Op.c x * (φ x * u' x) :=
      integral_congr_ae (by
        filter_upwards [hres ((u : H1amb Ω) 0), hu'] with x h1 h2
        rw [h1, h2]; ring)
    have e4 : ∫ x in W, (restrictL2 (Ω := W) (extendL2 hΩm f) x : ℝ) * φ x
        = ∫ x in W, (f x : ℝ) * φ x :=
      integral_congr_ae (by filter_upwards [hres f] with x h1; rw [h1])
    simpa only [e1, e2, e3, e4] using hloc
  -- the fundamental lemma of the calculus of variations
  have hae := hWo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_residual Op hWo hWΩ hsm hA1 f) htest
  filter_upwards [hae] with x hx hxW
  linarith only [hx hxW]

/-- **Solvability with a smooth interior representative satisfying the equation.** On a
bounded domain, for an operator with no transport term and a nonnegative zeroth-order
coefficient, whose diffusion is `C¹` and whose coefficients lie in `W^{k,∞}` at every order,
and for a datum with weak derivatives of every order bounded in `L²`, the Dirichlet problem has
a weak solution whose class has a `C^∞` representative on the interior of every compact subset
of the domain, and that representative satisfies the equation there almost everywhere. -/
theorem exists_weakSolution_interior_classical {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (hA1 : IsC1Coeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u : H01 Ω,
      (∀ v : H01 Ω, Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) ∧
      ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
        u' =ᵐ[volume.restrict (interior V)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
          ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) ∧
          ∀ᵐ x ∂volume, x ∈ interior V →
            -(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
              + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x = f x := by
  obtain ⟨u, hu, u', hu', hsm⟩ :=
    exists_weakSolution_interior_smooth Op hΩm hΩo hΩb hb hc hA1.toIsLipCoeff hA hbc f hf hVc hVΩ
  have hWΩ : interior V ⊆ Ω := interior_subset.trans hVΩ
  have hu'2 : u' =ᵐ[volume.restrict (interior V)] fun x => ((u : H1amb Ω) 0 : L2D Ω) x := by
    filter_upwards [hu', ae_restrict_of_ae (coeFn_extendL2 hΩm ((u : H1amb Ω) 0)),
      ae_restrict_mem isOpen_interior.measurableSet] with x h1 h2 h3
    rw [h1, h2, Set.indicator_of_mem (hWΩ h3)]
  refine ⟨u, hu, u', hu', hsm, ?_⟩
  exact weakSolution_ae_eq_of_contDiffOn Op hΩm hA1 u f hu isOpen_interior hWΩ hu'2
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))

end EllipticPdes.Regularity
