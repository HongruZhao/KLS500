/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.DifferentiatedEquation
public import EllipticPdes.Regularity.LowerOrderWkInfty

/-!
# Moving a derivative onto the solution

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 differentiates the weak
equation in a direction `ℓ`. Each term of the equation has the shape `∫_V a·g·∂_ℓψ`, and the
Leibniz rule `HasWeakDerivOn.mul_isWkInfty_left` moves `∂_ℓ` onto the product `a·g`. The
coefficients enter only through the pair `(a, ∂_ℓ a)`, which `WeakBddPair` records, so one
identity serves a `C¹` coefficient and a `W^{1,∞}` coefficient alike: the first supplies its
classical derivative and the second a representative from a `W^{k,∞}` bundle (Guo, *Partial
Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2 (p. 65)).

## Main declarations

* `WeakBddPair`: a bounded measurable weight with a bounded measurable weak `ℓ`-derivative.
* `WeakBddPair.integral_mul_partialD_eq`: moving `∂_ℓ` off the test function in one term.
* `differentiated_weakForm_div_of_pairs`: the four terms assembled, divergence-datum form.
* `differentiated_weakForm_of_pairs`: Evans's equation (34), strong-datum form.
* `differentiated_weakForm_wkInfty`: the strong-datum form with every coefficient derivative
  read off a `W^{k,∞}` bundle.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Reading the order-one data off a `W^{k,∞}` bundle -/

namespace IsWkInftyCoeff

variable {A : EllipticCoeff d} {k : ℕ}

/-- The order-one member of the family is a weak partial derivative of the coefficient entry. -/
theorem hasWeakPartial_D (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    HasWeakPartial ℓ (fun x => A.a x i j) (hA.D [ℓ] i j) := by
  have h := hA.D_step i j ℓ [] (by simp)
  rwa [hA.D_nil i j] at h

/-- The order-one member of the family is measurable. -/
theorem measurable_D_singleton (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    Measurable (hA.D [ℓ] i j) := hA.D_meas i j [ℓ] (by simp)

/-- The order-one member of the family is essentially bounded by `bound 1`. -/
theorem ae_abs_D_singleton_le (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hA.D [ℓ] i j x| ≤ hA.bound 1 := by
  have h := hA.ess_bdd i j [ℓ] (by simp)
  simpa using h

/-- The order-two member of the family is a weak partial derivative of the order-one member. -/
theorem hasWeakPartial_D_singleton (hA : IsWkInftyCoeff A (k + 2)) (m ℓ i j : Fin d) :
    HasWeakPartial m (hA.D [ℓ] i j) (hA.D [m, ℓ] i j) := hA.D_step i j m [ℓ] (by simp)

/-- The order-two member of the family is measurable. -/
theorem measurable_D_pair (hA : IsWkInftyCoeff A (k + 2)) (m ℓ i j : Fin d) :
    Measurable (hA.D [m, ℓ] i j) := hA.D_meas i j [m, ℓ] (by simp)

/-- The order-two member of the family is essentially bounded by `bound 2`. -/
theorem ae_abs_D_pair_le (hA : IsWkInftyCoeff A (k + 2)) (m ℓ i j : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hA.D [m, ℓ] i j x| ≤ hA.bound 2 := by
  have h := hA.ess_bdd i j [m, ℓ] (by simp)
  simpa using h

end IsWkInftyCoeff

namespace IsWkInfty

variable {f : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ}

/-- The function is measurable, read off the order-zero member of the family. -/
theorem measurable_self (hf : IsWkInfty f k) : Measurable f := by
  have h := hf.D_meas [] (by simp)
  rwa [hf.D_nil] at h

/-- The function is essentially bounded by `bound 0`. -/
theorem ae_abs_le (hf : IsWkInfty f k) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |f x| ≤ hf.bound 0 := by
  have h := hf.ess_bdd [] (by simp)
  rwa [hf.D_nil] at h

/-- The order-one member of the family is a weak partial derivative of the function. -/
theorem hasWeakPartial_D (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    HasWeakPartial ℓ f (hf.D [ℓ]) := by
  have h := hf.D_step ℓ [] (by simp)
  rwa [hf.D_nil] at h

/-- The order-one member of the family is measurable. -/
theorem measurable_D_singleton (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    Measurable (hf.D [ℓ]) := hf.D_meas [ℓ] (by simp)

/-- The order-one member of the family is essentially bounded by `bound 1`. -/
theorem ae_abs_D_singleton_le (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hf.D [ℓ] x| ≤ hf.bound 1 := by
  have h := hf.ess_bdd [ℓ] (by simp)
  simpa using h

end IsWkInfty

/-! ### Weights with a weak derivative -/

/-- **A bounded weight with a bounded weak derivative.** The function `a` is measurable and
essentially bounded, and so is `a'`, which is its weak `ℓ`-derivative. This is the hypothesis of
`HasWeakDerivOn.mul_isWkInfty_left`. -/
structure WeakBddPair (ℓ : Fin d) (a a' : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  /-- The weight is measurable. -/
  measurable : Measurable a
  /-- The derivative is measurable. -/
  measurable_deriv : Measurable a'
  /-- `a'` is the weak `ℓ`-derivative of `a`. -/
  hasWeakPartial : HasWeakPartial ℓ a a'
  /-- The weight is essentially bounded. -/
  bdd : ∃ M, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ M
  /-- The derivative is essentially bounded. -/
  bdd_deriv : ∃ M, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a' x| ≤ M

/-- A `C¹` function with essentially bounded value and `ℓ`-derivative is a `WeakBddPair` with
its classical derivative. -/
theorem WeakBddPair.of_contDiff {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    (ℓ : Fin d) (hM : ∃ M, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ M)
    (hdM : ∃ M, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |partialD ℓ a x| ≤ M) :
    WeakBddPair ℓ a (partialD ℓ a) where
  measurable := ha.continuous.measurable
  measurable_deriv := ((ha.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable
  hasWeakPartial := hasWeakPartial_partialD ha ℓ
  bdd := hM
  bdd_deriv := hdM

/-- A `W^{k+1,∞}` function and the first member of its family form a `WeakBddPair`. -/
theorem IsWkInfty.weakBddPair {f : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ}
    (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) : WeakBddPair ℓ f (hf.D [ℓ]) :=
  ⟨hf.measurable_self, hf.measurable_D_singleton ℓ, hf.hasWeakPartial_D ℓ,
    ⟨_, hf.ae_abs_le⟩, ⟨_, hf.ae_abs_D_singleton_le ℓ⟩⟩

/-- An entry of a `W^{k+1,∞}` coefficient bundle and its first-order member form a
`WeakBddPair`. -/
theorem IsWkInftyCoeff.weakBddPair {A : EllipticCoeff d} {k : ℕ}
    (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    WeakBddPair ℓ (fun x => A.a x i j) (hA.D [ℓ] i j) :=
  (hA.entry i j).weakBddPair ℓ

/-- The first-order member of a `W^{k+2,∞}` bundle and its second-order member form a
`WeakBddPair`. -/
theorem IsWkInftyCoeff.weakBddPair_D {A : EllipticCoeff d} {k : ℕ}
    (hA : IsWkInftyCoeff A (k + 2)) (m ℓ i j : Fin d) :
    WeakBddPair m (hA.D [ℓ] i j) (hA.D [m, ℓ] i j) :=
  ⟨hA.measurable_D_singleton ℓ i j, hA.measurable_D_pair m ℓ i j,
    hA.hasWeakPartial_D_singleton m ℓ i j, ⟨_, hA.ae_abs_D_singleton_le ℓ i j⟩,
    ⟨_, hA.ae_abs_D_pair_le m ℓ i j⟩⟩

variable {V : Set (EuclideanSpace ℝ (Fin d))}

/-- A bounded measurable weight times an `L²(V)` class times a test function is integrable. -/
theorem integrable_coeff_mul_testFn {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hM : ∃ M, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |f x| ≤ M) (g : L2D V)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψc : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) :
    Integrable (fun x => f x * (g x : ℝ) * ψ x) (volume.restrict V) := by
  obtain ⟨M, hM⟩ := hM
  refine (integrable_mul_testFn (mulCoeffL hf (ae_restrict_of_ae hM) g) hψc hψcs).congr ?_
  filter_upwards [mulCoeffL_coeFn hf (ae_restrict_of_ae hM) g] with x hx
  rw [hx]

/-- **Moving `∂_ℓ` onto a weighted product.** If `g` has weak `ℓ`-derivative `g'` on `V` and
`(a, a')` is a `WeakBddPair`, then
`∫_V a·g·∂_ℓψ = -∫_V (a'·g + a·g') ψ` for every test function `ψ` supported in `V`. -/
theorem WeakBddPair.integral_mul_partialD_eq {ℓ : Fin d} {a a' : EuclideanSpace ℝ (Fin d) → ℝ}
    (hp : WeakBddPair ℓ a a') {g g' : L2D V} (hg : HasWeakDerivOn V ℓ g g')
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψc : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) (hψV : tsupport ψ ⊆ V) :
    ∫ x in V, a x * (g x : ℝ) * partialD ℓ ψ x
      = -∫ x in V, (a' x * (g x : ℝ) + a x * (g' x : ℝ)) * ψ x := by
  obtain ⟨M, hM⟩ := hp.bdd
  obtain ⟨M', hM'⟩ := hp.bdd_deriv
  have hMV := ae_restrict_of_ae (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (s := V) hM
  have hMV' := ae_restrict_of_ae (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (s := V) hM'
  have hmove := HasWeakDerivOn.mul_isWkInfty_left ℓ hg hp.measurable hp.measurable_deriv
    hp.hasWeakPartial hM hM' _ (mulCoeffL_coeFn hp.measurable hMV g) _
    (mulCoeffL_add_coeFn hp.measurable_deriv hMV' hp.measurable hMV g g') ψ hψc hψcs hψV
  refine Eq.trans (integral_congr_ae ?_) (hmove.trans (congrArg Neg.neg (integral_congr_ae ?_)))
  · filter_upwards [mulCoeffL_coeFn hp.measurable hMV g] with x hx
    rw [hx]
  · filter_upwards [mulCoeffL_add_coeFn hp.measurable_deriv hMV' hp.measurable hMV g g'] with x hx
    rw [hx]

/-! ### Differentiated identity -/

/-- **Differentiated weak formulation (divergence-datum form).** Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2. Let `u` satisfy the localised weak identity `hLoc` on
`V`, with first and second weak derivatives `Du` and `D2`. If every coefficient is a
`WeakBddPair` in the direction `ℓ`, with derivatives `da`, `db` and `dc`, then for every test
function `φ` supported in `V`,
`∑ ∫_V a_{ij}(∂ₗ∂ᵢu) ∂ⱼφ + ∑ ∫_V (∂_ℓ a_{ij})(∂ᵢu) ∂ⱼφ = ∫_V (∂_ℓf) φ
  - ∑ ∫_V [(∂_ℓ b_i)(∂ᵢu)+b_i(∂ₗ∂ᵢu)] φ - ∫_V [(∂_ℓ c)u + c(∂_ℓu)] φ`.

The proof tests `hLoc` against `∂_ℓφ` and moves `∂_ℓ` onto the solution in each term. -/
theorem differentiated_weakForm_div_of_pairs {V : Set (EuclideanSpace ℝ (Fin d))}
    (Op : FullEllipticOp d) (ℓ : Fin d)
    (da : Fin d → Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (db : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (dc : EuclideanSpace ℝ (Fin d) → ℝ)
    (ha : ∀ i j, WeakBddPair ℓ (fun x => Op.a x i j) (da i j))
    (hb : ∀ i, WeakBddPair ℓ (fun x => Op.b x i) (db i)) (hc : WeakBddPair ℓ Op.c dc)
    (u_V : L2D V) (Du : Fin d → L2D V) (D2 : Fin d → Fin d → L2D V) (f_V Df : L2D V)
    (hDu_D2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (hu_Duℓ : HasWeakDerivOn V ℓ u_V (Du ℓ))
    (hf_Df : HasWeakDerivOn V ℓ f_V Df)
    (hLoc : ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
        HasCompactSupport v → tsupport v ⊆ V →
        (∑ i, ∑ j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j v x)
          + (∑ i, ∫ x in V, Op.b x i * (Du i x : ℝ) * v x)
          + (∫ x in V, Op.c x * (u_V x : ℝ) * v x)
          = ∫ x in V, (f_V x : ℝ) * v x)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
      + (∑ i, ∑ j, ∫ x in V, da i j x * (Du i x : ℝ) * partialD j φ x)
    = (∫ x in V, (Df x : ℝ) * φ x)
      - (∑ i, ∫ x in V, (db i x * (Du i x : ℝ) + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
      - (∫ x in V, (dc x * (u_V x : ℝ) + Op.c x * (Du ℓ x : ℝ)) * φ x) := by
  have hstar := hLoc (partialD ℓ φ) (contDiff_partialD hφc ℓ) (hasCompactSupport_partialD hφcs ℓ)
    ((tsupport_partialD_subset ℓ φ).trans hφV)
  have hprin : ∀ i j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j (partialD ℓ φ) x
      = -((∫ x in V, da i j x * (Du i x : ℝ) * partialD j φ x)
        + ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x) := by
    intro i j
    obtain ⟨hψc, hψcs, hψV⟩ := isTest_partialD hφc hφcs hφV j
    rw [← partialD_partialD_swap hφc j ℓ, (ha i j).integral_mul_partialD_eq (hDu_D2 i) hψc hψcs hψV,
      ← integral_add (integrable_coeff_mul_testFn (ha i j).measurable_deriv (ha i j).bdd_deriv
        (Du i) hψc hψcs) (integrable_coeff_mul_testFn (ha i j).measurable (ha i j).bdd (D2 ℓ i)
        hψc hψcs)]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have htrans : ∀ i, ∫ x in V, Op.b x i * (Du i x : ℝ) * partialD ℓ φ x
      = -∫ x in V, (db i x * (Du i x : ℝ) + Op.b x i * (D2 ℓ i x : ℝ)) * φ x :=
    fun i => (hb i).integral_mul_partialD_eq (hDu_D2 i) hφc hφcs hφV
  have hzero := hc.integral_mul_partialD_eq hu_Duℓ hφc hφcs hφV
  have hdat := hf_Df φ hφc hφcs hφV
  simp only [hprin, htrans, Finset.sum_neg_distrib, Finset.sum_add_distrib] at hstar
  linarith [hstar, hzero, hdat]

/-- **Differentiated weak formulation (strong-datum form).** Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2, equation (34). In addition to the data of
`differentiated_weakForm_div_of_pairs`, the derivative `da i j` of each principal coefficient
is a `WeakBddPair` in every direction `j`, with derivative `dda i j`, and `D2` is the full
family of second derivatives of `Du`. Moving `∂ⱼ` off the commutator merges the second block of
the left-hand side into the datum, leaving
`∑ ∫_V a_{ij}(∂ₗ∂ᵢu) ∂ⱼφ = ∫_V f_ℓ · φ` with the datum `f_ℓ` delivered as an explicit sum of
integrals. -/
theorem differentiated_weakForm_of_pairs {V : Set (EuclideanSpace ℝ (Fin d))}
    (Op : FullEllipticOp d) (ℓ : Fin d)
    (da dda : Fin d → Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (db : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (dc : EuclideanSpace ℝ (Fin d) → ℝ)
    (ha : ∀ i j, WeakBddPair ℓ (fun x => Op.a x i j) (da i j))
    (hda : ∀ i j, WeakBddPair j (da i j) (dda i j))
    (hb : ∀ i, WeakBddPair ℓ (fun x => Op.b x i) (db i)) (hc : WeakBddPair ℓ Op.c dc)
    (u_V : L2D V) (Du : Fin d → L2D V) (D2 : Fin d → Fin d → L2D V) (f_V Df : L2D V)
    (hDu_D2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (hD2_j : ∀ i j, HasWeakDerivOn V j (Du i) (D2 j i))
    (hu_Duℓ : HasWeakDerivOn V ℓ u_V (Du ℓ))
    (hf_Df : HasWeakDerivOn V ℓ f_V Df)
    (hLoc : ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
        HasCompactSupport v → tsupport v ⊆ V →
        (∑ i, ∑ j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j v x)
          + (∑ i, ∫ x in V, Op.b x i * (Du i x : ℝ) * v x)
          + (∫ x in V, Op.c x * (u_V x : ℝ) * v x)
          = ∫ x in V, (f_V x : ℝ) * v x)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
    = (∫ x in V, (Df x : ℝ) * φ x)
      - (∑ i, ∫ x in V, (db i x * (Du i x : ℝ) + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
      - (∫ x in V, (dc x * (u_V x : ℝ) + Op.c x * (Du ℓ x : ℝ)) * φ x)
      + (∑ i, ∑ j, ∫ x in V, (dda i j x * (Du i x : ℝ) + da i j x * (D2 j i x : ℝ)) * φ x) := by
  have hdiv := differentiated_weakForm_div_of_pairs Op ℓ da db dc ha hb hc u_V Du D2 f_V Df
    hDu_D2 hu_Duℓ hf_Df hLoc hφc hφcs hφV
  have hCG : ∀ i j, ∫ x in V, da i j x * (Du i x : ℝ) * partialD j φ x
      = -∫ x in V, (dda i j x * (Du i x : ℝ) + da i j x * (D2 j i x : ℝ)) * φ x :=
    fun i j => (hda i j).integral_mul_partialD_eq (hD2_j i j) hφc hφcs hφV
  simp only [hCG, Finset.sum_neg_distrib] at hdiv
  linarith [hdiv]

/-- **Differentiated weak formulation for `W^{2,∞}` principal and `W^{1,∞}` lower-order
coefficients.** The strong-datum form with every derivative of a coefficient read off a
`W^{k,∞}` bundle, so that no coefficient is asked to be differentiable. -/
theorem differentiated_weakForm_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))}
    (Op : FullEllipticOp d) {k m : ℕ} (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2))
    (hbc : IsWkInftyLower Op (m + 1)) (ℓ : Fin d)
    (u_V : L2D V) (Du : Fin d → L2D V) (D2 : Fin d → Fin d → L2D V) (f_V Df : L2D V)
    (hDu_D2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (hD2_j : ∀ i j, HasWeakDerivOn V j (Du i) (D2 j i))
    (hu_Duℓ : HasWeakDerivOn V ℓ u_V (Du ℓ))
    (hf_Df : HasWeakDerivOn V ℓ f_V Df)
    (hLoc : ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
        HasCompactSupport v → tsupport v ⊆ V →
        (∑ i, ∑ j, ∫ x in V, Op.a x i j * (Du i x : ℝ) * partialD j v x)
          + (∑ i, ∫ x in V, Op.b x i * (Du i x : ℝ) * v x)
          + (∫ x in V, Op.c x * (u_V x : ℝ) * v x)
          = ∫ x in V, (f_V x : ℝ) * v x)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
    = (∫ x in V, (Df x : ℝ) * φ x)
      - (∑ i, ∫ x in V, ((hbc.bReg i).D [ℓ] x * (Du i x : ℝ)
                          + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
      - (∫ x in V, (hbc.cReg.D [ℓ] x * (u_V x : ℝ) + Op.c x * (Du ℓ x : ℝ)) * φ x)
      + (∑ i, ∑ j, ∫ x in V, (hA.D [j, ℓ] i j x * (Du i x : ℝ)
          + hA.D [ℓ] i j x * (D2 j i x : ℝ)) * φ x) :=
  differentiated_weakForm_of_pairs Op ℓ (fun i j => hA.D [ℓ] i j) (fun i j => hA.D [j, ℓ] i j)
    (fun i => (hbc.bReg i).D [ℓ]) (hbc.cReg.D [ℓ])
    (fun i j => hA.weakBddPair ℓ i j) (fun i j => hA.weakBddPair_D j ℓ i j)
    (fun i => (hbc.bReg i).weakBddPair ℓ) (hbc.cReg.weakBddPair ℓ)
    u_V Du D2 f_V Df hDu_D2 hD2_j hu_Duℓ hf_Df hLoc hφc hφcs hφV

end EllipticPdes.Regularity
