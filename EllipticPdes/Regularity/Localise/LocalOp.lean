/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Localise.CutoffProduct

/-!
# Localising coefficients smooth on an open set into a global elliptic operator

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 states its conclusion for
coefficients and a datum smooth on the whole region `Ω`, with no bound assumed anywhere. The
interior-regularity chain in this development runs on a `FullEllipticOp`, whose coefficients are
global, essentially bounded and measurable, which is a different hypothesis shape. This file
bridges the two: `SmoothOpOn` states coefficients smooth and uniformly elliptic on an open set
`U` with no global bound, and `localOp` blends them against `λ I`, `0`, `0` outside a cutoff to
build a `FullEllipticOp` agreeing with the given coefficients wherever the cutoff is `1`.

## The blend

For a test function `χ` of `U`, valued in `[0, 1]`,

* `a_χ = λ I + χ (a − λ I) = χ a + (1 − χ) λ I`,
* `b_χ = χ b`,
* `c_χ = χ c`.

Wherever `χ = 1` the blend agrees with `P.a`, `P.b`, `P.c`; wherever `χ = 0` it reduces to the
constant-coefficient Laplacian at level `λ`, which is trivially uniformly elliptic, bounded and
of every regularity class. Ellipticity of the blend follows from ellipticity of `P.a` on `U` and
convexity of the quadratic form in `χ` between the two extremes, needing no symmetry.

## Main declarations

* `PrincipalOn`: a principal part of class `C^m` on `U`, uniformly elliptic almost everywhere
  on `U`, and `blendOp`, the blended global operator with lower-order coefficients supplied.
* `SmoothOpOn`: coefficients smooth and uniformly elliptic a.e. on an open set, unbounded.
* `localOp`: the blended global operator of a `SmoothOpOn`.
* `exists_localOp`: for every compact `K ⊆ U` there is a cutoff and an open `W ⊇ K` on which
  `localOp` agrees with the given coefficients and meets every regularity mixin
  `interior_smooth` asks for.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **Principal part of class `C^m` on an open set.** Entries of class `C^m` on `U`, uniformly
elliptic almost everywhere on `U` with constant `lam > 0`, with no bound, no symmetry and nothing
asked off `U`. -/
structure PrincipalOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (m : ℕ∞) where
  /-- The principal-part coefficient matrix. -/
  a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ
  /-- The ellipticity constant. -/
  lam : ℝ
  /-- The ellipticity constant is strictly positive. -/
  lam_pos : 0 < lam
  /-- Every entry is of class `C^m` on `U`. -/
  contDiffOn : ∀ i j, ContDiffOn ℝ m (fun x => a x i j) U
  /-- Uniform ellipticity almost everywhere on `U`. -/
  elliptic : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Fin d → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j

namespace PrincipalOn

variable {U : Set (EuclideanSpace ℝ (Fin d))} {m : ℕ∞} (P : PrincipalOn d U m)

/-- The principal part shifted down to `λ I`, cut off by `χ`. -/
def gA (χ : EuclideanSpace ℝ (Fin d) → ℝ) (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  χ x * (P.a x i j - P.lam * (1 : Matrix (Fin d) (Fin d) ℝ) i j)

/-- The blended principal part `a_χ = λ I + χ (a − λ I) = χ a + (1 − χ) λ I`. -/
def aT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d) : ℝ :=
  P.lam * (1 : Matrix (Fin d) (Fin d) ℝ) i j + P.gA χ i j x

variable {χ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- `PrincipalOn.gA` is of class `C^m` for a test function `χ` on an open set. -/
theorem gA_contDiff (hU : IsOpen U) (hχ : IsTestFn U χ) (i j : Fin d) :
    ContDiff ℝ m (P.gA χ i j) :=
  contDiff_mul_of_contDiffOn hU hχ ((P.contDiffOn i j).sub contDiffOn_const)

/-- `PrincipalOn.gA` has compact support for a test function `χ`. -/
theorem gA_hasCompactSupport (hχ : IsTestFn U χ) (i j : Fin d) :
    HasCompactSupport (P.gA χ i j) :=
  hasCompactSupport_mul hχ

/-- The quadratic form of the blend, as a convex combination of `λ |ξ|²` and the quadratic form
of `a`. -/
theorem quad_aT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (ξ : Fin d → ℝ) :
    ∑ i, ∑ j, P.aT χ x i j * ξ i * ξ j
      = P.lam * ∑ i, ξ i ^ 2
        + χ x * (∑ i, ∑ j, P.a x i j * ξ i * ξ j - P.lam * ∑ i, ξ i ^ 2) := by
  simp only [aT, gA, Matrix.one_apply, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring_nf

/-- **Uniform ellipticity of the blend on all of `ℝᵈ`, at the constant `λ`.** Where `χ = 0` the
blend is the constant-coefficient form `λ I`, trivially elliptic at `λ`; where `χ ∈ (0, 1]` and
`x ∈ U`, the quadratic form is a convex combination of `λ |ξ|²` and a quantity at least
`λ |ξ|²` by ellipticity of `P.a`, hence itself at least `λ |ξ|²`. No symmetry of `P.a` enters. -/
theorem aT_elliptic (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hUm : MeasurableSet U) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ∀ ξ : Fin d → ℝ,
      P.lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.aT χ x i j * ξ i * ξ j := by
  filter_upwards [(ae_restrict_iff' hUm).1 P.elliptic] with x hx ξ
  rw [P.quad_aT]
  by_cases hxU : x ∈ U
  · have := hx hxU ξ
    have h0 := (hχ01 x).1
    nlinarith
  · have : χ x = 0 := by
      by_contra hne
      exact hxU (hχ.2.2 (subset_tsupport _ hne))
    simp [this]

/-- **`C^k` bundle of the blended principal part.** Each entry is a constant plus a compactly
supported function of class `C^m`, so its derivatives of order `1` to `k ≤ m` are bounded. Any
coefficient bundle `A` with `A.a = P.aT χ` has it. -/
theorem nonempty_isCkCoeff (hU : IsOpen U) (hχ : IsTestFn U χ) (A : EllipticCoeff d)
    (hA : A.a = P.aT χ) {k : ℕ} (hk : (k : ℕ∞) ≤ m) : Nonempty (IsCkCoeff A k) := by
  have h : ∀ ij : Fin d × Fin d, ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ j, 1 ≤ j → j ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => P.lam * (1 : Matrix (Fin d) (Fin d) ℝ) ij.1 ij.2
        + P.gA χ ij.1 ij.2 y) x‖ ≤ B j := fun ij => by
    obtain ⟨B, hB0, hB⟩ := exists_iteratedFDeriv_bound_const_add (P.gA_contDiff hU hχ ij.1 ij.2)
      (P.gA_hasCompactSupport hχ ij.1 ij.2) (P.lam * (1 : Matrix (Fin d) (Fin d) ℝ) ij.1 ij.2)
    exact ⟨B, hB0, fun j hj hjk => hB j hj ((by exact_mod_cast hjk : (j : ℕ∞) ≤ k).trans hk)⟩
  choose B hB0 hB using h
  exact ⟨{ contDiff := fun i j => by
              rw [hA]
              exact (contDiff_const.add (P.gA_contDiff hU hχ i j)).of_le (by exact_mod_cast hk)
           bound := fun j => ∑ ij, B ij j
           bound_nonneg := fun j => Finset.sum_nonneg fun ij _ => hB0 ij j
           iteratedFDeriv_bdd := fun i j k hk hkm x => by
             rw [hA]
             exact (hB (i, j) k hk hkm x).trans
               (Finset.single_le_sum (f := fun ij => B ij k) (fun ij _ => hB0 ij k)
                 (Finset.mem_univ (i, j))) }⟩

/-- The blended principal part is the given one wherever the cutoff is one. -/
theorem aT_eq_of_eq_one {χ : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : χ x = 1) (i j : Fin d) : P.aT χ x i j = P.a x i j := by
  simp [aT, gA, hx]

end PrincipalOn

/-- **Blended operator.** Principal part `λ I + χ (a − λ I)`, and lower-order coefficients
`b`, `c` supplied measurable and essentially bounded on the whole space. -/
def blendOp {U : Set (EuclideanSpace ℝ (Fin d))} {m : ℕ∞} (P : PrincipalOn d U m) (hU : IsOpen U)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ) {Bs Cs : ℝ}
    (hBs : 0 ≤ Bs) (hCs : 0 ≤ Cs)
    (hbm : ∀ i, Measurable fun x => b x i) (hcm : Measurable c)
    (hbb : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |b x i| ≤ Bs)
    (hcb : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Cs) :
    FullEllipticOp d where
  a := P.aT χ
  lam := P.lam
  Λ := P.lam + ∑ ij : Fin d × Fin d, ⨆ x, |P.gA χ ij.1 ij.2 x|
  lam_pos := P.lam_pos
  Λ_nonneg := add_nonneg P.lam_pos.le <| Finset.sum_nonneg fun ij _ =>
    (P.gA_hasCompactSupport hχ ij.1 ij.2).iSup_abs_nonneg (P.gA_contDiff hU hχ ij.1 ij.2).continuous
  measurable i j := (continuous_const.add (P.gA_contDiff hU hχ i j).continuous).measurable
  bdd i j := Filter.Eventually.of_forall fun x => by
    have h := abs_le_sum_iSup_abs (f := fun ij : Fin d × Fin d => P.gA χ ij.1 ij.2)
      (fun ij => (P.gA_contDiff hU hχ ij.1 ij.2).continuous)
      (fun ij => P.gA_hasCompactSupport hχ ij.1 ij.2) (i, j) x
    have hδ : |P.lam * (1 : Matrix (Fin d) (Fin d) ℝ) i j| ≤ P.lam := by
      rw [Matrix.one_apply]; split_ifs <;> simp [abs_of_pos P.lam_pos, P.lam_pos.le]
    exact (abs_add_le _ _).trans (add_le_add hδ h)
  elliptic := P.aT_elliptic hχ hχ01 hU.measurableSet
  b := b
  c := c
  Bsup := Bs
  Csup := Cs
  Bsup_nonneg := hBs
  Csup_nonneg := hCs
  b_meas := hbm
  c_meas := hcm
  b_bdd := hbb
  c_bdd := hcb

/-- **Coefficients of Evans §6.3.1, Theorem 3.** Smooth on the open set `U`, uniformly elliptic
almost everywhere on `U`, with no global bound, no measurability asked off `U` and no symmetry
asked anywhere. This is the hypothesis shape the theorem's classical statement supplies, before
it is localised into the global bounded-measurable shape `FullEllipticOp` asks for. -/
structure SmoothOpOn (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) extends PrincipalOn d U ⊤ where
  /-- The transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- The zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- Every transport component is smooth on `U`. -/
  b_smooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => b x i) U
  /-- The zeroth-order coefficient is smooth on `U`. -/
  c_smooth : ContDiffOn ℝ (⊤ : ℕ∞) c U

namespace SmoothOpOn

variable {U : Set (EuclideanSpace ℝ (Fin d))} (P : SmoothOpOn d U)

/-- The cut-off transport field. -/
def bT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ :=
  χ x * P.b x i

/-- The cut-off zeroth-order coefficient. -/
def cT (χ : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := χ x * P.c x

variable (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
include hU hχ

/-- `SmoothOpOn.bT` is smooth in `x` for each index. -/
theorem bT_contDiff (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun x => P.bT χ x i) :=
  contDiff_mul_of_contDiffOn hU hχ (P.b_smooth i)

/-- `SmoothOpOn.cT` is smooth. -/
theorem cT_contDiff : ContDiff ℝ (⊤ : ℕ∞) (P.cT χ) :=
  contDiff_mul_of_contDiffOn hU hχ P.c_smooth

end SmoothOpOn

open SmoothOpOn

variable {U : Set (EuclideanSpace ℝ (Fin d))}

/-- **The localised operator.** Global coefficients on `EuclideanSpace ℝ (Fin d)`, equal to
`λ I + χ (a − λ I)`, `χ b`, `χ c`, meeting every hypothesis `FullEllipticOp` asks: measurability
and boundedness come from smoothness plus compact support, and ellipticity from `aT_elliptic`. -/
def localOp (P : SmoothOpOn d U) (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) : FullEllipticOp d :=
  have hbc : ∀ i, Continuous fun x => P.bT χ x i := fun i => (P.bT_contDiff hU hχ i).continuous
  have hbs : ∀ i, HasCompactSupport fun x => P.bT χ x i := fun i =>
    hasCompactSupport_mul (g := fun x => P.b x i) hχ
  blendOp P.toPrincipalOn hU hχ hχ01 (P.bT χ) (P.cT χ)
    (Bs := ∑ i, ⨆ x, |P.bT χ x i|) (Cs := ⨆ x, |P.cT χ x|)
    (Finset.sum_nonneg fun i _ => (hbs i).iSup_abs_nonneg (hbc i))
    ((hasCompactSupport_mul (g := P.c) hχ).iSup_abs_nonneg (P.cT_contDiff hU hχ).continuous)
    (fun i => (hbc i).measurable) (P.cT_contDiff hU hχ).continuous.measurable
    (fun i => Filter.Eventually.of_forall fun x => abs_le_sum_iSup_abs hbc hbs i x)
    (Filter.Eventually.of_forall fun x => ((hasCompactSupport_mul (g := P.c) hχ).abs_le_iSup_abs
      (P.cT_contDiff hU hχ).continuous x))

variable (P : SmoothOpOn d U) (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ}
  (hχ : IsTestFn U χ) (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1)

/-- The localised principal part meets the `C¹` regularity `interior_smooth` asks for. -/
theorem nonempty_isC1Coeff : Nonempty (IsC1Coeff (localOp P hU hχ hχ01).toEllipticCoeff) :=
  ⟨(Classical.choice
    (P.toPrincipalOn.nonempty_isCkCoeff hU hχ _ rfl (k := 1) le_top)).toIsC1Coeff le_rfl⟩

/-- The localised principal part lies in `W^{k,∞}` at every order, through the `Cᵏ` bundle. -/
theorem nonempty_isWkInftyCoeff (k : ℕ) :
    Nonempty (IsWkInftyCoeff (localOp P hU hχ hχ01).toEllipticCoeff k) :=
  ⟨(Classical.choice
    (P.toPrincipalOn.nonempty_isCkCoeff hU hχ _ rfl (k := k) le_top)).toIsWkInftyCoeff⟩

/-- The localised lower-order coefficients lie in `W^{k,∞}` at every order, uniformly. -/
theorem nonempty_isWkInftyLower (k : ℕ) :
    Nonempty (IsWkInftyLower (localOp P hU hχ hχ01) k) :=
  ⟨.ofBundles
    (fun i => Classical.choice (nonempty_isWkInfty le_top (P.bT_contDiff hU hχ i)
      (hasCompactSupport_mul (g := fun x => P.b x i) hχ)))
    (Classical.choice (nonempty_isWkInfty le_top (P.cT_contDiff hU hχ)
      (hasCompactSupport_mul hχ)))⟩

/-! ### Agreement on the region where the cutoff is one -/

/-- The localised operator has the same `a` as `P` on any set where `χ = 1`. -/
theorem eqOn_a {W : Set (EuclideanSpace ℝ (Fin d))} (hW : ∀ x ∈ W, χ x = 1) :
    ∀ x ∈ W, (localOp P hU hχ hχ01).a x = P.a x := by
  intro x hx
  funext i j
  exact P.toPrincipalOn.aT_eq_of_eq_one (hW x hx) i j

/-- The localised operator has the same `b` as `P` on any set where `χ = 1`. -/
theorem eqOn_b {W : Set (EuclideanSpace ℝ (Fin d))} (hW : ∀ x ∈ W, χ x = 1) :
    ∀ x ∈ W, (localOp P hU hχ hχ01).b x = P.b x := by
  intro x hx
  funext i
  simp [localOp, blendOp, bT, hW x hx]

/-- The localised operator has the same `c` as `P` on any set where `χ = 1`. -/
theorem eqOn_c {W : Set (EuclideanSpace ℝ (Fin d))} (hW : ∀ x ∈ W, χ x = 1) :
    ∀ x ∈ W, (localOp P hU hχ hχ01).c x = P.c x := by
  intro x hx
  simp [localOp, blendOp, cT, hW x hx]

/-- The cutoff of `exists_isTestFn_one_nhdsSet_of_isCompact` and the open interior of the set
where it is one, which contains the compact set and has closure inside the support of the
cutoff, hence inside `U`. -/
theorem exists_cutoff_interior_one {K : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (χ : EuclideanSpace ℝ (Fin d) → ℝ) (_ : IsTestFn U χ) (_ : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
      (W : Set (EuclideanSpace ℝ (Fin d))), IsOpen W ∧ K ⊆ W ∧ closure W ⊆ tsupport χ ∧
        ∀ x ∈ W, χ x = 1 := by
  obtain ⟨χ, hχ, hone, hχ01⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hK hU hKU
  have hW1 : ∀ x ∈ interior {x | χ x = 1}, χ x = 1 := fun x hx =>
    interior_subset (s := {x | χ x = 1}) hx
  exact ⟨χ, hχ, hχ01, interior {x | χ x = 1}, isOpen_interior,
    subset_interior_iff_mem_nhdsSet.2 hone,
    closure_minimal (fun x hx => subset_tsupport _ (by simp [hW1 x hx])) (isClosed_tsupport _),
    hW1⟩

/-- **Localisation of the coefficients.** For every compact `K ⊆ U` there are a cutoff `χ` and an
open `W ⊇ K`, with `closure W` compact inside `U`, on which the localised operator agrees with
the given coefficients, and the localised operator meets every regularity mixin `interior_smooth`
asks for. The cutoff comes from `exists_isTestFn_one_nhdsSet_of_isCompact` and `W` is the
interior of the region on which it is `1`. -/
theorem exists_localOp {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsTestFn U χ)
      (hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (W : Set (EuclideanSpace ℝ (Fin d))),
      IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ (∀ x ∈ W, χ x = 1) ∧
      (localOp P hU hχ hχ01).lam = P.lam ∧
      (∀ x ∈ W, (localOp P hU hχ hχ01).a x = P.a x) ∧
      (∀ x ∈ W, (localOp P hU hχ hχ01).b x = P.b x) ∧
      (∀ x ∈ W, (localOp P hU hχ hχ01).c x = P.c x) ∧
      Nonempty (IsC1Coeff (localOp P hU hχ hχ01).toEllipticCoeff) ∧
      (∀ k, Nonempty (IsWkInftyCoeff (localOp P hU hχ hχ01).toEllipticCoeff k)) ∧
      (∀ k, Nonempty (IsWkInftyLower (localOp P hU hχ hχ01) k)) := by
  obtain ⟨χ, hχ, hχ01, W, hWo, hKW, hclW, hW1⟩ := exists_cutoff_interior_one hU hK hKU
  exact ⟨χ, hχ, hχ01, W, hWo, hKW, hχ.2.1.of_isClosed_subset isClosed_closure hclW,
    hclW.trans hχ.2.2, hW1, rfl, eqOn_a P hU hχ hχ01 hW1, eqOn_b P hU hχ hχ01 hW1,
    eqOn_c P hU hχ hχ01 hW1, nonempty_isC1Coeff P hU hχ hχ01,
    nonempty_isWkInftyCoeff P hU hχ hχ01, nonempty_isWkInftyLower P hU hχ hχ01⟩

end EllipticPdes.Regularity
