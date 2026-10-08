import KLS.LocalWeakAlgebra

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem memLp_two_on_compacts_of_top {f : Space n → ℝ}
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f ∞ (volume.restrict K)) :
    ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K) := by
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (hf K hK).mono_exponent (by simp)

theorem memLp_top_finset_product {ι : Type*} (s : Finset ι)
    {f : ι → Space n → ℝ} {μ : Measure (Space n)}
    (hf : ∀ a ∈ s, MemLp (f a) ∞ μ) :
    MemLp (fun x => ∏ a ∈ s, f a x) ∞ μ := by
  simpa only [ENNReal.inv_top, Finset.sum_const_zero, ENNReal.inv_zero] using MemLp.fun_prod hf

theorem memLp_two_finset_product_derivative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {f F : ι → Space n → ℝ} {μ : Measure (Space n)}
    (hf : ∀ a ∈ s, MemLp (f a) ∞ μ)
    (hF : ∀ a ∈ s, MemLp (F a) 2 μ) :
    MemLp (fun x => ∑ a ∈ s, (∏ b ∈ s.erase a, f b x) * F a x) 2 μ := by
  apply memLp_finsetSum
  intro a ha
  exact (memLp_top_finset_product (s.erase a) (fun b hb => hf b (Finset.mem_of_mem_erase hb))).mul (hF a ha)

lemma finite_product_derivative_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι) (ha : a ∉ s) (f F : ι → ℝ) :
    (∑ b ∈ insert a s, (∏ c ∈ (insert a s).erase b, f c) * F b) =
      F a * (∏ b ∈ s, f b) + f a * (∑ b ∈ s, (∏ c ∈ s.erase b, f c) * F b) := by
  rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := by rintro rfl; exact ha hb
    have hae : a ∉ s.erase b := fun h => ha (Finset.mem_of_mem_erase h)
    rw [Finset.erase_insert_of_ne hba.symm, Finset.prod_insert hae]
    ring

/-- Finite products of locally bounded functions with actual local L2
weak derivatives obey the full Leibniz formula. -/
theorem hasLocalWeakCoordinateDerivative_finset_product
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f F : ι → Space n → ℝ} {i : Fin n}
    (hF : ∀ a ∈ s, HasLocalWeakCoordinateDerivative (f a) (F a) i)
    (hf : ∀ a ∈ s, ∀ K : Set (Space n), IsCompact K → MemLp (f a) ∞ (volume.restrict K))
    (hFloc : ∀ a ∈ s, ∀ K : Set (Space n), IsCompact K → MemLp (F a) 2 (volume.restrict K)) :
    HasLocalWeakCoordinateDerivative (fun x => ∏ a ∈ s, f a x)
      (fun x => ∑ a ∈ s, (∏ b ∈ s.erase a, f b x) * F a x) i := by
  induction s using Finset.induction_on with
  | empty => simpa using hasLocalWeakCoordinateDerivative_const (n := n) 1 i
  | @insert a s ha ih =>
    have hs (b : ι) (hb : b ∈ s) : b ∈ insert a s := Finset.mem_insert_of_mem hb
    have hprodb : ∀ K : Set (Space n), IsCompact K →
        MemLp (fun x => ∏ b ∈ s, f b x) ∞ (volume.restrict K) :=
      fun K hK => memLp_top_finset_product s (fun b hb => hf b (hs b hb) K hK)
    have hprodF : ∀ K : Set (Space n), IsCompact K →
        MemLp (fun x => ∑ b ∈ s, (∏ c ∈ s.erase b, f c x) * F b x) 2 (volume.restrict K) :=
      fun K hK => memLp_two_finset_product_derivative s
        (fun b hb => hf b (hs b hb) K hK) (fun b hb => hFloc b (hs b hb) K hK)
    have hp := (hF a (Finset.mem_insert_self _ _)).mul
      (ih (fun b hb => hF b (hs b hb)) (fun b hb => hf b (hs b hb))
        (fun b hb => hFloc b (hs b hb)))
      (memLp_two_on_compacts_of_top (hf a (Finset.mem_insert_self _ _)))
      (memLp_two_on_compacts_of_top hprodb) (hFloc a (Finset.mem_insert_self _ _)) hprodF
    have he : (fun x => ∏ b ∈ insert a s, f b x) = fun x => f a x * ∏ b ∈ s, f b x := by
      funext x
      exact Finset.prod_insert ha
    have hd : (fun x => ∑ b ∈ insert a s, (∏ c ∈ (insert a s).erase b, f c x) * F b x) =
        fun x => F a x * (∏ b ∈ s, f b x) + f a x * (∑ b ∈ s, (∏ c ∈ s.erase b, f c x) * F b x) := by
      funext x
      exact finite_product_derivative_insert s a ha (fun b => f b x) (fun b => F b x)
    rwa [he, hd]

end KLS
end
