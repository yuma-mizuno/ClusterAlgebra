import Mathlib.LinearAlgebra.Dual
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.Basic
import Mathlib.Data.Sign
/-!
# Mutations

This file defines mutations as isomorphisms between ambient fields.

A seed mutation is a combinatorial operation on a ℤ-module `N` given by a piecewise-linear
transformation on `N`. A mutation is a field isomorphism associated with a seed mutation.
It is an isomorphism on the `K` that is a field of fractions of the group algebra 
of the dual module of `N`. We define mutations by the following three steps.

Step 1. We define a map `SeedMutation.monomialToAway` that is a monoid hom 
from `Module.Dual ℤ N` to `S`, where `S` is a localization of the group algebra of 
`Module.Dual ℤ N` away from a non-zero element in the group algebra of `Module.Dual ℤ N`.
Step 2. We show that the map defined in Step 1 induces a isomorphism on `S`.
Step 3. We show that the map defined in Step 2 induces a isomorphism on `K` by using the following
general fact on localizations: a composition of localizations are equivalent to a single localization 
when submonoids under these localizations satisfies appropriate inclusion conditions. 

## Main definitions

* `SeedMutation (s s' : Multiset N)` is a structure expressing that `μ : seed_mutatoin s s'`
  is a seed mutation with a source seed `s` and a target seed `s'`.
* `SeedMutation.fieldEquiv μ K` is a field isomorphism `K ≃+* K` associated with 
  a seed mutation `μ`.

## Main statements

* `mutation_fieldEquiv_map_monomial` gives a fomula for a mutation on the monomials.
-/

noncomputable 
section

open Classical BilinForm

class SkewSymmForm (N : Type _) [AddCommGroup N] :=
(form : BilinForm ℤ N)
(alt : BilinForm.IsAlt form)

variable {N : Type _} [AddCommGroup N] [SkewSymmForm N] 

section SeedMutation

open SkewSymmForm

abbrev B := @BilinForm.toLin ℤ N _ _ _ form

end SeedMutation

section

abbrev R (N : Type _) [AddCommGroup N] := AddMonoidAlgebra ℤ (Module.Dual ℤ N)

instance : CommSemiring (R N) := 
  inferInstanceAs <| CommSemiring <| AddMonoidAlgebra ℤ (Module.Dual ℤ N)

instance : CommRing (Module.Dual ℤ N →₀ ℤ) := 
  inferInstanceAs <| CommRing <| AddMonoidAlgebra _ _

open AddMonoidAlgebra

private abbrev z  (m : Module.Dual ℤ N) : R N := AddMonoidAlgebra.single m 1

private lemma z_def  (m : Module.Dual ℤ N) : z m = AddMonoidAlgebra.single m 1 := rfl

private abbrev f (v : N) := 1 + z (B v)

lemma function_of_vector_ne_zero (v : N) : f v ≠ (0 : R N) := by
  dsimp only [AddMonoidAlgebra.one_def, f]
  cases' eq_or_ne (B v) 0 with H H
  · rw [H, Finsupp.nonzero_iff_exists, ←AddMonoidAlgebra.single_add]
    exact ⟨0, by simp⟩
  · rw [Finsupp.nonzero_iff_exists]
    use 0
    have : (0 : Module.Dual ℤ N) ∉ (AddMonoidAlgebra.single (B v) 1 : R N).support := by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]
      exact H.symm
    rw [Finsupp.not_mem_support_iff] at this
    rw [Finsupp.add_apply, this]
    simp

end

namespace Mutation

section mutation_away

variable (S : Type _) [CommRing S] [IsDomain S] [Algebra (R N) S]

local instance : Algebra (AddMonoidAlgebra ℤ (Module.Dual ℤ N)) S := by assumption
local instance : Algebra (R N) S := by assumption

variable (ε : ℤˣ) (v : N)

open AddMonoidAlgebra

variable [IsLocalization.Away (f v) S]

def awayUnit : Units S where
  val := algebraMap (R N) S (f v)
  inv := IsLocalization.mk' S 1 ⟨f v, Submonoid.mem_powers (f v)⟩
  val_inv := by rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self]
  inv_val := by rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self]

def monomialToAway : Multiplicative (Module.Dual ℤ N) →* S :=
{ toFun := fun m => 
    IsLocalization.mk' S
    (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1 : R N) (1 : Submonoid.powers (f v))
        * ↑((awayUnit S v)^(ε • (-(Multiplicative.toAdd m) v))),
  map_one' := by
    suffices IsLocalization.mk' S (AddMonoidAlgebra.single 0 1) (1 : Submonoid.powers (f v)) = 1 by simpa
    rw [IsLocalization.mk'_one]
    apply map_one
  map_mul' := fun x y => by
    simp only [Algebra.id.smul_eq_mul, zpow_neg, Int.mul_neg_eq_neg_mul_symm,
      neg_add_rev, LinearMap.add_apply, toAdd_mul,
      smul_add, smul_neg, zpow_neg]
    rw [<- one_mul (1 : ℤ), ←AddMonoidAlgebra.single_mul_single]
    rw [<- one_mul (1 : Submonoid.powers (f v)),
      IsLocalization.mk'_mul]
    rw [mul_one]
    simp only [mul_one, zpow_add, zpow_neg, zpow_sub, Int.mul_neg_eq_neg_mul_symm, Units.val_mul]
    ring  }

def toAway : R N →+* S :=
  AddMonoidAlgebra.liftNCRingHom (Int.castRingHom S)
(monomialToAway S ε v) (fun _ _ => (Commute.all _ _))

@[simp]
lemma toAway_of_function_of_mutation_direction (v v' : N) (hv : ∃ k : ℤ, v' = k • v) [IsLocalization.Away (f v) S] :
(toAway S ε v) (f v') = 
  IsLocalization.mk' S (f v')
      (1 : Submonoid.powers (f v)) := by
  rcases hv with ⟨k, hk⟩
  simp [one_def, z_def, toAway, liftNCRingHom, monomialToAway, IsLocalization.mk'_one, 
    hk, liftNC_single, IsAlt.self_eq_zero SkewSymmForm.alt, f]

@[simp]
lemma toAway_of_function_of_self :
    (toAway S ε v) (f v) = 
      IsLocalization.mk' S (f v)
          (1 : Submonoid.powers (f v)) :=
  toAway_of_function_of_mutation_direction S ε v v ⟨1, (one_smul ℤ v).symm⟩

lemma isUnit_toAway : 
    IsUnit (toAway S ε v (f v)) := by
  rw [toAway_of_function_of_mutation_direction S ε v v ⟨1, by simp⟩, IsLocalization.mk'_one]
  exact IsLocalization.map_units S ⟨f v, Submonoid.mem_powers _⟩

def ringHomAway : S →+* S :=
IsLocalization.Away.lift (f v) (isUnit_toAway S ε v)

@[simp] lemma mutation_away_map_const  : 
    ((ringHomAway S ε v) ∘ (algebraMap (R N) S)) ∘
      AddMonoidAlgebra.singleZeroRingHom =
        (algebraMap (R N) S ) ∘ AddMonoidAlgebra.singleZeroRingHom := by
  simp only [←RingHom.coe_comp, FunLike.coe_fn_eq, eq_iff_true_of_subsingleton]

@[simp] lemma mutation_away_map_const'  (b : ℤ) : 
    ringHomAway S ε v ((algebraMap (R N) S) (AddMonoidAlgebra.single 0 b)) =
algebraMap (R N) S (AddMonoidAlgebra.single 0 b) := by
  have h : AddMonoidAlgebra.single (0 : Module.Dual ℤ N) b = AddMonoidAlgebra.singleZeroRingHom b := by rfl
  rw [h]
  simp_rw [←RingHom.comp_apply]
  simp_rw [←RingHom.coe_comp]
  apply congrFun <| mutation_away_map_const _ _ _

@[simp] 
lemma mutation_away_map_monomial (v : N) [IsLocalization.Away (f v) S] (a : Multiplicative (Module.Dual ℤ N)) : 
    ringHomAway S ε v ((algebraMap (R N) S) (AddMonoidAlgebra.single a 1)) =
      algebraMap (R N) S (AddMonoidAlgebra.single a 1) * ↑(awayUnit S v ^ (ε • (- a v))) := by
  dsimp only [ringHomAway, IsLocalization.Away.lift]
  rw [IsLocalization.lift_eq]
  dsimp [toAway]
  dsimp [AddMonoidAlgebra.liftNCRingHom]
  dsimp [monomialToAway]
  simp only [smul_neg, zpow_neg, AddMonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, map_one, toAdd_ofAdd,
    one_mul]
  congr
  rw [IsLocalization.mk'_one]

@[simp]
lemma mutation_away_eq_self_of_gpow_of_unit (k : ℤ) : 
    ringHomAway S ε v (awayUnit S v ^ k) = awayUnit S v ^ k := by
  dsimp [ringHomAway, IsLocalization.Away.lift, awayUnit]
  rcases k with (k | k)
  · simp only [Int.ofNat_eq_coe, zpow_coe_nat, Units.val_pow_eq_pow_val, map_pow]
    rw [IsLocalization.lift_eq]
    apply congr_arg (fun x : S => x ^ k)
    rw [toAway_of_function_of_self]
    rw [IsLocalization.mk'_one]
  · simp only [zpow_negSucc]
    rw [←inv_pow]
    simp only [Units.inv_mk, Units.val_pow_eq_pow_val, map_pow]
    apply congr_arg (fun x : S => x ^ (k + 1))
    rw [IsLocalization.lift_mk'_spec]
    simp only [map_one, toAway_of_function_of_self]
    rw [←IsLocalization.mk'_mul]
    rw [one_mul, mul_one, IsLocalization.mk'_self]

lemma ringEquivAway_hom_inv_aux (ε ε' : ℤˣ) (hε : ε' = - ε) (v : N) [IsLocalization.Away (f v) S] : 
  ((ringHomAway S ε' v).comp (ringHomAway S ε v)).comp (algebraMap (R N) S) = algebraMap (R N) S := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro a
    · simp
    · suffices algebraMap (R N) S (z a) * ↑(awayUnit S v ^ (ε • a v)) * 
        (ringHomAway S (-ε) v) (awayUnit S v ^ (-(ε • a v))) =
          algebraMap (R N) S (z a) by simpa [hε] using this
      rw [mutation_away_eq_self_of_gpow_of_unit S (-ε) (v)]
      simp 

lemma IsLocalization.lift_id' {R : Type _} [CommSemiring R] (M : Submonoid R) (S : Type _) [CommSemiring S] [Algebra R S] [IsLocalization M S] :
    IsLocalization.lift (IsLocalization.map_units S : ∀ y : M, IsUnit (algebraMap R S y)) = RingHom.id S := by
  ext
  apply IsLocalization.lift_id

def ringEquivAway (v : N) [IsLocalization.Away (f v) S] : S ≃+* S :=
  RingEquiv.ofHomInv (ringHomAway S ε v) (ringHomAway S (-ε) v)
    (by
      rw [←IsLocalization.lift_id' (Submonoid.powers (f v)), IsLocalization.lift_unique]
      rw [←Function.funext_iff]
      apply congr_arg FunLike.coe (ringEquivAway_hom_inv_aux S ε (-ε) (by simp) v))
    (by
      rw [←IsLocalization.lift_id' (Submonoid.powers (f v)), IsLocalization.lift_unique]
      rw [←Function.funext_iff]
      apply congr_arg FunLike.coe (ringEquivAway_hom_inv_aux S (-ε) ε (by simp) v))

end mutation_away

section mutation_frac

variable [IsDomain (R N)] (K : Type _) [Field K] [Algebra (R N) K] [IsFractionRing (R N) K] (ε : ℤˣ)

set_option synthInstance.maxHeartbeats 1000000 in
instance (v : N) : Algebra (R N) (Localization.Away (f v)) := by infer_instance

set_option maxHeartbeats 1000000 in
instance (v : N) : IsDomain (Localization.Away (f v)) := 
  IsLocalization.isDomain_of_le_nonZeroDivisors (R N)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ((function_of_vector_ne_zero v)))

variable (v : N) 

instance : Algebra (Localization.Away (f v)) K := by
  apply RingHom.toAlgebra
  apply @IsLocalization.lift (R N) _ (Submonoid.powers (f v)) _ _ _ _ _ _ (algebraMap (R N) K)
  intro a
  have ha := powers_le_nonZeroDivisors_of_noZeroDivisors (function_of_vector_ne_zero v) a.2
  apply IsLocalization.map_units _ (⟨a.1, ha⟩ : nonZeroDivisors (R N))


set_option maxHeartbeats 2000000 in
instance : IsScalarTower (R N) (Localization.Away (f v)) K := 
  IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away (f v)) K 
    (Submonoid.powers (f v)) (nonZeroDivisors (R N)) (powers_le_nonZeroDivisors_of_noZeroDivisors (function_of_vector_ne_zero v))

set_option maxHeartbeats 2000000 in
instance : IsFractionRing (Localization.Away (f v)) K := 
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (f v))  (Localization.Away (f v)) K

def fieldEquiv (ε : ℤˣ) (v : N) : K ≃+* K := 
  IsFractionRing.fieldEquivOfRingEquiv (ringEquivAway (Localization.Away (f v)) ε v)

section

-- private def z' {K : Type _} [Field K] [Algebra (R N) K] [IsFractionRing (R N) K] (m : Module.Dual ℤ N) : K := 
--   algebraMap (R N) K (AddMonoidAlgebra.single m 1)

-- set_option maxHeartbeats 1000000 in
-- lemma mutation_fieldEquiv_map_monomial (m : Module.Dual ℤ N) : 
--     fieldEquiv K ε v (z' m) = z' m * (1 + z' (B (ε • v))) ^ (- m v) := by
--   dsimp only [z', fieldEquiv, IsFractionRing.fieldEquivOfRingEquiv, ringEquivAway]
--   let h_ne := function_of_vector_ne_zero (ε • v)
--   simp_rw [IsScalarTower.algebraMap_apply (R N) (Localization.Away (f v)) K]
--   simp only [IsLocalization.ringEquivOfRingEquiv_apply, IsLocalization.map_eq, RingHom.coe_coe,
--     RingEquiv.ofHomInv_apply, mutation_away_map_monomial, smul_neg, zpow_neg, map_mul, map_units_inv, mul_eq_mul_left_iff,
--     inv_inj]
--   apply Or.inl
--   dsimp only [awayUnit, z, f]
--   induction m v
--   simp only [f, z, map_add, map_one, Int.ofNat_eq_coe, LinearMap.map_smul_of_tower, zpow_coe_nat]
--   simp? [Units.val_mk, Int.ofNat_eq_coe]


--   rw [<- AddMonoidAlgebra.one_def]
--   simp only [ring_hom.map_one]

end

end mutation_frac

end Mutation

end