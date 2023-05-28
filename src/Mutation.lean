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

Step 1. We define a map `SeedMutation.monomial_to_away` that is a monoid hom 
from `Module.Dual ℤ N` to `S`, where `S` is a localization of the group algebra of 
`Module.Dual ℤ N` away from a non-zero element in the group algebra of `Module.Dual ℤ N`.
Step 2. We show that the map defined in Step 1 induces a isomorphism on `S`.
Step 3. We show that the map defined in Step 2 induces a isomorphism on `K` by using the following
general fact on localizations: a composition of localizations are equivalent to a single localization 
when submonoids under these localizations satisfies appropriate inclusion conditions. 

## Main definitions

* `SeedMutation (s s' : Multiset N)` is a structure expressing that `μ : seed_mutatoin s s'`
  is a seed mutation with a source seed `s` and a target seed `s'`.
* `SeedMutation.field_equiv μ K` is a field isomorphism `K ≃+* K` associated with 
  a seed mutation `μ`.

## Main statements

* `mutation_field_equiv_map_monomial` gives a fomula for a mutation on the monomials.
-/

noncomputable section

-- variable {R : Type _} {M : Type _} [Ring R] [AddCommMonoid M] [Module R M]

open Classical BilinForm

class SkewSymmForm (N : Type _) [AddCommGroup N] :=
(form : BilinForm ℤ N)
(alt : BilinForm.IsAlt form)

variable {N : Type _} [AddCommGroup N] [SkewSymmForm N] 

section SeedMutation

-- variable (v : N) (ε : ℤ)

open SkewSymmForm

abbrev B := @BilinForm.toLin ℤ N _ _ _ form

-- def plMutation (v : N) (ε : ℤ) : N → N :=
-- fun n => n + (max 0 (ε * (B n v))) • v

-- def plMutation.equiv : N ≃ N where
--   toFun := plMutation v ε
--   invFun := plMutation (-v) (-ε)
--   left_inv := fun n => by simp [plMutation, IsAlt.self_eq_zero alt]
--   right_inv := fun n => by simp [plMutation, IsAlt.self_eq_zero alt]

-- lemma pl_mutation.bijective : Function.Bijective (plMutation v ε) :=
-- (plMutation.equiv v ε).bijective

-- @[simp] lemma pl_mutation_neg_left_id : plMutation (-v) (-ε) ∘ plMutation v ε = id :=
-- by ext x; apply (plMutation.equiv v ε).left_inv x

-- @[simp] lemma pl_mutation_neg_left_apply : plMutation (-v) (-ε) (plMutation v ε x) = x :=
-- by apply (plMutation.equiv v ε).left_inv x

-- @[simp] lemma pl_mutation_neg_righ_id : plMutation v ε ∘ plMutation (-v) (-ε) = id :=
-- by ext x; apply (plMutation.equiv v ε).right_inv x

-- structure SeedMutation (s s' : Multiset N) where
-- -- (sign : ℤ)
--   sign : ℤˣ
--   -- sign_ne_zero : NeZero sign
--   src_vect : N
--   tar_vect : N
--   src_in : src_vect ∈ s
--   tar_in : tar_vect ∈ s'
--   seed_tar_src : s'.erase tar_vect = Multiset.map (plMutation src_vect sign) (s.erase src_vect)
--   vect_tar_src : tar_vect = - src_vect

-- -- lemma SeedMutation.neg_sign_ne_zero (s s' : Multiset N) (μ : SeedMutation s s') : NeZero (-μ.sign) := by
-- --   letI h := μ.sign_ne_zero
-- --   cases μ.sign
-- --   · cases μ.sign
-- --     simp at h
-- --   apply SignType.pos_or_neg_of_ne_zero

-- end SeedMutation

-- section direction
-- variable {s s' : Multiset N} (μ : SeedMutation s s') (v : N)

-- def IsMutationDirection : Prop := ∃ k : ℤ, v = k • μ.src_vect

-- def SeedMutation.Direction := ℤ ∙ μ.src_vect 

-- lemma SeedMutation.direction_def (h : v ∈ ℤ ∙ μ.src_vect) : ∃ k : ℤ, k • μ.src_vect = v :=
--   Submodule.mem_span_singleton.1 h


-- lemma isMutationDirection_def 
--     (h : IsMutationDirection μ v) : ∃ k : ℤ, v = k • μ.src_vect := 
--   h

-- lemma src_vect_is_mutation_direction :
--     IsMutationDirection μ μ.src_vect := 
--   ⟨1, by simp only [one_smul]⟩

-- lemma tar_vect_is_mutation_direction :
-- IsMutationDirection μ μ.tar_vect := 
--   ⟨-1, by simpa using μ.vect_tar_src⟩

-- lemma SeedMutation.tar_vect_eq_neg_src_vect 
--     {s s' : Multiset N} (μ : SeedMutation s s') : μ.tar_vect = - μ.src_vect := 
--   μ.vect_tar_src

-- lemma SeedMutation.src_vect_eq_neg_tar_vect {s s' : Multiset N} (μ : SeedMutation s s') :  
-- μ.src_vect = - μ.tar_vect :=
--   calc μ.src_vect = - - μ.src_vect := by rw [neg_neg]
--         _         =   - μ.tar_vect := by rw [μ.vect_tar_src]

-- instance sign_tar_vect_IsMutationDirection : IsMutationDirection μ ((μ.sign : ℤ) • μ.tar_vect) := by
--   cases' Int.units_eq_one_or μ.sign with h h
--   simp at h
--   · simpa [h] using (tar_vect_is_mutation_direction μ)
--   · -- simp does not works
--     rw [μ.tar_vect_eq_neg_src_vect] 
--     simpa [h] using (src_vect_is_mutation_direction μ)

-- instance sign_src_vect_is_mutation_direction : IsMutationDirection μ ((μ.sign : ℤ) • μ.src_vect) := by
--   cases' Int.units_eq_one_or μ.sign with h h
--   · simpa [h] using (src_vect_is_mutation_direction μ)
--   · simpa [h, ←μ.tar_vect_eq_neg_src_vect] using (tar_vect_is_mutation_direction μ)

-- end direction

-- section SeedMutation

-- open SkewSymmForm

-- namespace SeedMutation

-- @[simp] 
-- lemma form_mutation_direction_eq_zero {s s' : Multiset N} (μ : SeedMutation s s')
--     (v w : N) (hv: IsMutationDirection μ v) (hw : IsMutationDirection μ w) : form v w = 0 := by
--   cases' hv with k hk
--   cases' hw with l hl
--   rw [hk, hl]
--   simp [IsAlt.self_eq_zero alt]

-- @[simp] 
-- lemma form_mutation_direction_eq_zero' {s s' : Multiset N} (μ : SeedMutation s s')
--     (v w : N) (hv: IsMutationDirection μ v) (hw : IsMutationDirection μ w) : B v w = 0 :=
--   form_mutation_direction_eq_zero μ v w hv hw

-- end SeedMutation

-- lemma pl_mutation_eq (v : N) {w : N} (ε : ℤ) (c : ℤ) (h : w = c • v) : plMutation v ε w = w := by
--   simp [h, plMutation, IsAlt.self_eq_zero alt]

-- @[simp] lemma pl_mutation_eq' (v : N) (ε : ℤ) : plMutation v ε v = v :=
-- pl_mutation_eq v ε 1 (one_smul _ _).symm


-- def SeedMutation.symm {s s' : Multiset N} (μ : SeedMutation s s') : SeedMutation s' s :=
-- { sign := - μ.sign,
--   -- is_sign := @is_sign.rec_on _ (is_sign (- μ.sign)) μ.is_sign 
--   --   (fun h => h.symm ▸ neg_one.is_sign) (fun h => h.symm ▸ one.is_sign),
--   -- sign_ne_zero := NeZero.symm μ.sign_ne_zero,
--   src_vect := μ.tar_vect,
--   tar_vect := μ.src_vect,
--   src_in := μ.tar_in,
--   tar_in := μ.src_in,
--   seed_tar_src := by
--     let h := μ.seed_tar_src
--     rw [Multiset.map_erase] at h
--     rw [h, Multiset.map_erase]
--     simp only [Function.comp_apply, Multiset.map_congr, Multiset.map_map]
--     rw [pl_mutation_eq μ.src_vect μ.sign 1]
--     dsimp only [Units.val_neg]
--     rw[ pl_mutation_eq μ.tar_vect (-μ.sign) (-1),
--       μ.tar_vect_eq_neg_src_vect]
--     simp only [id.def, Multiset.map_id', eq_self_iff_true, Multiset.map_congr, pl_mutation_neg_left_id]
--     change Multiset.erase s μ.src_vect =
--       Multiset.erase (Multiset.map ((plMutation (-μ.src_vect) (-↑μ.sign)) ∘ (plMutation μ.src_vect (↑μ.sign))) s)
--         μ.src_vect
--     rw [pl_mutation_neg_left_id]
--     congr 1
--     apply Eq.symm
--     apply Multiset.map_id
    
--     -- any_goals {simp only [one_smul, neg_smul]}
--     · simpa using μ.src_vect_eq_neg_tar_vect
--     · simp
--     · exact Function.Bijective.injective (pl_mutation.bijective μ.tar_vect (-μ.sign))
--     · exact Function.Bijective.injective (pl_mutation.bijective μ.src_vect μ.sign)
--   vect_tar_src := μ.src_vect_eq_neg_tar_vect }

end SeedMutation

section function_of_vector

abbrev R (N : Type _) [AddCommGroup N] := AddMonoidAlgebra ℤ (Module.Dual ℤ N)

-- local notation "R" => AddMonoidAlgebra ℤ (Module.Dual ℤ N)

-- local attribute [reducible, inline] AddMonoidAlgebra ring_of_function

noncomputable instance : CommSemiring (R N) := 
  inferInstanceAs <| CommSemiring <| AddMonoidAlgebra ℤ (Module.Dual ℤ N)

noncomputable instance : CommRing (Module.Dual ℤ N →₀ ℤ) := 
  inferInstanceAs <| CommRing <| AddMonoidAlgebra _ _

open AddMonoidAlgebra

noncomputable
def function_of_vector (v : N) : (R N) :=
AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single (B v) 1

-- scoped[Polynomial] 
-- notation c:60 "• z ^ "v:60 => single v c
-- notation "z ^ "v:60 => single v 1

private abbrev z  (m : Module.Dual ℤ N) : R N := AddMonoidAlgebra.single m 1

private lemma z_def  (m : Module.Dual ℤ N) : z m = AddMonoidAlgebra.single m 1 := rfl

private def f (v : N) := 1 + z (B v)

def function_of_vector' (n : N) : (R N) := f n

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

-- lemma function_of_vector_ne_zero' (v : N) : f v ≠ (0 : R N) := by
--   cases' eq_or_ne (B v) 0 with H H
--   · rw [H]
--     rw [one_def]
--     rw [Finsupp.nonzero_iff_exists, ←AddMonoidAlgebra.single_add]
--     exact ⟨0, by simp⟩
--   · rw [one_def, Finsupp.nonzero_iff_exists]
--     use 0
--     have : (0 : Module.Dual ℤ N) ∉ (AddMonoidAlgebra.single (B v) 1 : R N).support := by
--       rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]
--       exact H.symm
--     rw [Finsupp.not_mem_support_iff] at this
--     rw [Finsupp.add_apply, this]
--     simp

end function_of_vector

namespace Mutation

section mutation_away

variable (S : Type _) [CommRing S] [IsDomain S] [Algebra (R N) S]

local instance : Algebra (AddMonoidAlgebra ℤ (Module.Dual ℤ N)) S := by assumption
local instance : Algebra (R N) S := by assumption

variable (ε : ℤˣ) (v : N)

open AddMonoidAlgebra

local instance : Algebra (AddMonoidAlgebra ℤ ((Module.Dual ℤ N))) S := by assumption
local instance : Algebra (R N) S := by assumption

variable [IsLocalization.Away (f v) S]

def awayUnit : Units S where
  val := algebraMap (R N) S (f v)
  inv := IsLocalization.mk' S 1 ⟨f v, Submonoid.mem_powers (f v)⟩
  val_inv := by rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self]
  inv_val := by rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self]

def monomial_to_away : Multiplicative (Module.Dual ℤ N) →* S :=
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

def to_away : R N →+* S :=
  AddMonoidAlgebra.liftNCRingHom (Int.castRingHom S)
(monomial_to_away S ε v) (fun _ _ => (Commute.all _ _))

@[simp]
lemma to_away_of_function_of_mutation_direction' (v v' : N) (hv : ∃ k : ℤ, v' = k • v) [IsLocalization.Away (f v) S] :
(to_away S ε v) (f v') = 
  IsLocalization.mk' S (f v')
      (1 : Submonoid.powers (f v)) := by
  rcases hv with ⟨k, hk⟩
  simp [one_def, z_def, to_away, liftNCRingHom, monomial_to_away, IsLocalization.mk'_one, 
    hk, liftNC_single, IsAlt.self_eq_zero SkewSymmForm.alt, f]

@[simp]
lemma to_away_of_function_of_self :
    (to_away S ε v) (f v) = 
      IsLocalization.mk' S (f v)
          (1 : Submonoid.powers (f v)) :=
  to_away_of_function_of_mutation_direction' S ε v v ⟨1, (one_smul ℤ v).symm⟩

-- @[simp]
-- lemma to_away_of_function_of_neg :
--     (to_away S ε v) (1 + z (B (-v))) = 
--       IsLocalization.mk' S (1 + z (B (-v)))
--           (1 : Submonoid.powers (f v)) :=
--   to_away_of_function_of_mutation_direction' S ε v (-v) ⟨-1, by simp⟩
    

lemma is_unit_to_away : 
    IsUnit (to_away S ε v (f v)) := by
  rw [to_away_of_function_of_mutation_direction' S ε v v ⟨1, by simp⟩, IsLocalization.mk'_one]
  exact IsLocalization.map_units S ⟨f v, Submonoid.mem_powers _⟩

def ring_hom_away : S →+* S :=
IsLocalization.Away.lift (f v) (is_unit_to_away S ε v)


@[simp] lemma mutation_away_map_const  : 
    ((ring_hom_away S ε v) ∘ (algebraMap (R N) S)) ∘
      AddMonoidAlgebra.singleZeroRingHom =
        (algebraMap (R N) S ) ∘ AddMonoidAlgebra.singleZeroRingHom := by
  simp only [←RingHom.coe_comp, FunLike.coe_fn_eq, eq_iff_true_of_subsingleton]

@[simp] lemma mutation_away_map_const''  (b : ℤ) : 
    ring_hom_away S ε v ((algebraMap (R N) S) (AddMonoidAlgebra.single 0 b)) =
algebraMap (R N) S (AddMonoidAlgebra.single 0 b) := by
  have h : AddMonoidAlgebra.single (0 : Module.Dual ℤ N) b = AddMonoidAlgebra.singleZeroRingHom b := by rfl
  rw [h]
  simp_rw [←RingHom.comp_apply]
  simp_rw [←RingHom.coe_comp]
  apply congrFun <| mutation_away_map_const _ _ _

@[simp] 
lemma mutation_away_map_monomial (v : N) [IsLocalization.Away (f v) S] (a : Multiplicative (Module.Dual ℤ N)) : 
    ring_hom_away S ε v ((algebraMap (R N) S) (AddMonoidAlgebra.single a 1)) =
      algebraMap (R N) S (AddMonoidAlgebra.single a 1) * ↑(awayUnit S v ^ (ε • (- a v))) := by
  dsimp only [ring_hom_away, IsLocalization.Away.lift]
  rw [IsLocalization.lift_eq]
  dsimp [to_away]
  dsimp [AddMonoidAlgebra.liftNCRingHom]
  -- dsimp
  -- rw [AddMonoidAlgebra.liftNCRingHom]
  dsimp [monomial_to_away]
  simp only [smul_neg, zpow_neg, AddMonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, map_one, toAdd_ofAdd,
    one_mul]
  congr
  rw [IsLocalization.mk'_one]

@[simp]
lemma mutation_away_eq_self_of_gpow_of_unit (k : ℤ) : 
    ring_hom_away S ε v (awayUnit S v ^ k) = awayUnit S v ^ k := by
  dsimp [ring_hom_away, IsLocalization.Away.lift, awayUnit]
  rcases k with (k | k)
  · simp only [Int.ofNat_eq_coe, zpow_coe_nat, Units.val_pow_eq_pow_val, map_pow]
    rw [IsLocalization.lift_eq]
    apply congr_arg (fun x : S => x ^ k)
    rw [to_away_of_function_of_self]
    rw [IsLocalization.mk'_one]
  · simp only [zpow_negSucc]
    rw [←inv_pow]
    simp only [Units.inv_mk, Units.val_pow_eq_pow_val, map_pow]
    apply congr_arg (fun x : S => x ^ (k + 1))
    rw [IsLocalization.lift_mk'_spec]
    simp only [map_one, to_away_of_function_of_self]
    rw [←IsLocalization.mk'_mul]
    rw [one_mul, mul_one, IsLocalization.mk'_self]

-- @[simp]
-- lemma mutation_away_eq_neg_of_gpow_of_unit (v : N) [IsLocalization.Away (f v) S] (k : ℤ) : 
--     SeedMutation.ring_hom_away' S ε v ↑((SeedMutation.awayUnit S (-v)) ^ k) = ↑((SeedMutation.awayUnit S (-v)) ^ k) := by
--   dsimp [SeedMutation.ring_hom_away', IsLocalization.Away.lift, SeedMutation.awayUnit]
--   rcases k with (k | k)
--   · simp only [Int.ofNat_eq_coe, zpow_coe_nat, Units.val_pow_eq_pow_val, map_pow]
--     rw [IsLocalization.lift_eq]
--     apply congr_arg (fun x : S => x ^ k)
--     rw [to_away_of_function_of_neg]
--     rw [IsLocalization.mk'_one]
--   · simp only [zpow_negSucc]
--     rw [←inv_pow]
--     simp only [Units.inv_mk, Units.val_pow_eq_pow_val, map_pow]
--     apply congr_arg (fun x : S => x ^ (k + 1))
--     simp?
--     rw [IsLocalization.lift_mk'_spec]
--     simp only [map_one, to_away_of_function_of_self]
--     rw [←IsLocalization.mk'_mul]
--     rw [one_mul, mul_one, IsLocalization.mk'_self]

lemma ring_equiv_away_hom_inv_aux (ε ε' : ℤˣ) (hε : ε' = - ε) (v : N) [IsLocalization.Away (f v) S] : 
  ((ring_hom_away S ε' v).comp (ring_hom_away S ε v)).comp (algebraMap (R N) S) = algebraMap (R N) S := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro a
    · simp 
    · 
      -- replace hε : ε' = - ε := by simpa [←eq_inv_mul_iff_mul_eq] using hε
      suffices algebraMap (R N) S (z a) * ↑(awayUnit S v ^ (ε • a v)) * 
        (ring_hom_away S (-ε) v) (awayUnit S v ^ (-(ε • a v))) =
          algebraMap (R N) S (z a) by simpa [hε] using this
      rw [mutation_away_eq_self_of_gpow_of_unit S (-ε) (v)]
      simp 

lemma IsLocalization.lift_id' {R : Type _} [CommSemiring R] (M : Submonoid R) (S : Type _) [CommSemiring S] [Algebra R S] [IsLocalization M S] :
    IsLocalization.lift (IsLocalization.map_units S : ∀ y : M, IsUnit (algebraMap R S y)) = RingHom.id S := by
  ext
  apply IsLocalization.lift_id

def ring_equiv_away (v : N) [IsLocalization.Away (f v) S] : S ≃+* S :=
  RingEquiv.ofHomInv (ring_hom_away S ε v) (ring_hom_away S (-ε) v)
    (by
      rw [←IsLocalization.lift_id' (Submonoid.powers (f v)), IsLocalization.lift_unique]
      rw [←Function.funext_iff]
      apply congr_arg FunLike.coe (ring_equiv_away_hom_inv_aux S ε (-ε) (by simp) v))
    (by
      rw [←IsLocalization.lift_id' (Submonoid.powers (f v)), IsLocalization.lift_unique]
      rw [←Function.funext_iff]
      apply congr_arg FunLike.coe (ring_equiv_away_hom_inv_aux S (-ε) ε (by simp) v))

end mutation_away

section mutation_frac

variable [IsDomain (R N)] (K : Type _) [Field K] [Algebra (R N) K] [IsFractionRing (R N) K] (ε : ℤˣ)

-- local attribute [instance] ring_of_function.integral_domain 

-- abbreviation SeedMutation.Away := localization.Away (function_of_vector (μ.sign • μ.src_vect))

private abbrev z  (m : Module.Dual ℤ N) : R N := AddMonoidAlgebra.single m 1

private lemma z_def  (m : Module.Dual ℤ N) : z m = AddMonoidAlgebra.single m 1 := rfl

set_option synthInstance.maxHeartbeats 1000000 in
instance (v : N) : Algebra (R N) (Localization.Away (f v)) := by infer_instance

set_option maxHeartbeats 1000000 in
instance domain (v : N) : IsDomain (Localization.Away (f v)) := 
IsLocalization.isDomain_of_le_nonZeroDivisors (R N)
  (powers_le_nonZeroDivisors_of_noZeroDivisors ((function_of_vector_ne_zero v)))

-- local attribute [instance]  away.integral_domain

variable (v : N) 
-- [IsLocalization.Away (f v) K]

instance : Algebra (Localization.Away (f v)) K := by
  apply RingHom.toAlgebra
  apply @IsLocalization.lift (R N) _ (Submonoid.powers (f v)) _ _ _ _ _ _ (algebraMap (R N) K)
  intro a
  have ha := powers_le_nonZeroDivisors_of_noZeroDivisors (function_of_vector_ne_zero v) a.2
  apply IsLocalization.map_units _ (⟨a.1, ha⟩ : nonZeroDivisors (R N))


set_option maxHeartbeats 2000000 in
instance : IsScalarTower (R N) (Localization.Away (f v)) K := 
IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away (f v)) K (Submonoid.powers (f v)) (nonZeroDivisors (R N)) (powers_le_nonZeroDivisors_of_noZeroDivisors (function_of_vector_ne_zero v))

-- local attribute[instance] SeedMutation.algebra_of_away_frac

-- def SeedMutation.is_fraction_of_algebra_of_away_frac : 
-- @is_fraction_ring μ.Away _ K _ (μ.algebra_of_away_frac K) :=
-- IsLocalization.is_fraction_of_algebra_of_away_frac _ μ.Away K



set_option maxHeartbeats 2000000 in
instance fraction : IsFractionRing (Localization.Away (f v)) K := by
  apply IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (f v))  (Localization.Away (f v)) K
  -- let M := IsLocalization.localizationLocalizationSubmodule (Submonoid.powers (f v)) (nonZeroDivisors (Localization.Away (f v)))
  -- have h := IsLocalization.localization_localization_isLocalization (Submonoid.powers (f v)) (nonZeroDivisors (Localization.Away (f v)))

-- local attribute[instance] SeedMutation.is_fraction_of_algebra_of_away_frac

def SeedMutation.field_equiv (ε : ℤˣ) (v : N) : K ≃+* K := 
IsFractionRing.fieldEquivOfRingEquiv (ring_equiv_away (Localization.Away (f v)) ε v)



-- section

-- private def z' 
-- {K : Type _} [Field K] [Algebra (R N) K] [IsFractionRing (R N) K] 
-- (m : Module.Dual ℤ N) := algebraMap (R N) K (AddMonoidAlgebra.single m 1)

-- lemma mutation_field_equiv_map_monomial (m : Module.Dual ℤ N) : 
-- μ.field_equiv K (z m)  = 
-- z m * (1 + z (B (μ.sign • μ.src_vect))) ^ - m μ.src_vect := by
--   dsimp only [z SeedMutation.field_equiv, is_fraction_ring.field_equiv_of_ring_equiv, ring_equiv_away]
--   let h_ne := function_of_vector_ne_zero (μ.sign • μ.src_vect),
--   repeat {rw [IsLocalization.eq_comp_map_of_lift_of_of_away_frac h_ne μ.Away K] }
--   simp only [fpow_neg, linear_map.map_smul, IsLocalization.ring_equiv_of_ring_equiv_eq, 
--     mutation_away_map_monomial, algebra.id.smul_eq_mul, one_mul, gpow_neg, mul_eq_mul_left_iff, inv_inj', 
--     mul_neg_eq_neg_mul_symm, ring_hom.map_units_inv, ring_equiv.of_hom_inv_apply, ring_hom.map_mul]
--   apply or.inl
--   unfold SeedMutation.awayUnit function_of_vector
--   induction m μ.src_vect
--   simp only [ring_hom.map_add, units.coe_mk, gpow_neg_succ_of_nat, inv_inj', ring_hom.map_pow,
--       ring_hom.map_units_inv, linear_map.map_smul, units.coe_pow, int.of_nat_eq_coe, gpow_coe_nat]
--   rw <- AddMonoidAlgebra.one_def
--   simp only [ring_hom.map_one]

-- end

end mutation_frac

end Mutation

end