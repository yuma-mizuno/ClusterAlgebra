import Mathlib.LinearAlgebra.Dual
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.BilinearForm
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
from `module.dual ℤ N` to `S`, where `S` is a localization of the group algebra of 
`module.dual ℤ N` away from a non-zero element in the group algebra of `module.dual ℤ N`.
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

namespace BilinForm

-- section skew_sym_BilinForm

variable {R : Type _} {M : Type _} [Ring R] [AddCommMonoid M] [Module R M] {B : BilinForm R M}

def isSkewSymm (B : BilinForm R M) : Prop := 
  ∀ (x y : M), B x y = - B y x

variable (H : isSkewSymm B)

lemma skew_symm (x y : M) : B x y = - B y x := H x y

lemma is_refl : IsRefl B := fun x y H1 => (H y x).symm ▸ neg_eq_zero.mpr H1

lemma ortho_comm {x y : M} : IsOrtho B x y ↔ IsOrtho B y x := 
(is_refl H).ortho_comm

lemma is_alt [NoZeroDivisors R] [CharZero R] : IsAlt B := 
fun n => add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (H n n))

@[simp]
lemma self_eq_zero  [NoZeroDivisors R] [CharZero R] (x : M) : B x x = 0 := is_alt H x

-- @[simp]
-- lemma self_eq_zero_to_lin [NoZeroDivisors R] [CharZero R] (x : M) : ⇑(BilinForm.toLin B x) x = 0 := 
-- self_eq_zero H x

-- end skew_sym_BilinForm

end BilinForm

namespace SignType

-- @[elab_as_elim]
lemma pos_or_neg_of_ne_zero (x : SignType) [NeZero x] : x = pos ∨ x = neg := by
  cases x
  · simp [neZero_iff] at *
  · exact Or.inr rfl 
  · exact Or.inl rfl

end SignType

-- inductive IsSign (ε : ℤ) : Prop
--   | pos : ε = 1 → IsSign
--   | neg : ε = -1 → IsSign

-- instance one.is_sign : is_sign 1 := is_sign.pos rfl

-- instance neg_one.is_sign : is_sign (-1) := is_sign.neg rfl

-- instance neg.is_sign (ε : ℤ) [is_sign ε] : is_sign (-ε) :=
-- begin
--   let h : is_sign ε := by apply_instance,
--   refine is_sign.rec_on h (λ H, _) (λ H, _),
--   repeat {any_goals { rw H <|> apply_instance <|> rw neg_neg }},
-- end

open Classical BilinForm

class SkewSymmForm (N : Type _) [AddCommGroup N] :=
(form : BilinForm ℤ N)
(skew : BilinForm.isSkewSymm form)

variable {N : Type _} [AddCommGroup N] [SkewSymmForm N] 

section SeedMutation

variable (s s' : Multiset N) (v : N) (ε : ℤ)

open SkewSymmForm

abbrev B := @BilinForm.toLin ℤ N _ _ _ form

def plMutation (v : N) (ε : ℤ) : N → N :=
fun n => n + (max 0 (ε * (B n v))) • v

def plMutation.equiv : N ≃ N where
  toFun := plMutation v ε
  invFun := plMutation (-v) (-ε)
  left_inv := fun n => by simp [plMutation, self_eq_zero skew]
  right_inv := fun n => by simp [plMutation, self_eq_zero skew]

lemma pl_mutation.bijective : Function.Bijective (plMutation v ε) :=
(plMutation.equiv v ε).bijective

@[simp] lemma pl_mutation_neg_left_id : plMutation (-v) (-ε) ∘ plMutation v ε = id :=
by ext x; apply (plMutation.equiv v ε).left_inv x

@[simp] lemma pl_mutation_neg_left_apply : plMutation (-v) (-ε) (plMutation v ε x) = x :=
by apply (plMutation.equiv v ε).left_inv x

@[simp] lemma pl_mutation_neg_righ_id : plMutation v ε ∘ plMutation (-v) (-ε) = id :=
by ext x; apply (plMutation.equiv v ε).right_inv x

structure SeedMutation (s s' : Multiset N) where
-- (sign : ℤ)
  sign : ℤˣ
  -- sign_ne_zero : NeZero sign
  src_vect : N
  tar_vect : N
  src_in : src_vect ∈ s
  tar_in : tar_vect ∈ s'
  seed_tar_src : s'.erase tar_vect = Multiset.map (plMutation src_vect sign) (s.erase src_vect)
  vect_tar_src : tar_vect = - src_vect

-- lemma SeedMutation.neg_sign_ne_zero (s s' : Multiset N) (μ : SeedMutation s s') : NeZero (-μ.sign) := by
--   letI h := μ.sign_ne_zero
--   cases μ.sign
--   · cases μ.sign
--     simp at h
--   apply SignType.pos_or_neg_of_ne_zero

end SeedMutation

section direction
variable {s s' : Multiset N} (μ : SeedMutation s s') (v : N)

def IsMutationDirection : Prop := ∃ k : ℤ, v = k • μ.src_vect

lemma isMutationDirection_def 
    (h : IsMutationDirection μ v) : ∃ k : ℤ, v = k • μ.src_vect := 
  h

lemma src_vect_is_mutation_direction :
    IsMutationDirection μ μ.src_vect := 
  ⟨1, by simp only [one_smul]⟩

lemma tar_vect_is_mutation_direction :
IsMutationDirection μ μ.tar_vect := 
  ⟨-1, by simpa using μ.vect_tar_src⟩

lemma SeedMutation.tar_vect_eq_neg_src_vect 
    {s s' : Multiset N} (μ : SeedMutation s s') : μ.tar_vect = - μ.src_vect := 
  μ.vect_tar_src

lemma SeedMutation.src_vect_eq_neg_tar_vect {s s' : Multiset N} (μ : SeedMutation s s') :  
μ.src_vect = - μ.tar_vect :=
  calc μ.src_vect = - - μ.src_vect := by rw [neg_neg]
        _         =   - μ.tar_vect := by rw [μ.vect_tar_src]

instance sign_tar_vect_IsMutationDirection : IsMutationDirection μ ((μ.sign : ℤ) • μ.tar_vect) := by
  cases' Int.units_eq_one_or μ.sign with h h
  simp at h
  · simpa [h] using (tar_vect_is_mutation_direction μ)
  · -- simp does not works
    rw [μ.tar_vect_eq_neg_src_vect] 
    simpa [h] using (src_vect_is_mutation_direction μ)

instance sign_src_vect_is_mutation_direction : IsMutationDirection μ ((μ.sign : ℤ) • μ.src_vect) := by
  cases' Int.units_eq_one_or μ.sign with h h
  · simpa [h] using (src_vect_is_mutation_direction μ)
  · simpa [h, ←μ.tar_vect_eq_neg_src_vect] using (tar_vect_is_mutation_direction μ)

end direction

section SeedMutation

open SkewSymmForm

namespace SeedMutation

@[simp] 
lemma form_mutation_direction_eq_zero {s s' : Multiset N} (μ : SeedMutation s s')
    (v w : N) (hv: IsMutationDirection μ v) (hw : IsMutationDirection μ w) : form v w = 0 := by
  cases' hv with k hk
  cases' hw with l hl
  rw [hk, hl]
  simp [self_eq_zero skew]

@[simp] 
lemma form_mutation_direction_eq_zero' {s s' : Multiset N} (μ : SeedMutation s s')
    (v w : N) (hv: IsMutationDirection μ v) (hw : IsMutationDirection μ w) : B v w = 0 :=
  form_mutation_direction_eq_zero μ v w hv hw

end SeedMutation

lemma pl_mutation_eq (v : N) {w : N} (ε : ℤ) (c : ℤ) (h : w = c • v) : plMutation v ε w = w := by
  simp [h, plMutation, self_eq_zero skew]

@[simp] lemma pl_mutation_eq' (v : N) (ε : ℤ) : plMutation v ε v = v :=
pl_mutation_eq v ε 1 (one_smul _ _).symm


def SeedMutation.symm {s s' : Multiset N} (μ : SeedMutation s s') : SeedMutation s' s :=
{ sign := - μ.sign,
  -- is_sign := @is_sign.rec_on _ (is_sign (- μ.sign)) μ.is_sign 
  --   (fun h => h.symm ▸ neg_one.is_sign) (fun h => h.symm ▸ one.is_sign),
  -- sign_ne_zero := NeZero.symm μ.sign_ne_zero,
  src_vect := μ.tar_vect,
  tar_vect := μ.src_vect,
  src_in := μ.tar_in,
  tar_in := μ.src_in,
  seed_tar_src := by
    let h := μ.seed_tar_src
    rw [Multiset.map_erase] at h
    rw [h, Multiset.map_erase]
    simp only [Function.comp_apply, Multiset.map_congr, Multiset.map_map]
    rw [pl_mutation_eq μ.src_vect μ.sign 1]
    dsimp only [Units.val_neg]
    rw[ pl_mutation_eq μ.tar_vect (-μ.sign) (-1),
      μ.tar_vect_eq_neg_src_vect]
    simp only [id.def, Multiset.map_id', eq_self_iff_true, Multiset.map_congr, pl_mutation_neg_left_id]
    change Multiset.erase s μ.src_vect =
      Multiset.erase (Multiset.map ((plMutation (-μ.src_vect) (-↑μ.sign)) ∘ (plMutation μ.src_vect (↑μ.sign))) s)
        μ.src_vect
    rw [pl_mutation_neg_left_id]
    congr 1
    apply Eq.symm
    apply Multiset.map_id
    
    -- any_goals {simp only [one_smul, neg_smul]}
    · simpa using μ.src_vect_eq_neg_tar_vect
    · simp
    · exact Function.Bijective.injective (pl_mutation.bijective μ.tar_vect (-μ.sign))
    · exact Function.Bijective.injective (pl_mutation.bijective μ.src_vect μ.sign)
  vect_tar_src := μ.src_vect_eq_neg_tar_vect }

end SeedMutation

section function_of_vector

def ring_of_function (N : Type _) [AddCommGroup N]  :=
AddMonoidAlgebra ℕ (Module.Dual ℤ N)

-- local notation "R" => AddMonoidAlgebra ℤ (Module.Dual ℤ N)

-- local attribute [reducible, inline] add_monoid_algebra ring_of_function

noncomputable instance : CommSemiring (ring_of_function N) := 
  inferInstanceAs <| CommSemiring <| AddMonoidAlgebra ℕ (Module.Dual ℤ N)

noncomputable instance : CommRing (Module.Dual ℤ N →₀ ℤ) := 
  inferInstanceAs <| CommRing <| AddMonoidAlgebra _ _

noncomputable

-- open skew_symmetric_form

def function_of_vector (v : N) : (ring_of_function N) :=
AddMonoidAlgebra.single 0 1 + AddMonoidAlgebra.single (B v) 1

lemma function_of_vector_ne_zero (v : N) : function_of_vector v ≠ (0 : ring_of_function N) := by
  dsimp only [function_of_vector]
  cases' eq_or_ne (B v) 0 with H H
  · rw [H, Finsupp.nonzero_iff_exists, ←Finsupp.single_add]
    exact ⟨0, by simp⟩
  · rw [Finsupp.nonzero_iff_exists]
    use 0
    have : (0 : Module.Dual ℤ N) ∉ (Finsupp.single (B v) 1 : ring_of_function N).support := by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]
      exact H.symm
    rw [Finsupp.not_mem_support_iff] at this
    rw [Finsupp.add_apply, this]
    simp

end function_of_vector

section mutation_away

-- local attribute [class] is_integral_domain

#check IsDomain

-- local notation "R" => AddMonoidAlgebra ℤ (Module.Dual ℤ N)

-- variable {N : Type _} [AddCommGroup N] [SkewSymmForm N] 

variable {s s' : Multiset N} (μ : SeedMutation s s') (S : Type _) [CommSemiring S] [IsDomain S]
[Algebra (ring_of_function N) S]
[IsLocalization.Away (function_of_vector (μ.sign • μ.src_vect)) S]

instance : Algebra (AddMonoidAlgebra ℕ (Module.Dual ℤ N)) S := by assumption

-- open skew_symmetric_form

variable (ε : ℤˣ) 

namespace SeedMutation

instance : Algebra (AddMonoidAlgebra ℕ ((Module.Dual ℤ N))) S := by assumption

noncomputable
def away_unit : Units S :=
{ val := algebraMap (ring_of_function N) S (function_of_vector (μ.sign • μ.src_vect)),
  inv := IsLocalization.mk' S 1 ⟨function_of_vector (μ.sign • μ.src_vect), Submonoid.mem_powers _⟩,
  val_inv := by rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self],
  inv_val := by rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self] }

noncomputable
def away_unit' (v : N) [IsLocalization.Away (function_of_vector v) S] : Units S :=
{ val := algebraMap (ring_of_function N) S (function_of_vector v),
  inv := IsLocalization.mk' S 1 ⟨function_of_vector v, Submonoid.mem_powers (function_of_vector v)⟩,
  val_inv := by rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self],
  inv_val := by rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self] }

def monomial_to_away' (v : N) [IsLocalization.Away (function_of_vector v) S] : Multiplicative (Module.Dual ℤ N) →* S :=
{ toFun := fun m => 
    IsLocalization.mk' S
    (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1 : AddMonoidAlgebra ℕ (Module.Dual ℤ N)) (1 : Submonoid.powers (function_of_vector v))
        * ↑((away_unit' S v)^(ε • (-(Multiplicative.toAdd m) v))),
  map_one' := by
    suffices IsLocalization.mk' S (AddMonoidAlgebra.single 0 1) (1 : Submonoid.powers (function_of_vector _)) = 1 by simpa
    rw [IsLocalization.mk'_one]
    apply map_one
  map_mul' := fun x y => by
    simp only [Algebra.id.smul_eq_mul, zpow_neg, Int.mul_neg_eq_neg_mul_symm,
      neg_add_rev, LinearMap.add_apply, toAdd_mul,
      smul_add, smul_neg, zpow_neg]
    rw [<- one_mul (1 : ℕ), ←AddMonoidAlgebra.single_mul_single]
    rw [<- one_mul (1 : Submonoid.powers (function_of_vector v)),
      IsLocalization.mk'_mul]
    rw [mul_one]
    simp only [mul_one, zpow_add, zpow_neg, zpow_sub, Int.mul_neg_eq_neg_mul_symm, Units.val_mul]
    ring  }

def monomial_to_away : Multiplicative (Module.Dual ℤ N) →* S :=
{ toFun := fun m => 
    IsLocalization.mk' S
    (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1 : AddMonoidAlgebra ℕ (Module.Dual ℤ N)) (1 : Submonoid.powers (function_of_vector (μ.sign • μ.src_vect)))
        * ↑((μ.away_unit S)^(ε • (-(Multiplicative.toAdd m) μ.src_vect))),
  map_one' := by
    suffices IsLocalization.mk' S (AddMonoidAlgebra.single 0 1) (1 : Submonoid.powers (function_of_vector _)) = 1 by simpa
    rw [IsLocalization.mk'_one]
    apply map_one
  map_mul' := fun x y => by
    simp only [Algebra.id.smul_eq_mul, zpow_neg, Int.mul_neg_eq_neg_mul_symm,
      neg_add_rev, LinearMap.add_apply, toAdd_mul,
      smul_add, smul_neg, zpow_neg]
    rw [<- one_mul (1 : ℕ), ←AddMonoidAlgebra.single_mul_single]
    rw [<- one_mul (1 : Submonoid.powers (function_of_vector (μ.sign • μ.src_vect))),
      IsLocalization.mk'_mul]
    rw [mul_one]
    simp only [mul_one, zpow_add, zpow_neg, zpow_sub, Int.mul_neg_eq_neg_mul_symm, Units.val_mul]
    ring  }

def to_away : ring_of_function N →+* S :=
  AddMonoidAlgebra.liftNCRingHom (Nat.castRingHom S)
(μ.monomial_to_away S ε) (fun _ _ => (Commute.all _ _))

def to_away' (v : N) [IsLocalization.Away (function_of_vector v) S] : 
    ring_of_function N →+* S :=
  AddMonoidAlgebra.liftNCRingHom (Nat.castRingHom S)
(monomial_to_away' S ε v) (fun _ _ => (Commute.all _ _))

end SeedMutation
  
  
instance (v : N) [IsLocalization.Away (function_of_vector v) S] :
  IsLocalization.Away (function_of_vector (-v)) S := by
  sorry


-- @[simp]
-- lemma to_away_of_function_of_mutation_direction (v : N) (hv : IsMutationDirection μ v) :
-- (μ.to_away S ε) (function_of_vector v) = 
--   IsLocalization.mk' S (function_of_vector v) 
--       (1 : Submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) := by
--   dsimp [SeedMutation.to_away, function_of_vector,
--     SeedMutation.monomial_to_away, AddMonoidAlgebra.liftNCRingHom]
--   cases' hv with k hk
--   simp only [smul_neg, zpow_neg, MonoidHom.coe_mk, OneHom.coe_mk, map_add, RingHom.coe_mk,
--     AddMonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, map_one, ofAdd_zero, toAdd_one, LinearMap.zero_apply, smul_zero,
--     zpow_zero, inv_one, Units.val_one, mul_one, one_mul, toAdd_ofAdd, toLin_apply]
--   dsimp
--   erw [IsLocalization.mk'_one, IsLocalization.mk'_one, <- AddMonoidAlgebra.one_def]
--   simp only [ring_hom.map_add, add_left_inj, ring_hom.map_one]
--   simpa

-- lemma is_unit_to_away : 
-- is_unit (μ.to_away S ε (function_of_vector (μ.sign • μ.src_vect))) := by
--   rw to_away_of_function_of_mutation_direction,
--   rw is_localization.mk'_one,
--   refine @is_localization.map_units (ring_of_function N) _ _ S _ _ _ 
--     ⟨function_of_vector (μ.sign • μ.src_vect), submonoid.mem_powers _⟩,

@[simp]
lemma to_away_of_function_of_mutation_direction' (v : N) [IsLocalization.Away (function_of_vector v) S] :
(SeedMutation.to_away' S ε v) (function_of_vector v) = 
  IsLocalization.mk' S (function_of_vector v) 
      (1 : Submonoid.powers (function_of_vector v)) := by
  dsimp [SeedMutation.to_away',
    SeedMutation.monomial_to_away', AddMonoidAlgebra.liftNCRingHom]
  -- cases' hv with k hk
  simp only [smul_neg, zpow_neg, MonoidHom.coe_mk, OneHom.coe_mk, map_add, RingHom.coe_mk,
    AddMonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, map_one, ofAdd_zero, toAdd_one, LinearMap.zero_apply, smul_zero,
    zpow_zero, inv_one, Units.val_one, mul_one, one_mul, toAdd_ofAdd, toLin_apply]
  simp_rw [IsLocalization.mk'_one]
  dsimp [function_of_vector]
  simp
  rw [←AddMonoidAlgebra.one_def]
  simp only [map_add, AddMonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, map_one, toAdd_ofAdd, toLin_apply,
    one_mul]
  dsimp
  simp [RingHom.map_add, add_left_inj, RingHom.map_one, self_eq_zero SkewSymmForm.skew]
  rfl
  

lemma is_unit_to_away' (v : N) [IsLocalization.Away (function_of_vector v) S] : 
    IsUnit (SeedMutation.to_away' S ε v (function_of_vector v)) := by
  rw [to_away_of_function_of_mutation_direction', IsLocalization.mk'_one]
  refine @IsLocalization.map_units (ring_of_function N) _ _ S _ _ _ 
    ⟨function_of_vector v, Submonoid.mem_powers _⟩

def SeedMutation.ring_hom_away : S →+* S :=
is_localization.away.lift (function_of_vector (μ.sign • μ.src_vect)) (is_unit_to_away μ S ε)

def SeedMutation.ring_hom_away' (v : N) [IsLocalization.Away (function_of_vector v) S] : S →+* S :=
IsLocalization.Away.lift (function_of_vector v) (is_unit_to_away' S ε v)


def SeedMutation.ring_equiv_away' (v : N) [IsLocalization.Away (function_of_vector v) S] : S ≃+* S :=
  RingEquiv.ofHomInv (ring_hom_away' S ε v) (ring_hom_away' S (-ε) (-v)) (by
      ext x
      simp
      _
    ) 
    _


@[simp] lemma mutation_away_map_const' : 
((μ.ring_hom_away S ε).comp (algebra_map (ring_of_function N) S)).comp 
  add_monoid_algebra.single_zero_ring_hom =
  (algebra_map (ring_of_function N) S ).comp add_monoid_algebra.single_zero_ring_hom := 
dec_trivial

@[simp] lemma mutation_away_map_const (b : ℤ) : 
μ.ring_hom_away S ε ((algebra_map (ring_of_function N) S) (finsupp.single 0 b)) =
algebra_map (ring_of_function N) S (finsupp.single 0 b) :=
begin
  have h : finsupp.single (0 : module.dual ℤ N) b = add_monoid_algebra.single_zero_ring_hom b := by refl,
  rw h,
  repeat {rw <- ring_hom.comp_apply},
  repeat {rw <- ring_hom.coe_comp},
  rw mutation_away_map_const',
end

@[simp] lemma mutation_away_map_monomial (a : multiplicative(module.dual ℤ N)) : 
(μ.ring_hom_away S ε) ((algebra_map (ring_of_function N) S) (finsupp.single a 1)) =
algebra_map (ring_of_function N) S (finsupp.single a 1) 
  * ↑((μ.away_unit S) ^ (ε • (- a μ.src_vect))) :=
begin
  unfold SeedMutation.ring_hom_away is_localization.away.lift,
  rw is_localization.lift_eq,
  unfold SeedMutation.to_away add_monoid_algebra.lift_nc_ring_hom,
  dsimp,
  rw add_monoid_algebra.lift_nc_single,
  unfold SeedMutation.monomial_to_away,
  dsimp,
  rw [int.cast_one, one_mul],
  simp only [gpow_neg, units.ne_zero, or_false, mul_neg_eq_neg_mul_symm, mul_eq_mul_right_iff],
  rw is_localization.mk'_one,
  congr,
end

@[simp]
lemma mutation_away_eq_self_of_gpow_of_unit (k : ℤ) : 
μ.ring_hom_away S ε ↑((μ.away_unit S) ^ k ) = ↑((μ.away_unit S) ^ k) := 
begin
  unfold SeedMutation.ring_hom_away is_localization.away.lift SeedMutation.away_unit,
  induction k,
  { dsimp,
    rw [gpow_coe_nat,  units.coe_pow, ring_hom.map_pow], 
    dsimp,
    rw [is_localization.lift_eq],
    apply congr_arg (λ x : S, x ^ k),
    rw to_away_of_function_of_mutation_direction,
    rw is_localization.mk'_one },
  { rw [gpow_neg_succ_of_nat, <- inv_pow,units.coe_pow],
    rw [ring_hom.map_pow],
    apply congr_arg (λ x : S, x ^ k.succ),
    simp only [units.coe_mk, units.inv_mk],
    rw is_localization.lift_mk'_spec,
    simp only [set_like.coe_mk, to_away_of_function_of_mutation_direction, ring_hom.map_one],
    rw <- is_localization.mk'_mul,
    rw [one_mul, mul_one, is_localization.mk'_self] },
end


def SeedMutation.ring_equiv_away : S ≃+* S :=
ring_equiv.of_hom_inv (μ.ring_hom_away S ε)
(μ.ring_hom_away S (-ε))
begin
  ext x,
  have : ring_hom.id S = is_localization.lift 
  (@is_localization.map_units _ _ (submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) S _ _ _),
  { ext z,
    rw ring_hom.id_apply,
    rw is_localization.lift_id },
  rw this,
  rw is_localization.lift_unique,
  rw <- function.funext_iff,
  rw [<- function.comp, <- ring_hom.coe_comp, function.funext_iff,
    <- @ring_hom.ext_iff (ring_of_function N) S],
  apply add_monoid_algebra.ring_hom_ext,
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_away_map_const, mutation_away_map_const] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_away_map_monomial, ring_hom.map_mul, mutation_away_map_monomial, mul_assoc],
    simp only [gpow_neg],
    rw mutation_away_eq_self_of_gpow_of_unit,
    simp only [algebra.id.smul_eq_mul, gpow_neg, mul_neg_eq_neg_mul_symm],
    simp only [neg_mul_eq_neg_mul_symm, gpow_neg, inv_inv],
    erw units.val_inv,
    apply mul_one },
end
begin
  ext x,
  have : ring_hom.id S = is_localization.lift 
  (@is_localization.map_units _ _ (submonoid.powers (function_of_vector (μ.sign • μ.src_vect))) S _ _ _),
  { ext z,
    rw ring_hom.id_apply,
    rw is_localization.lift_id },
  rw this,
  rw is_localization.lift_unique,
  rw <- function.funext_iff,
  rw [<- function.comp, <- ring_hom.coe_comp, function.funext_iff,
    <- @ring_hom.ext_iff (ring_of_function N) S],
  apply add_monoid_algebra.ring_hom_ext,
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_away_map_const, mutation_away_map_const] },
  { intros a,
    repeat {rw ring_hom.coe_comp, rw function.comp},
    dsimp,
    rw [mutation_away_map_monomial, ring_hom.map_mul, mutation_away_map_monomial, mul_assoc],
    simp only [gpow_neg],
    rw mutation_away_eq_self_of_gpow_of_unit,
    simp only [algebra.id.smul_eq_mul, gpow_neg, mul_neg_eq_neg_mul_symm],
    simp only [neg_mul_eq_neg_mul_symm, gpow_neg, inv_inv],
    erw units.val_inv,
    apply mul_one },
end

end mutation_away

section mutation_frac

variables 
[is_integral_domain (ring_of_function N)]
{s s' : Multiset N} (μ : SeedMutation s s')
(K : Type*) [field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K] 
(ε : ℤ) [is_sign ε]

local attribute [class] is_integral_domain

def ring_of_function.integral_domain : integral_domain (ring_of_function N) := 
is_integral_domain.to_integral_domain _ (by assumption)

local attribute [instance] ring_of_function.integral_domain 

abbreviation SeedMutation.away := localization.away (function_of_vector (μ.sign • μ.src_vect))

def away.integral_domain : integral_domain μ.away :=
is_localization.integral_domain_of_le_non_zero_divisors μ.away
  (powers_le_non_zero_divisors_of_no_zero_divisors (function_of_vector_ne_zero (μ.sign • μ.src_vect)))

local attribute [instance]  away.integral_domain

def SeedMutation.algebra_of_away_frac : algebra μ.away K :=
is_localization.algebra_of_away_frac (function_of_vector_ne_zero (μ.sign • μ.src_vect)) μ.away K

local attribute[instance] SeedMutation.algebra_of_away_frac

def SeedMutation.is_fraction_of_algebra_of_away_frac : 
@is_fraction_ring μ.away _ K _ (μ.algebra_of_away_frac K) :=
is_localization.is_fraction_of_algebra_of_away_frac _ μ.away K

local attribute[instance] SeedMutation.is_fraction_of_algebra_of_away_frac

private def z 
{K : Type*} [field K] [algebra (ring_of_function N) K] [is_fraction_ring (ring_of_function N) K] 
(m : module.dual ℤ N) := algebra_map (ring_of_function N) K (finsupp.single m 1)

def SeedMutation.field_equiv : K ≃+* K := 
is_fraction_ring.field_equiv_of_ring_equiv (μ.ring_equiv_away μ.away 1)

lemma mutation_field_equiv_map_monomial (m : module.dual ℤ N) : 
μ.field_equiv K (z m)  = 
z m * (1 + z (B (μ.sign • μ.src_vect))) ^ - m μ.src_vect :=
begin
  unfold z SeedMutation.field_equiv is_fraction_ring.field_equiv_of_ring_equiv SeedMutation.ring_equiv_away,
  let h_ne := function_of_vector_ne_zero (μ.sign • μ.src_vect),
  repeat {rw is_localization.eq_comp_map_of_lift_of_of_away_frac h_ne μ.away K},
  simp only [fpow_neg, linear_map.map_smul, is_localization.ring_equiv_of_ring_equiv_eq, 
    mutation_away_map_monomial, algebra.id.smul_eq_mul, one_mul, gpow_neg, mul_eq_mul_left_iff, inv_inj', 
    mul_neg_eq_neg_mul_symm, ring_hom.map_units_inv, ring_equiv.of_hom_inv_apply, ring_hom.map_mul],
  apply or.inl,
  unfold SeedMutation.away_unit function_of_vector,
  induction m μ.src_vect;
  simp only [ring_hom.map_add, units.coe_mk, gpow_neg_succ_of_nat, inv_inj', ring_hom.map_pow,
      ring_hom.map_units_inv, linear_map.map_smul, units.coe_pow, int.of_nat_eq_coe, gpow_coe_nat];
  rw <- add_monoid_algebra.one_def;
  simp only [ring_hom.map_one],
end

end mutation_frac

end