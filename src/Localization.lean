import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Away.Basic
/-!
This file proves some properties on localizations that are needed to define mutations.

## Main statements

* `IsLocalization_of_lift_of_sup`: let `A`, `B`, and `C` are commutative rings, and `M` and `N`
  are Submonoids of `A`. Suppose that `B` is a localization of `A` at `M` and `C` is a localization
  of `A` at `M ⊔ N`. Then `C` is a localization of `B` at the image of `N` by the localization map
  from `A` to `B`.

-/

namespace IsLocalization

noncomputable
section

variable
{A : Type _}  [CommRing A]
(M N : Submonoid A)
(B : Type _) [CommRing B] (C : Type _) [CommRing C]
[Algebra A B] [Algebra A C]
[IsLocalization M B] [IsLocalization (M ⊔ N) C]

def lift_of_sup : B →+* C :=
lift <| fun h => by simpa using map_units C (⟨h.1, SetLike.le_def.mp le_sup_left h.2⟩ : ↑(M ⊔ N))

def algebra_of_lift_of_sup : Algebra B C := RingHom.toAlgebra (lift_of_sup M N B C)

-- attribute [local instance] algebra_of_lift_of_sup

lemma eq_comp_map_of_lift_of_sup (a : A) : algebraMap A C a = lift_of_sup M N B C (algebraMap A B a) := by
  rw [lift_of_sup, lift_eq]


lemma eq_comp_of_lift_of_sup : (algebraMap A C) = (lift_of_sup M N B C).comp (algebraMap A B) := by
ext; exact eq_comp_map_of_lift_of_sup M N B C _

lemma IsLocalization_of_lift_of_sup
    {A : Type _}  [CommRing A]
    (M : Submonoid A) (N : Submonoid A)
    (B : Type _) [CommRing B] (C : Type _) [CommRing C]
    [Algebra A B] [Algebra A C]
    [IsLocalization M B] [IsLocalization (M ⊔ N) C] :
    letI : Algebra B C := RingHom.toAlgebra (lift_of_sup M N B C)
    IsLocalization (N.map (algebraMap A B) : Submonoid B) C := by
  letI : Algebra B C := RingHom.toAlgebra (lift_of_sup M N B C)
  letI : IsScalarTower A B C := by sorry
  apply isLocalization_of_submonoid_le B C M (M ⊔ N) (by simp)
-- { map_units := by
--     intros n'
--     rcases Submonoid.mem_map.mp n'.property with ⟨n, ⟨hn, H⟩⟩
--     have : n ∈ M ⊔ N := set_like.le_def.mp le_sup_right hn
--     simp only [ring_hom.coe_monoid_hom, subtype.val_eq_coe] at H
--     rw [<- H, <- eq_comp_map_of_lift_of_sup]
--     exact IsLocalization.map_units C ⟨n, this⟩
--   surj := by
--     intros c
--     rcases surj (M ⊔ N) c with ⟨⟨a, ⟨mn, h_mn⟩⟩ , H⟩
--     rcases Submonoid.mem_sup.mp h_mn with ⟨m, hm, n, hn, H'⟩
--     repeat {rw [eq_comp_map_of_lift_of_sup M N B C] at H}
--     rw [set_like.coe_mk] at H
--     dsimp at H
--     have : algebraMap A B n ∈ (N.map (algebraMap A B) : Submonoid B)
--     apply Submonoid.mem_map.mpr
--     use n
--     use hn
--     rw [ring_hom.coe_monoid_hom]
--     constructor
--     constructor
--     exact ↑((is_unit.unit (map_units B ⟨m, hm⟩))⁻¹) * (algebraMap A B a)
--     exact ⟨algebraMap A B n, this⟩
--     simp only [set_like.coe_mk, ring_hom.map_mul]
--     rw [<- H, <- H']
--     simp only [ring_hom.map_mul]
--     ring_nf
--     apply congr_arg (· * c)
--     rw  [<- one_mul ((algebraMap B C) ((algebraMap A B) n))]
--     apply congr_arg (· * ((algebraMap B C) ((algebraMap A B) n)))
--     rw [<- ring_hom.map_mul]
--     rw [<- ring_hom.map_one (algebraMap B C)]
--     apply congr_arg
--     rw [units.mul_inv_of_eq]
--     rw [is_unit.unit_spec]
--   eq_iff_exists := by
--     intros b₁ b₂
--     split
--     { intros h
--       rcases surj M b₁ with ⟨⟨a₁, ⟨m₁, hm₁⟩⟩, H₁⟩
--       rcases surj M b₂ with ⟨⟨a₂, ⟨m₂, hm₂⟩⟩, H₂⟩
--       have : algebraMap A C (a₁ * m₂) = algebraMap A C (a₂ * m₁)
--       rw [eq_comp_map_of_lift_of_sup M N B C]
--       rw [eq_comp_map_of_lift_of_sup M N B C]
--       dsimp at *
--       simp only [ring_hom.map_mul]
--       rw [<- H₁, <- H₂]
--       simp only [ring_hom.map_mul]
--       rw [h]
--       ring
--       rcases (eq_iff_exists (M ⊔ N) C).mp this with ⟨⟨mn, mn_in⟩, hmn⟩
--       rcases Submonoid.mem_sup.mp mn_in with ⟨m, hm, n, hn, H'⟩
--       dsimp at *
--       have : algebraMap A B n ∈ Submonoid.map ↑(algebraMap A B) N
--       apply Submonoid.mem_map.mpr
--       use n
--       use hn
--       rw [ring_hom.coe_monoid_hom]
--       use ⟨algebraMap A B n, this⟩
--       dsimp
--       refine (is_unit.mul_left_inj _).mp _
--       exact algebraMap A B m
--       exact map_units B ⟨m, hm⟩
--       repeat {rw [mul_assoc, <- ring_hom.map_mul]}
--       rw [mul_comm] at H'
--       rw [H']
--       have hb₁ : b₁ = mk' B a₁ ⟨m₁, hm₁⟩ := eq_mk'_iff_mul_eq.mpr H₁
--       have hb₂ : b₂ = mk' B a₂ ⟨m₂, hm₂⟩ := eq_mk'_iff_mul_eq.mpr H₂
--       rw [hb₁, hb₂]
--       -- nth_rewrite_lhs 0 mul_comm
--       -- nth_rewrite_rhs 0 mul_comm
--       rw [mul_mk'_eq_mk'_of_mul, mul_mk'_eq_mk'_of_mul]
--       refine mk'_eq_of_eq _
--       dsimp
--       exact calc mn * a₂ * m₁ = a₂ * m₁ * mn := by ring
--       _                       = a₁ * m₂ * mn := by rw [<-hmn]
--       _                       = mn * a₁ * m₂ := by ring }
--     { intros h
--       rcases h with ⟨⟨n', hn'⟩, H⟩
--       rcases Submonoid.mem_map.mp hn' with ⟨n, ⟨hn, H'⟩⟩
--       have n_in : n ∈ M ⊔ N := Submonoid.mem_sup_right hn
--       rcases surj M b₁ with ⟨⟨a₁, ⟨m₁, hm₁⟩⟩, H₁⟩
--       rcases surj M b₂ with ⟨⟨a₂, ⟨m₂, hm₂⟩⟩, H₂⟩
--       dsimp at *
--       have : ∃ m : M, a₁ * m₂ * n * m = a₂ * m₁ * n * m
--       refine (eq_iff_exists M B).mp _
--       simp only [ring_hom.map_mul]
--       rw [H']
--       rw [<- H₁, <- H₂]
--       exact calc b₁ * (algebraMap A B) m₁ * (algebraMap A B) m₂ * n'
--                = b₁ * n' * (algebraMap A B) m₁ * (algebraMap A B) m₂  := by ring
--       _        = b₂ * n' * (algebraMap A B) m₁ * (algebraMap A B) m₂  := by rw [H]
--       _        = b₂ * (algebraMap A B) m₂ * (algebraMap A B) m₁ * n'  := by ring
--       rcases this with ⟨⟨m, hm⟩, H''⟩
--       dsimp at H''
--       have p : algebraMap A C (a₁ * m₂) = algebraMap A C (a₂ * m₁)
--       refine (eq_iff_exists (M ⊔ N) C).mpr _
--       use ⟨n * m, mul_comm m n ▸ Submonoid.mul_mem _ (Submonoid.mem_sup_left hm) (Submonoid.mem_sup_right hn)⟩
--       dsimp
--       repeat {rw <- mul_assoc}
--       exact H''
--       repeat {rw eq_comp_map_of_lift_of_sup M N B C at p}
--       simp only [ring_hom.map_mul] at p
--       rw [<- H₁, <- H₂] at p
--       refine (is_unit.mul_left_inj _).mp _
--       exact algebraMap A C (m₁ * m₂)
--       have : m₁ * m₂ ∈ M ⊔ N
--       refine Submonoid.mul_mem _ (Submonoid.mem_sup_left hm₁) (Submonoid.mem_sup_left hm₂)
--       exact map_units C ⟨m₁ * m₂, this⟩
--       repeat {rw eq_comp_map_of_lift_of_sup M N B C}
--       simp only [ring_hom.map_mul] at *
--       repeat {rw mul_assoc at *}
--       nth_rewrite 3 mul_comm
--       exact p }}

end 

section

variable
{A : Type _}  [CommRing A]
{M : Submonoid A} {N : Submonoid A}
(B : Type _) [CommRing B] (C : Type _) [CommRing C]
[Algebra A B] [Algebra A C]
[IsLocalization M B] [IsLocalization N C]
(h : M ≤ N)

noncomputable def lift_of_le : B →+* C :=
@lift_of_sup A _ M N B _ C _ _ _ _ (by rw [sup_eq_right.mpr h]; infer_instance)

noncomputable def algebra_of_lift_of_le : Algebra B C := 
RingHom.toAlgebra (lift_of_le B C h)

lemma eq_comp_map_of_lift_of_le (a : A) : 
algebraMap A C a = @algebraMap B C _ _ (algebra_of_lift_of_le B C h) (algebraMap A B a) := by
  have : @algebraMap B C _ _ (algebra_of_lift_of_le B C h) = lift_of_le B C h := by rfl
  rw [this]
  unfold lift_of_le lift_of_sup
  rw [lift_eq]

def IsLocalization_of_lift_of_le (h : M ≤ N) :
@IsLocalization _ _ (N.map (algebraMap A B) : Submonoid B) C _ (algebra_of_lift_of_le B C h) :=
@IsLocalization_of_lift_of_sup A _ M N B _ C _ _ _ _ (by rw [sup_eq_right.mpr h]; infer_instance)

end

section

variable
{A : Type _} [CommRing A] {M N : Submonoid A}
(B : Type _) [CommRing B] 
[Algebra A B] [IsLocalization M B]

lemma IsLocalization_of_le_of_exists_mul_mem (h_le : M ≤ N) (h : ∀ n : N, ∃ a : A, ↑n * a ∈ M) :
    IsLocalization N B where
  map_units' := by
    rintro ⟨n, hn⟩
    rcases h ⟨n, hn⟩ with ⟨a, hm⟩
    let p := map_units B ⟨n * a, hm⟩
    simp only [IsUnit.mul_iff, map_mul] at p
    exact p.left
  surj' := by
    intros b
    rcases surj M b with ⟨⟨a, ⟨m, hm⟩⟩, H⟩
    use ⟨a, ⟨m, SetLike.le_def.mp h_le hm⟩⟩
    exact H
  eq_iff_exists' := by
    intros a₁ a₂
    constructor
    intros ha
    rcases (eq_iff_exists M B).mp ha with ⟨⟨m, hm⟩, H⟩
    use ⟨m, SetLike.le_def.mp h_le hm⟩
    exact H
    rintro ⟨⟨n, hn⟩, H⟩
    rcases h ⟨n, hn⟩ with ⟨a, hm⟩
    apply (eq_iff_exists M B).mpr _
    use ⟨n * a, hm⟩
    exact calc n * a * a₁ = a * (n * a₁) := by ring
    _                     = a * (n * a₂) := by rw [H]
    _                     = n * a * a₂   := by ring

end

section

variable {A : Type _} [CommRing A] [IsDomain A] {f : A} (h_ne : f ≠ 0)
(B : Type _) [CommRing B] [IsDomain B] (C : Type _) [CommRing C] [IsDomain C]
[Algebra A B] [Algebra A C]
[IsLocalization.Away f B] [IsFractionRing A C]

--local attribute[instance] algebra_of_lift_of_le
-- include f h_ne

noncomputable def lift_of_away_frac : B →+* C :=
lift_of_le B C (powers_le_nonZeroDivisors_of_noZeroDivisors h_ne)

noncomputable def algebra_of_away_frac : Algebra B C :=
RingHom.toAlgebra (lift_of_away_frac h_ne B C)

--local attribute [instance] algebra_of_away_frac

lemma eq_comp_map_of_lift_of_of_away_frac (a : A) : algebraMap A C a = 
    @algebraMap B C _ _ (algebra_of_away_frac h_ne B C) (algebraMap A B a) := by
  have : @algebraMap B C _ _ (algebra_of_away_frac h_ne B C) = lift_of_away_frac h_ne B C := by rfl
  rw [this]
  unfold lift_of_away_frac lift_of_le lift_of_sup
  rw [lift_eq]

def IsLocalization_of_away :
@IsLocalization B _ ((nonZeroDivisors A).map (algebraMap A B) : Submonoid B) C _ 
  (algebra_of_lift_of_le B C
  (powers_le_nonZeroDivisors_of_noZeroDivisors  h_ne)) :=
IsLocalization_of_lift_of_le B C _

lemma non_zero_map_le_non_zero :
((nonZeroDivisors A).map (algebraMap A B) : Submonoid B) ≤ nonZeroDivisors B := by
  rintro x ⟨a, ⟨ha, H⟩⟩
  rw [<- H]
  refine map_mem_nonZeroDivisors _ ?_ ha
  refine IsLocalization.injective B (powers_le_nonZeroDivisors_of_noZeroDivisors  h_ne)

lemma exists_mul_mem_of_away_of_ne_zero (g : nonZeroDivisors B) :
∃ b : B, ↑g * b ∈ ((nonZeroDivisors A).map (algebraMap A B) : Submonoid B) := by
  rcases IsLocalization.surj (Submonoid.powers f) (g : B) with ⟨⟨gn, ⟨gd, hg⟩⟩, H⟩
  dsimp at H
  use algebraMap A B gd
  rw [H]
  simp only [Submonoid.mem_map]
  refine ⟨gn, ?_, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intros h
  let p := (IsLocalization.to_map_eq_zero_iff B (powers_le_nonZeroDivisors_of_noZeroDivisors  h_ne)).mpr h
  rw [<- H] at p
  have hgd : (algebraMap A B) gd ∈ nonZeroDivisors B
  rw [mem_nonZeroDivisors_iff_ne_zero]
  refine IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors B (powers_le_nonZeroDivisors_of_noZeroDivisors  h_ne) ?_
  refine SetLike.le_def.mp (powers_le_nonZeroDivisors_of_noZeroDivisors  h_ne) hg
  let q := (nonZeroDivisors B).mul_mem' g.2 hgd
  simp at q
  rw [mem_nonZeroDivisors_iff_ne_zero] at q
  refine q p

def is_fraction_of_algebra_of_away_frac :
@IsFractionRing B _ C _ (algebra_of_away_frac h_ne B C) := by
  letI : Algebra B C := (algebra_of_away_frac h_ne B C)
  haveI := IsLocalization_of_away h_ne B C
  exact IsLocalization_of_le_of_exists_mul_mem C (non_zero_map_le_non_zero h_ne B) 
    (fun n => exists_mul_mem_of_away_of_ne_zero h_ne B n)

end

end IsLocalization