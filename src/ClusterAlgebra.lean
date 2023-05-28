section SeedMutation

-- variable (v : N) (ε : ℤ)

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