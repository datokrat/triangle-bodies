import convex linalg multiset data.fintype.basic linear_algebra.dimension
  measure_theory.measure.measure_space_def
  data.multiset
  linear_algebra.finite_dimensional
  analysis.inner_product_space.projection
  data.multiset.basic
  data.nat.basic

open_locale pointwise

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma dim_finrank : dim = finite_dimensional.finrank ℝ := rfl

lemma project_subspace_def (E F : submodule ℝ V) : project_subspace E F = F.map (orthogonal_projection E).to_linear_map
:= rfl

lemma zero_projection_of_le {E F : subspace ℝ V}
(h : F ≤ E) : project_subspace Eᗮ F = ⊥ :=
begin
  apply linear_map.le_ker_iff_map.mp,
  change F ≤ (proj Eᗮ).ker,
  simp only [ker_of_complementary_orthogonal_projection E, h],
end

lemma xyz {C : multiset (set V)} {E : submodule ℝ V}
: project_subspace Eᗮ (vector_span ℝ C.sum) = vector_span ℝ (project_collection Eᗮ C).sum :=
begin
  simp [project_subspace_vector_span, minksum_proj_commute_multiset],
end

lemma abc {C : multiset (set V)} {E : submodule ℝ V}
: project_subspace Eᗮ (E + vector_span ℝ C.sum) = vector_span ℝ (project_collection Eᗮ C).sum :=
begin
  simp only [project_subspace, submodule.add_eq_sup, submodule.map_sup],
  rw [←project_subspace_def],
  simp [zero_projection_of_le, xyz.symm],
  refl,
end

lemma z {A : multiset (set V)} {E : submodule ℝ V}
(h : Π B : multiset (set V),
B ≤ A → dim (E + (vector_span ℝ B.sum) : submodule ℝ V) ≥ dim E + B.card)
: semicritical (project_collection Eᗮ A) :=
begin
  rintro F Fsub,
  rcases multiset_exists_of_le_map Fsub with ⟨G, Gsub, G_to_F⟩,
  let W : submodule ℝ V := E + vector_span ℝ G.sum,
  have rn := subspace_rank_nullity (orthogonal_projection Eᗮ).to_linear_map W,
  suffices hsuff : common_dimension F = dim (project_subspace Eᗮ W) ∧
                   dim E ≥ dim ((proj Eᗮ).ker ⊓ W : submodule ℝ V) ∧
                   dim W ≥ dim E + F.card,
  {
    calc common_dimension F
       = dim (project_subspace Eᗮ W) : hsuff.1
  ...  = dim W - dim ((proj Eᗮ).ker ⊓ W : submodule ℝ V) : _
  ...  ≥ dim W - dim E : nat.sub_le_sub_left (dim W) hsuff.2.1
  ...  ≥ multiset.card F : _,
    {
      rw [dim_finrank, ←rn], -- here is an interesting case I don't understand
      dsimp only [proj],     -- Why does dsimp work but simp does not?
      dsimp only [project_subspace],
      simp,
    },
    {
      -- Natural numbers are hard.
      rw [←nat.add_sub_cancel (multiset.card F) (dim E), add_comm (multiset.card F)],
      refine nat.sub_le_sub_right hsuff.2.2 (dim E),
    }
  },
  repeat {split},
  {
    -- have : W = E + vector_span ℝ G.sum := rfl,
    rw [abc, project_collection, G_to_F],
    refl,
  },
  {
    refine finrank_le_of_le _,
    refine le_trans inf_le_left _,
    rw [ker_of_complementary_orthogonal_projection E],
    exact le_refl E,
  },
  {
    rw [←G_to_F],
    simp only [multiset.card_map],
    exact h G Gsub,
  },
end

lemma common_dimension_of_empty {a : set V}
(he : a = ∅) : common_dimension ({a} : multiset (set V)) = 0 :=
begin
  simp [common_dimension, vector_span, he],
end

lemma nonempty_of_semicritical {A : multiset (set V)} (hsc : semicritical A)
(a : set V) (ha : a ∈ A) : a.nonempty :=
begin
  by_contradiction,
  have he : a = ∅ := sorry,
  have : common_dimension {a} = 0 := common_dimension_of_empty he,
  have h2 := hsc {a} (multiset.singleton_le.mpr ha),
  rw [multiset.card_singleton] at h2,
  rw [this] at h2,
  linarith,
end

lemma zz {A B : multiset (set V)} {E : submodule ℝ V}
(hsc : semicritical (A + B)) (hE : diff A.sum ≤ E) (hdim : dim E ≤ A.card)
(C : multiset (set V)) (hCB : C ≤ B) :
dim (E + (vector_span ℝ C.sum) : submodule ℝ V) ≥ dim E + C.card :=
begin
  calc dim (E + (vector_span ℝ C.sum) : submodule ℝ V)
     ≥ dim ((vector_span ℝ A.sum) + (vector_span ℝ C.sum) : submodule ℝ V) : by
          {
            apply submodule.finrank_mono,
            refine sup_le_sup_right _ _,
            apply submodule.span_le.mpr,
            assumption,
          }
...  = common_dimension (A + C)                                            : by
          {
            simp only [common_dimension],
            rw [multiset.sum_add, vector_span_sum_commute],
            {
              apply multiset_sum_nonempty_of_elements,
              refine nonempty_of_semicritical (subcollection_semicritical (show A ≤ A + B, by simp) hsc),
            },
            {
              apply multiset_sum_nonempty_of_elements,
              refine nonempty_of_semicritical (subcollection_semicritical (show C ≤ A + B, by { refine le_trans hCB _, simp [hCB] }) hsc),
            }
          }
...  ≥ (A + C).card                                                        : by
          {
            have : A + C ≤ A + B := by simp [hCB],
            refine hsc (A + C) this,
          }
...  = A.card + C.card                                                     : multiset.card_add A C
...  ≥ dim E + C.card                                                      : add_le_add hdim (le_refl _),
end

lemma subcritical_factorization_3 {C D : multiset (set V)} {E : submodule ℝ V}
(hE : diff D.sum ≤ E) (hne : ∀ x ∈ C + D, set.nonempty x) :
common_dimension D + common_dimension (project_collection Eᗮ C) ≤ common_dimension (C + D) :=
begin
  let W := vector_span ℝ (C + D).sum,
  have ss_rn := subspace_rank_nullity (proj Eᗮ) W,
  suffices h : common_dimension D ≤ dim (((proj Eᗮ).ker ⊓ W): submodule ℝ V) ∧
    common_dimension (project_collection Eᗮ C) = dim (project_subspace Eᗮ W),
  {
    rw [add_comm],
    calc common_dimension (C + D)
       = dim W : by refl
   ... = dim (project_subspace Eᗮ W) + dim ((proj Eᗮ).ker ⊓ W : submodule ℝ V) : ss_rn.symm
   ... ≥ dim (project_subspace Eᗮ W) + common_dimension D : by simp [h.1]
   ... = common_dimension (project_collection Eᗮ C) + common_dimension D : by simp [h.2],
  },
  split,
  {
    refine finrank_le_of_le _,
    rw [ker_of_complementary_orthogonal_projection E],
    refine le_inf (submodule.span_le.mpr hE) _,
    simp only [vector_span],
    refine submodule.span_mono _,
    change diff D.sum ⊆ diff (C + D).sum,
    simp only [multiset.sum_add],
    refine diff_set_le_add _ _ _,
    refine multiset_sum_nonempty_of_elements _,
    intros a haC,
    refine hne a _,
    exact multiset.mem_add.mpr (or.inl haC),
  },
  {
    simp only [common_dimension],
    rw [←xyz],
    suffices h : project_subspace Eᗮ (vector_span ℝ C.sum) = project_subspace Eᗮ (vector_span ℝ (C + D).sum),
    {rw [h]},
    {
      simp only [multiset.sum_add],
      have CD_nonempty : C.sum.nonempty ∧ D.sum.nonempty :=
      begin
        apply nonempty_sets_of_nonempty_sum,
        rw [←multiset.sum_add],
        exact multiset_sum_nonempty_of_elements hne,
      end,
      rw [vector_span_sum_commute C.sum D.sum CD_nonempty.1 CD_nonempty.2],
      simp only [project_subspace, submodule.add_eq_sup, submodule.map_sup, left_eq_sup],
      refine le_trans _ bot_le,
      refine eq_bot_iff.mp _,
      refine zero_projection_of_le _,
      simp only [vector_span, submodule.span_le],
      assumption,
    }
  }
end

lemma subcritical_factorization {C D : multiset (set V)} {E : submodule ℝ V}
(hDC : D ≤ C) (hE : diff D.sum ≤ E) (hdim : finite_dimensional.finrank ℝ E ≤ D.card) :
semicritical C ↔ (semicritical D ∧ semicritical (project_collection Eᗮ (C - D))) :=
begin
  rcases multiset.le_iff_exists_add.mp hDC with ⟨CsubD, rfl⟩,
  simp only [add_tsub_cancel_left],

  apply iff.intro,
  begin
    intro hsc,
    apply and.intro,
    exact subcollection_semicritical hDC hsc,
    simp only [project_collection],

    change semicritical (project_collection Eᗮ CsubD),
    exact z (zz hsc hE hdim),
  end,
  begin
    rintro ⟨Dsc, Psc⟩,
    rintro F Fsub,
    rcases multiset_split_le Fsub with ⟨G, H, hG, hH, rfl⟩,
    have hGE : diff G.sum ≤ E := begin
      refine le_trans _ hE,
      refine diff_multiset_sum_mono hG _,
      refine nonempty_of_semicritical Dsc,
    end,
    have hne : ∀ x ∈ H + G, set.nonempty x := by admit,
    have sf3 := subcritical_factorization_3 hGE hne,
    rw [add_comm],
    
    calc common_dimension (H + G)
       ≥ common_dimension G + common_dimension (project_collection Eᗮ H) : sf3
  ...  ≥ multiset.card G + multiset.card (project_collection Eᗮ H) : by
            {
              exact add_le_add
                (Dsc G hG)
                (Psc (project_collection Eᗮ H)
                     (multiset.map_le_map hH)),
            }
  ...  = multiset.card (H + G) : by
            {
              simp only [project_collection, multiset.card_add, multiset.card_map],
              rw [add_comm],
            },
  end
end

def semicritical_spaces (C : multiset (submodule ℝ V)) :=
  ∀ τ, τ ≤ C → dim τ.sum ≥ τ.card

def subcritical_spaces (C : multiset (submodule ℝ V)) :=
  C.card > 0 ∧ ∃ τ, τ ≤ C ∧ dim τ.sum ≤ τ.card

lemma nonempty_of_subcritical_spaces {C : multiset (submodule ℝ V)}
(h : subcritical_spaces C):
C.card > 0 := h.1

lemma semicritical_switching
(C : multiset (submodule ℝ V × submodule ℝ V))
(E : submodule ℝ V)
(C1sc : semicritical_spaces (C.map prod.fst))
(hE : dim E = C.card)
(hCE : multiset_all (λ x : submodule ℝ V × submodule ℝ V, x.fst ≤ E ∧ x.snd ≤ E) C)
(hne : ∀ x : submodule ℝ V × submodule ℝ V, x ∈ C → prod.snd x ≠ 0):
∃ A B : multiset (submodule ℝ V × submodule ℝ V), A ≤ B ∧ B ≤ C ∧
semicritical_spaces ((B.map prod.snd) + ((C - B).map prod.fst)) ∧
dim (A.map prod.snd).sum = A.card ∧
A.card > 0 := sorry

lemma semicritical_of_le
(C D : multiset (submodule ℝ V))
(h : C ≤ D)
(hsc : semicritical_spaces D) :
semicritical_spaces C := sorry
