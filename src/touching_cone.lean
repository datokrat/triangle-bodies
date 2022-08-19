import convex linalg polytope relint
  linear_algebra.affine_space.affine_subspace

open_locale pointwise
open_locale topological_space

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def outer_normal_cone (A : set V) (S : set V) : set V :=
{ u : V | S ⊆ normal_face A u }

lemma outer_normal_cone_convex (A : set V) (S : set V) :
convex ℝ (outer_normal_cone A S) :=
begin
  rintro u v hu hv,
  rintro a b ha hb -,
  simp only [outer_normal_cone, set.mem_set_of, subset_normal_face] at *,
  split,
  {tauto},
  rintro s hs y hy,
  simp only [inner_add_right, inner_smul_right],
  replace hu := hu.2 s hs y hy,
  replace hv := hv.2 s hs y hy,
  apply_rules [add_le_add,
    mul_le_mul_of_nonneg_left hu ha,
    mul_le_mul_of_nonneg_left hv hb],
end

def pre_touching_cone (A : set V) (u : V) : set V :=
outer_normal_cone A (normal_face A u)

lemma self_mem_pre_touching_cone (A : set V) (u : V) :
u ∈ pre_touching_cone A u :=
begin
  simp only [pre_touching_cone, outer_normal_cone, set_of, has_mem.mem],
end

def touching_cone (A : set V) (u : V) : set V :=
smallest_face_containing_point
  (outer_normal_cone_convex _ _ : convex ℝ (pre_touching_cone A u))
  (self_mem_pre_touching_cone A u)

lemma touching_cone_face (A : set V) (u : V) :
is_face (pre_touching_cone A u) (touching_cone A u) :=
(smallest_face_containing_point
  (outer_normal_cone_convex _ _ : convex ℝ (pre_touching_cone A u))
  (self_mem_pre_touching_cone A u)).2

lemma self_mem_relint_touching_cone (A : set V) (u : V) :
u ∈ relint (touching_cone A u) :=
begin
  apply point_in_relint_face,
end

lemma touching_cone_unique_face (A : set V) (u : V)
(F : set V) :
is_face (pre_touching_cone A u) F → u ∈ relint F →
F = touching_cone A u :=
begin
  intros hf hu,
  apply surrounding_relint_face_unique,
  {simp only [set.singleton_nonempty]},
  {assumption},
  {simp only [hu, set.singleton_subset_iff]},
end

lemma outer_normal_cone_Inter (A : set V) (S : set V) :
outer_normal_cone A S = ⋂ s ∈ S, outer_normal_cone A {s} :=
begin
  ext,
  simp only [outer_normal_cone, set.mem_set_of_eq, set.singleton_subset_iff, set.mem_Inter],
  tauto,
end

lemma outer_normal_cone_singleton_Inter₁ (A : set V) {s : V} (sA : s ∈ A) :
outer_normal_cone A {s} = ⋂ y ∈ A, { u : V | ⟪y, u⟫_ℝ ≤ ⟪s, u⟫_ℝ } :=
begin
  ext,
  simp only [outer_normal_cone, normal_face, ge_iff_le, set.singleton_subset_iff, set.mem_set_of_eq, set.mem_Inter,
  and_iff_right_iff_imp],
  tauto,
end

lemma outer_normal_cone_singleton_Inter₂ (A : set V) {s : V} (sA : s ∉ A) :
outer_normal_cone A {s} = ∅ :=
begin
  ext,
  simp only [outer_normal_cone, normal_face, set.singleton_subset_iff, set.mem_set_of_eq, set.mem_empty_eq, iff_false, not_and,
  not_forall, not_le, exists_prop],
  intro h,
  contradiction,
end

lemma outer_normal_cone_singleton_closed (A : set V) (s : V) :
is_closed (outer_normal_cone A {s}) :=
begin
  by_cases h : s ∈ A,
  {
    rw [outer_normal_cone_singleton_Inter₁ A h],
    apply is_closed_Inter,
    intro y,
    apply is_closed_Inter,
    intro hy,
    let f : V → V × V := λ v, (s - y, v),
    let g : V × V → ℝ := λ x, ⟪x.fst, x.snd⟫_ℝ,
    let h := g ∘ f,
    let M := h ⁻¹' set.Ici 0,
    suffices hh : is_closed M,
    {
      convert hh,
      funext,
      simp only [inner_sub_left, sub_nonneg, set.mem_Ici, g, h, function.comp_app],
    },
    {
      have : continuous f := by continuity,
      have : continuous g := continuous_inner,
      have : continuous h := by continuity,
      rw [continuous_iff_is_closed] at this,
      refine this _ is_closed_Ici,
    },
  },
  {
    rw [outer_normal_cone_singleton_Inter₂ A h],
    exact is_closed_empty,
  },
end

lemma outer_normal_cone_closed (A : set V) (S : set V) :
is_closed (outer_normal_cone A S) :=
begin
  rw [outer_normal_cone_Inter],
  apply is_closed_Inter,
  intro y,
  apply is_closed_Inter,
  intro hy,
  exact outer_normal_cone_singleton_closed A y,
end

lemma pre_touching_cone_closed (A : set V) (u : V) : is_closed $ pre_touching_cone A u :=
outer_normal_cone_closed _ _

lemma pre_touching_cone_convex (A : set V) (u : V) : convex ℝ $ pre_touching_cone A u :=
outer_normal_cone_convex _ _

lemma touching_cone_closed (A : set V) (u : V) : is_closed $ touching_cone A u :=
begin
  exact face_closed (pre_touching_cone_closed _ _) (touching_cone_face _ _),
end


lemma segment_image_flat (E : submodule ℝ V) (x y : E) :
(coe : E → V) '' (segment ℝ x y) = segment ℝ ↑x ↑y :=
begin
  exact segment_image ℝ E.subtype x y,
end

lemma open_segment_image_flat (E : submodule ℝ V) (x y : E) :
(coe : E → V) '' (open_segment ℝ x y) = open_segment ℝ ↑x ↑y :=
begin
  exact open_segment_image ℝ E.subtype x y,
end

lemma open_segment_preimage_flat (E : submodule ℝ V) (x y : E) :
open_segment ℝ x y = (coe : E → V) ⁻¹' (open_segment ℝ ↑x ↑y) :=
begin
  rw [←open_segment_image_flat E x y,
      set.preimage_image_eq _ subtype.coe_injective],
end

lemma convex_flat_inter {A : set V} (Acv : convex ℝ A) (E : submodule ℝ V) :
convex ℝ (coe ⁻¹' A : set E) :=
begin
  refine convex_iff_segment_subset.mpr _,
  rintro x y xA yA s hs,
  simp only [set.mem_preimage] at *,
  refine convex_iff_segment_subset.mp Acv xA yA _,
  rw [←segment_image_flat E x y],
  exact set.mem_image_of_mem coe hs,
end

lemma face_flat_inter {A F: set V}
(Acv : convex ℝ A) (hF : is_face A F) (E : submodule ℝ V) :
@is_face E _ _ (coe ⁻¹' A) (coe ⁻¹' F) :=
begin
  simp only [is_face],
  refine ⟨_, _, _⟩,
  {
    rintro ⟨x, xE⟩ x_in_preimage,
    simp only [set.preimage, set_of, has_mem.mem] at *,
    exact face_subset hF x_in_preimage,
  },
  {
    apply convex_flat_inter (face_convex hF) E,
  },
  {
    rintro x xA y yA ⟨z, hzs, hz⟩,
    rw [set.image_subset_iff.symm, segment_image_flat],
    rw [set.mem_preimage] at *,
    rw [open_segment_preimage_flat] at hzs,
    refine face_absorbs_segments hF _ _ _ _ ⟨↑z, hzs, _⟩,
    all_goals {assumption},
  },
end

lemma inner_eq_orthogonal_projection {u : V} (E : submodule ℝ V)
(uE : u ∈ E) :
∀ x : V, inner x u = @inner ℝ E _ (proj E x) ⟨u, uE⟩ :=
begin
  intro x,
  rw [proj],
  have := orthogonal_projection_inner_eq_zero x u uE,
  simpa only [inner_sub_left, sub_eq_zero] using this,
end

lemma inner_eq_orthogonal_projection' (E : submodule ℝ V)
(u : E) :
∀ x : V, inner x ↑u = @inner ℝ E _ (proj E x) u :=
begin
  rcases u with ⟨v, hv⟩,
  simp only [submodule.coe_mk, submodule.coe_inner],
  exact inner_eq_orthogonal_projection E hv,
end

lemma normal_face_orthogonal_projection {A : set V} {u : V}
(E : submodule ℝ V) (uE : u ∈ E) :
normal_face (proj E '' A) ⟨u, uE⟩ = proj E '' normal_face A u :=
begin
  apply le_antisymm,
  {
    rintro x hx,
    rw [set.mem_image],
    simp only [normal_face, set.mem_set_of] at *,
    simp only [set.mem_image] at hx,
    rcases hx with ⟨⟨v, vA, rfl⟩, hn⟩,
    refine ⟨v, _⟩,
    repeat {split},
    assumption,
    intros y yA,
    have := hn (proj E y) ⟨y, yA, rfl⟩,
    simpa only [inner_eq_orthogonal_projection E uE] using this,
  },
  {
    rintro x hx,
    simp only [normal_face, set.mem_set_of, set.mem_image] at *,
    rcases hx with ⟨y, ⟨yA, hy⟩, rfl⟩,
    refine ⟨⟨y, _⟩, _⟩,
    {tauto},
    rintro e ⟨v, ⟨vA, rfl⟩⟩,
    simp only [inner_eq_orthogonal_projection E uE] at hy,
    tauto,
  }
end

lemma outer_normal_cone_orthogonal_projection {A : set V} {S : set V}
(SA : S ⊆ A)  (E : submodule ℝ V):
(coe : E → V) ⁻¹' (outer_normal_cone A S) =
outer_normal_cone (proj E '' A) (proj E '' S) :=
begin
  simp only [submodule.coe_subtype,
    outer_normal_cone] at *,
  apply le_antisymm,
  {
    rintro u hu,
    simp only [set.mem_preimage, set.mem_set_of, subset_normal_face] at hu,
    simp only [set.mem_image, set.mem_set_of, subset_normal_face],
    split,
    {refine set.image_subset _ hu.1},
    {
      rintro - ⟨vs, hvs, rfl⟩ - ⟨a, ha, rfl⟩,
      rcases hu with ⟨-, hu⟩,
      repeat {rw [←inner_eq_orthogonal_projection']},
      apply hu,
      all_goals{assumption},
    },
  },
  {
    rintro h hu,
    simp only [set.mem_set_of, subset_normal_face] at hu,
    simp only [set.mem_preimage, set.mem_set_of, subset_normal_face],
    split,
    {assumption},
    rintro s hs y hy,
    rcases hu with ⟨-, hu⟩,
    repeat {rw [inner_eq_orthogonal_projection' E]},
    refine hu (proj E s) _ (proj E y) _,
    all_goals {
      apply set.mem_image_of_mem,
      assumption,
    },
  },
end

lemma pre_touching_cone_orthogonal_projection {A : set V} {u : V}
(E : submodule ℝ V) (uE : u ∈ E) :
pre_touching_cone (proj E '' A) ⟨u, uE⟩ = coe ⁻¹' (pre_touching_cone A u) :=
begin
  simp only [pre_touching_cone],
  rw [outer_normal_cone_orthogonal_projection],
  {
    congr,
    refine normal_face_orthogonal_projection _ _,
  },
  {
    apply normal_face_subset,
  },
end

lemma touching_cone_orthogonal_projection {E : submodule ℝ V}
(A : set V) {u : V} (uE : u ∈ E) :
touching_cone (proj E '' A) ⟨u, uE⟩ = coe ⁻¹' (touching_cone A u) :=
begin
  symmetry,
  apply touching_cone_unique_face,
  {
    simp only [pre_touching_cone_orthogonal_projection],
    refine face_flat_inter _ _ E,
    {apply pre_touching_cone_convex},
    {apply touching_cone_face},
  },
  {
    apply relint_inter_flat,
    apply self_mem_relint_touching_cone,
  },
end

-- touching space
noncomputable def TS (A : set V) (u : V) : submodule ℝ V :=
(submodule.span ℝ (touching_cone A u))ᗮ

lemma TS_orthogonal_projection {E : submodule ℝ V}
(A : set V) {u : V} (uE : u ∈ E) :
(TS A u).map (proj E) = TS ((proj E) '' A) ⟨u, uE⟩ :=
begin
  simp only [TS, touching_cone_orthogonal_projection],
  have hu : u ∈ (relint (touching_cone A u)) ∩ E,
  {
    exact ⟨self_mem_relint_touching_cone _ _, uE⟩,
  },
  simp only [←submodule.coe_subtype, span_inter hu, map_proj_orthogonal],
end

lemma TS_le_uperp (A : set V) (u : V) :
TS A u ≤ vector_orth u :=
begin
  simp only [TS, vector_orth],
  apply submodule.orthogonal_le,
  rw [submodule.span_singleton_le_iff_mem],
  apply submodule.subset_span,
  exact relint_subset_self _ (self_mem_relint_touching_cone _ _),
end

lemma touching_cone_subset_pre (A : set V) (u : V) :
touching_cone A u ⊆ pre_touching_cone A u :=
begin
  simp only [touching_cone],
  exact face_subset' _,
end

lemma outer_normal_cone_orthogonal (A : set V) (S : set V) :
vector_span ℝ S ≤ (submodule.span ℝ (outer_normal_cone A S))ᗮ :=
begin
  intros y hy,
  simp only [set_like.mem_coe, mem_orthogonal_span],
  intros u hu,
  simp only [outer_normal_cone, set.mem_set_of] at hu,
  replace hy := vector_span_mono ℝ hu hy,
  revert y,
  simpa only [submodule.mem_orthogonal'] using mem_vspan_normal_face A u,
end
