import convex linalg
  linear_algebra.affine_space.affine_subspace

open_locale pointwise

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

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
@is_face E _ (coe ⁻¹' A) (coe ⁻¹' F) :=
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

lemma normal_face_orthogonal_projection {A : set V} {u : V}
(Acv : convex ℝ A) (E : submodule ℝ V) (uE : u ∈ E) :
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

lemma pre_touching_cone_orthogonal_projection {A : set V} {u : V}
(Acv : convex ℝ A) (E : submodule ℝ V) (uE : u ∈ E) :
pre_touching_cone (proj E '' A) ⟨u, uE⟩ = coe ⁻¹' (pre_touching_cone A u) :=
begin
  admit,
end

lemma touching_cone_orthogonal_projection {A : set V} {u : V}
(Acv : convex ℝ A) (E : submodule ℝ V) (uE : u ∈ E):
touching_cone (proj E '' A) ⟨u, uE⟩ = coe ⁻¹' (touching_cone A u) :=
begin
  admit,
end