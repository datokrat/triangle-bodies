import convex touching_cone

open_locale pointwise

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma polytope_pre_touching_cone_nhd {P : set V} (hP : is_polytope P) (u : V) :
∃ ε : ℝ, ε > 0 ∧
metric.ball u ε ∩ (vector_span ℝ (normal_face P u))ᗮ ⊆ pre_touching_cone P u :=
begin
  rcases polytope_facial_gap hP u with ⟨ε, εpos, εball⟩,
  refine ⟨ε, εpos, _⟩,
  rintro z ⟨hv₁, hz⟩,
  simp only [set_like.mem_coe] at hz,
  --rcases (set.eq_of_mem_singleton hu).symm with rfl,
  simp only [pre_touching_cone, outer_normal_cone, set.mem_set_of],
  intros v hv,
  rcases polytope_normal_face_nonempty hP z with ⟨w, wua⟩,
  have wu := εball _ hv₁ wua,
  simp only [mem_normal_face],
  split,
  {
    exact normal_face_subset hv,
  },
  {
    intros y yP,
    have hu := mem_vspan_normal_face P u,
    have : ⟪v, z - u⟫_ℝ = ⟪w, z - u⟫_ℝ,
    {
      rw [←sub_eq_zero, ←inner_sub_left],
      exact (submodule.sub_mem _ hz hu) (v - w) (vsub_mem_vector_span ℝ hv wu),
    },
    have zeq: z = u + (z - u) := by simp only [add_sub_cancel'_right],
    rw [zeq],
    simp only [inner_add_right, inner_eq_of_mem_normal_face hv wu],
    simp only [this, ←inner_add_right, add_sub_cancel'_right],
    exact wua.2 y yP,
  },
end

lemma ball_spans_submodule (E : submodule ℝ V) (u : V) (uE : u ∈ E)
{ε : ℝ} (εpos : ε > 0) :
submodule.span ℝ (metric.ball u ε ∩ E) = E :=
begin
  let u' : E := ⟨u, uE⟩,
  suffices h : submodule.span ℝ (metric.ball u' ε) = ⊤,
  {
    simp only [u'] at h,
    replace h := congr_arg (submodule.map E.subtype) h,
    simp only [submodule.map_span] at h,
    simp only [submodule.coe_subtype, submodule.map_subtype_top] at h,
    simpa only [coe_ball_submodule, submodule.coe_mk] using h,
  },
  exact span_top_of_ball_subset εpos (subset_refl _),
end

lemma polytope_vspan_pre_touching_cone {P : set V} (hP : is_polytope P) (u : V) :
submodule.span ℝ (pre_touching_cone P u) =
(vector_span ℝ (normal_face P u))ᗮ :=
begin
  apply le_antisymm,
  {
    simp only [pre_touching_cone],
    rw [le_orthogonal_symm],
    apply outer_normal_cone_orthogonal,
  },
  {
    rcases polytope_pre_touching_cone_nhd hP u
      with ⟨ε, εpos, εball⟩,
    have hu : u ∈ (vector_span ℝ (normal_face P u))ᗮ :=
      by apply mem_vspan_normal_face,
    have := ball_spans_submodule _ u hu εpos,
    rw [←this, submodule.span_le],
    refine subset_trans _ submodule.subset_span,
    convert εball,
  },
end

lemma self_mem_relint_pre_touching_cone {P : set V} (hP : is_polytope P) (u : V) :
u ∈ relint (pre_touching_cone P u) :=
begin
  simp only [mem_relint],
  split,
  {
    apply mem_span_points,
    apply self_mem_pre_touching_cone,
  },
  {
    rcases polytope_pre_touching_cone_nhd hP u
      with ⟨ε, εpos, εball⟩,
    refine ⟨ε, εpos, subset_trans _ εball⟩,
    apply set.inter_subset_inter_right,
    refine subset_trans (aspan_le_span _) _,
    rw [polytope_vspan_pre_touching_cone hP],
    refine subset_of_eq _,
    refl,
  },
end

/- lemma polytope_relint_pre_touching_cone {P : set V} (hP : is_polytope P) (u : V) :
relint (pre_touching_cone P u) = { v : V | normal_face P v = normal_face P u } :=
begin
  apply subset_antisymm,
  {
    admit,
  },
  {
    admit,
  --   simp only [is_polytope] at hP,
  --   rcases hP with ⟨S, Sfin, Sne, rfl⟩,
  --   simp only [pre_touching_cone, outer_normal_cone],
  --   simp only [normal_face_spanned_by_verts],
  --   intros v hv,
  --   simp only [set.mem_set_of] at hv,
  },
end -/

lemma polytope_touching_cone_eq_pre {P : set V} (hP : is_polytope P) (u : V) :
touching_cone P u = pre_touching_cone P u :=
begin
  symmetry,
  apply touching_cone_unique_face,
  {
    apply is_face_refl,
    apply pre_touching_cone_convex,
  },
  {
    apply self_mem_relint_pre_touching_cone hP,
  },
end

lemma TS_poly_eq_vspan_face {P : set V} (hP : is_polytope P) (u : V) :
TS P u = vector_span ℝ (normal_face P u) :=
begin
  symmetry,
  simp only [TS, eq_orthogonal_symm, polytope_touching_cone_eq_pre hP],
  rw [polytope_vspan_pre_touching_cone hP u, submodule.orthogonal_orthogonal],
end