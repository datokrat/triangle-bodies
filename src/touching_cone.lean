import convex linalg
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


lemma relint_subset_self (A : set V) :
relint A ⊆ A :=
begin
  simp only [relint],
  intros x hx,
  simp only [set.mem_image] at hx,
  rcases hx with ⟨y, hy, rfl⟩,
  replace hy := interior_subset hy,
  exact hy,
end

lemma coe_ball_submodule {E : submodule ℝ V} (u : E) (ε : ℝ) :
coe '' metric.ball u ε = metric.ball (u : V) ε ∩ E :=
begin
  ext,
  simp only [set.mem_image, metric.mem_ball, set.mem_inter_iff],
  split,
  {
    rintro ⟨e, he, rfl⟩,
    refine ⟨_, e.property⟩,
    simpa only [subtype.dist_eq] using he,
  },
  {
    rintro ⟨h, xE⟩,
    refine ⟨⟨x, xE⟩, _, rfl⟩,
    {
      simpa only [subtype.dist_eq, subtype.coe_mk] using h,
    },
  },
end

lemma coe_ball_affine {E : affine_subspace ℝ V} (u : E) (ε : ℝ) :
coe '' metric.ball u ε = metric.ball (u : V) ε ∩ E :=
begin
  ext,
  simp only [set.mem_image, metric.mem_ball, set.mem_inter_iff],
  split,
  {
    rintro ⟨e, he, rfl⟩,
    refine ⟨_, e.property⟩,
    simpa only [subtype.dist_eq] using he,
  },
  {
    rintro ⟨h, xE⟩,
    refine ⟨⟨x, xE⟩, _, rfl⟩,
    {
      simpa only [subtype.dist_eq, subtype.coe_mk] using h,
    },
  },
end

lemma mem_relint (A : set V) (u : V) :
-- WRONG!
u ∈ relint A ↔ u ∈ span_points ℝ A ∧ ∃ ε : ℝ, ε > 0 ∧ metric.ball u ε ∩ span_points ℝ A ⊆ A :=
begin
  split,
  {
    intro hu,
    refine ⟨mem_span_points _ _ _ (relint_subset_self _ hu), _⟩,
    simp only [relint] at hu,
    rcases hu with ⟨pu, hpu, rfl⟩,
    have : is_open (interior (coe ⁻¹' A)) := is_open_interior,
    rw [metric.is_open_iff] at this,
    replace this := this _ hpu,
    rcases this with ⟨ε, hε, εball⟩,
    refine ⟨ε, hε, _⟩,
    replace εball := subset_trans εball interior_subset,
    rintro x ⟨xball, xA⟩,
    rw [←set.image_subset_iff] at εball,
    refine εball _,
    simp only [set.mem_image],
    refine ⟨⟨x, xA⟩, _, rfl⟩,
    {
      --simp only [metric.mem_ball] at xball,
      simp only [metric.mem_ball] at xball ⊢,
      simp only [subtype.dist_eq],
      exact xball,
    },
  },
  {
    intro h,
    rcases h with ⟨usp, ε, εpos, εball⟩,
    simp only [relint, set.mem_image],
    refine ⟨⟨u, usp⟩, _, rfl⟩,
    {
      simp only [mem_interior],
      refine ⟨metric.ball ⟨u, usp⟩ ε, _, _, _⟩,
      {
        simp only [←set.image_subset_iff, coe_ball_affine, subtype.coe_mk, coe_affine_span],
        exact εball,
      },
      {
        exact metric.is_open_ball,
      },
      {
        exact metric.mem_ball_self εpos,
      },
    },
  },
end

lemma relint_mem_between {A : set V} {u x: V}
(uA : u ∈ relint A) (xA : x ∈ span_points ℝ A) (ne : u ≠ x) :
∃ y ∈ open_segment ℝ u x, y ∈ A :=
begin
  let v := x - u,
  let f : ℝ → V := λ δ, δ • v + u,
  have fcont : continuous f := by continuity,
  let uA := uA,
  rw [mem_relint] at uA,
  rcases uA with ⟨usp, ε, εpos, εball⟩,
  let U := f ⁻¹' metric.ball u ε,
  have Uo : is_open U := is_open.preimage fcont metric.is_open_ball,
  rw [metric.is_open_iff] at Uo,
  have Uo0 : (0 : ℝ) ∈ U,
  {
    simp only [set.mem_preimage, f, metric.mem_ball, zero_smul, zero_add, dist_self],
    exact εpos,
  },
  rcases Uo 0 Uo0 with ⟨δ', δpos', hδ'⟩,
  let δ := min δ' 1,
  have δpos : δ > 0,
  {
    simp only [gt_iff_lt, lt_min_iff, zero_lt_one, and_true],
    exact δpos',
  },
  have hδ : metric.ball 0 δ ⊆ U,
  {
    refine subset_trans _ hδ',
    apply metric.ball_subset_ball,
    simp only [min_le_iff, le_refl, true_or],
  },
  have δlt : δ / 2 < 1,
  {
    simp only [δ, div_lt_iff (show 0 < (2 : ℝ), by linarith)],
    simp only [one_mul, min_lt_iff],
    right,
    linarith,
  },
  let x' := (δ / 2) • v + u,
  refine ⟨x', _, _⟩,
  {
    simp only [open_segment, set.mem_set_of],
    refine ⟨1 - δ / 2, δ / 2, _, _, _, _⟩,
    {
      simp only [sub_pos],
      exact δlt,
    },
    {
      exact half_pos δpos,
    },
    {
      ring,
    },
    {
      simp only [x', sub_smul, one_smul, smul_sub],
      abel,
    },
  },
  {
    apply εball,
    split,
    {
      have : δ / 2 ∈ U,
      {
        apply hδ,
        simp only [metric.mem_ball, dist_eq_norm, tsub_zero, real.norm_eq_abs,
          abs_eq_self.mpr (le_of_lt (half_pos δpos))],
        exact half_lt_self δpos,
      },
      exact this,
    },
    {
      simp only [x', v],
      refine vadd_mem_span_points_of_mem_span_points_of_mem_vector_span ℝ _ _,
      {
        exact usp,
      },
      {
        refine submodule.smul_mem _ _ _,
        refine vsub_mem_vector_span_of_mem_span_points_of_mem_span_points ℝ _ _,
        {exact xA},
        {exact usp},
      },
    },
  },
end

lemma affine_span_inter' {A : set V} {E : submodule ℝ V} {u : V}
(uA : u ∈ relint A) (uE : u ∈ E) :
span_points ℝ A ∩ (E : set V) ⊆ span_points ℝ (A ∩ E) :=
begin
  rintro x ⟨hx₁, hx₂⟩,
  let uA := uA,
  rw [mem_relint] at uA,
  rcases uA with ⟨umem, ε, εpos, εball⟩,
  have umem' : u ∈ span_points ℝ A,
  {
    apply mem_span_points,
    exact relint_subset_self _ uA,
  },
  have umem : u ∈ span_points ℝ (A ∩ E),
  {
    apply mem_span_points,
    exact ⟨relint_subset_self _ uA, uE⟩,
  },
  let v := x - u,
  have vmem : v ∈ vector_span ℝ (A ∩ E),
  {
    have vmem' : v ∈ vector_span ℝ A :=
      vsub_mem_vector_span_of_mem_span_points_of_mem_span_points ℝ
      hx₁ umem',
    have : ∀ δ : ℝ, δ • v + u ∈ span_points ℝ A,
    {
      intro δ,
      have : δ • v ∈ vector_span ℝ A := submodule.smul_mem _ δ vmem',
      exact vadd_mem_span_points_of_mem_span_points_of_mem_vector_span ℝ
        umem' this,
    },
    let f : ℝ → V := λ δ, δ • v + u,
    have fcont : continuous f := by continuity,
    let U := f ⁻¹' metric.ball u ε,
    have Uo : is_open U := is_open.preimage fcont metric.is_open_ball,
    rw [metric.is_open_iff] at Uo,
    have Uo0 : (0 : ℝ) ∈ U,
    {
      simp only [set.mem_preimage, f, metric.mem_ball, zero_smul, zero_add, dist_self],
      exact εpos,
    },
    rcases Uo 0 Uo0 with ⟨δ, δpos, hδ⟩,
    let x' := (δ / 2) • v + u,
    have x'A : x' ∈ A ∩ E,
    {
      split, rotate,
      {
        simp only [x', set_like.mem_coe],
        apply E.add_mem (E.smul_mem _
          (E.sub_mem hx₂ uE)) uE,
      },
      apply εball,
      split,
      {
        have : δ / 2 ∈ U,
        {
          apply hδ,
          simp only [metric.mem_ball, dist_eq_norm, tsub_zero, real.norm_eq_abs,
            abs_eq_self.mpr (le_of_lt (half_pos δpos))],
          exact half_lt_self δpos,
        },
        exact this,
      },
      {
        exact this (δ / 2),
      },
    },
    let v' := (δ / 2) • v,
    have v'mem : v' ∈ vector_span ℝ (A ∩ E),
    {
      simpa only [vsub_eq_sub, add_sub_cancel] using vsub_mem_vector_span_of_mem_span_points_of_mem_span_points ℝ
        (mem_span_points ℝ x' (A ∩ ↑E) x'A) umem,
    },
    suffices h : (δ / 2)⁻¹ • (δ / 2) • v ∈ vector_span ℝ (A ∩ E),
    {
      simp only [inv_smul_smul₀ (ne_of_gt (half_pos δpos))] at h,
      exact h,
    },
    exact submodule.smul_mem _ (δ / 2)⁻¹ v'mem,
  },
  suffices h : v + u ∈ span_points ℝ (A ∩ E),
  {
    simpa only [sub_add_cancel] using h,
  },
  exact vadd_mem_span_points_of_mem_span_points_of_mem_vector_span
    ℝ umem vmem,
end

/- lemma affine_span_inter {A : set V} {E : submodule ℝ V} {u : V}
(h : u ∈ (relint A) ∩ E) :
affine_span ℝ (E.subtype ⁻¹' A) = (affine_span ℝ A).comap E.subtype.to_affine_map :=
begin
  apply le_antisymm,
  {
    admit,
  },
  {
    rw [set.mem_inter_iff] at h,
    have := affine_span_inter' h.1 h.2,
    intros x hx,
    simp only [affine_subspace.coe_comap, linear_map.coe_to_affine_map, submodule.coe_subtype, coe_affine_span, set.mem_preimage] at hx,
    have xmem : ↑x ∈ span_points ℝ (A ∩ E),
    {
      apply this,
      split,
      {exact hx},
      {exact x.property},
    },
    simp only [submodule.coe_subtype, coe_affine_span],
    admit,
  }
end -/

lemma line_subset_aspan {A : set V} {x y : V}
(xA : x ∈ span_points ℝ A) (yA : y ∈ span_points ℝ A) {c d : ℝ} (h : c + d = 1) :
c • x + d • y ∈ span_points ℝ A :=
begin
  suffices hs : c • (x - y) + (c + d) • y ∈ span_points ℝ A,
  {
    simp only [smul_sub, add_smul] at hs,
    simp only [←add_assoc, add_sub_right_comm, sub_add_cancel] at hs,
    exact hs,
  },
  {
    apply vadd_mem_span_points_of_mem_span_points_of_mem_vector_span ℝ,
    {
      rw [h, one_smul],
      exact yA,
    },
    {
      refine submodule.smul_mem _ _ _,
      apply vsub_mem_vector_span_of_mem_span_points_of_mem_span_points ℝ,
      all_goals {assumption},
    }
  },
end


lemma span_eq_hom_aspan {A : set V} :
-- WRONG!
↑(submodule.span ℝ A) =
{ x : V | (∃ (a : ℝ) (y ∈ span_points ℝ A), x = a • y)
∨ x ∈ vector_span ℝ A} :=
begin
  apply subset_antisymm,
  {
    intros x hx,
    refine submodule.span_induction hx _ _ _ _,
    {
      intros y yA,
      left,
      refine ⟨1, y, (mem_span_points _ _ _ yA), (one_smul _ _).symm⟩,
    },
    {
      right,
      exact submodule.zero_mem _,
    },
    {
      simp only [set.mem_set_of],
      intros y z hy hz,
      rcases hy with ⟨cy, y', ysp, rfl⟩,
      {
        rcases hz with ⟨cz, z', zsp, rfl⟩,
        {
          by_cases hc : cy + cz = 0,
          {
            right,
            simp only [add_eq_zero_iff_eq_neg] at hc,
            rw [hc, neg_smul, add_comm, ←sub_eq_add_neg, ←smul_sub],
            refine submodule.smul_mem _ _ _,
            apply vsub_mem_vector_span_of_mem_span_points_of_mem_span_points ℝ,
            all_goals {assumption},
          },
          {
            left,
            let c := cy + cz,
            refine ⟨c, c⁻¹ • (cy • y' + cz • z'), _, _⟩,
            {
              simp only [smul_add, ←mul_smul],
              apply line_subset_aspan,
              any_goals {assumption},
              simp only [c, ←mul_add, inv_mul_eq_one₀ hc],
            },
            {
              simp only [smul_inv_smul₀ hc],
            },
          },
        },
        {
          by_cases hc : cy = 0,
          {
            right,
            simp only [hc, zero_smul, zero_add],
            assumption,
          },
          {
            left,
            refine ⟨cy, y' + cy⁻¹ • z, _, _⟩,
            {
              rw [add_comm],
              apply vadd_mem_span_points_of_mem_span_points_of_mem_vector_span ℝ,
              {assumption},
              {
                refine submodule.smul_mem _ _ _,
                assumption,
              },
            },
            {
              rw [smul_add, smul_inv_smul₀ hc],
            },
          },
        },
      },
      {
        rcases hz with ⟨cz, z', zsp, rfl⟩,
        {
          by_cases hc : cz = 0,
          {
            right,
            simp only [hc, zero_smul, add_zero],
            assumption,
          },
          {
            left,
            refine ⟨cz, cz⁻¹ • y + z', _, _⟩,
            {
              apply vadd_mem_span_points_of_mem_span_points_of_mem_vector_span ℝ,
              {assumption},
              {
                refine submodule.smul_mem _ _ _,
                assumption,
              },
            },
            {
              rw [smul_add, smul_inv_smul₀ hc],
            },
          },
        },
        {
          right,
          refine submodule.add_mem _ _ _,
          all_goals {assumption},
        },
      },
    },
    {
      intros a y hy,
      rcases hy with ⟨cy, y', hy, rfl⟩,
      {
        left,
        simp only [smul_smul],
        tauto,
      },
      {
        right,
        refine submodule.smul_mem _ _ _,
        assumption,
      },
    },
  },
  {
    intros x hx,
    have : affine_span ℝ A ≤ (submodule.span ℝ A).to_affine_subspace,
    {
      rw [affine_span_le],
      apply submodule.subset_span,
    },
    rcases hx with ⟨a, x', hx', rfl⟩,
    {
      -- replace hx' := this hx',
      simp only [set_like.mem_coe],
      apply submodule.smul_mem _ _ _,
      exact this hx',
    },
    {
      have : vector_span ℝ A ≤ submodule.span ℝ A,
      {
        simp only [vector_span, submodule.span_le],
        rintro - ⟨a, b, ha, hb, rfl⟩,
        rw [vsub_eq_sub, set_like.mem_coe],
        apply submodule.sub_mem _ _ _,
        all_goals {
          apply submodule.subset_span,
          assumption,
        },
      },
      exact this hx,
    },
  },
end

lemma aspan_inter_eq_aspan_preimage (A : set V) (E : submodule ℝ V) :
span_points ℝ (A ∩ E) = coe '' span_points ℝ (E.subtype ⁻¹' A) :=
begin
  suffices h : affine_span ℝ (A ∩ E) = affine_subspace.map E.subtype.to_affine_map (affine_span ℝ (E.subtype ⁻¹' A)),
  {
    ext, split,
    {
      intro hx,
      change x ∈ affine_span ℝ (A ∩ E) at hx,
      rw [h] at hx,
      exact hx,
    },
    {
      intro hx,
      change x ∈ (affine_span ℝ (E.subtype ⁻¹' A)).map E.subtype.to_affine_map at hx,
      rw [←h] at hx,
      exact hx,
    },
  },
  apply le_antisymm,
  {
    apply affine_span_le.mpr,
    rintro x ⟨xA, xE⟩,
    simp only [submodule.coe_subtype, affine_subspace.coe_map, linear_map.coe_to_affine_map, set.mem_image, coe_affine_span],
    refine ⟨⟨x, xE⟩, _, _⟩,
    {
      apply mem_span_points ℝ,
      simp only [set.mem_preimage, submodule.coe_mk],
      exact xA,
    },
    {
      simp only [submodule.coe_mk],
    },
  },
  {
    rw [affine_subspace.map_span, affine_span_le],
    simp only [linear_map.coe_to_affine_map, submodule.coe_subtype, coe_affine_span, set.image_subset_iff],
    intros x hx,
    simp only [set.mem_preimage] at hx ⊢,
    apply mem_span_points ℝ,
    exact ⟨hx, x.property⟩,
  },
end

lemma vspan_inter {A : set V} {E : submodule ℝ V} {u : V}
(h : u ∈ (relint A) ∩ E) :
vector_span ℝ (E.subtype ⁻¹' A) = (vector_span ℝ A).comap E.subtype :=
begin
  apply le_antisymm,
  {
    simp only [vector_span, submodule.span_le],
    rintro - ⟨a, b, ha, hb, rfl⟩,
    simp only [vsub_eq_sub, submodule.comap_coe, submodule.coe_subtype, set.mem_preimage, add_subgroup_class.coe_sub,
    set_like.mem_coe],
    apply submodule.subset_span _,
    refine ⟨a, b, ha, hb, rfl⟩,
  },
  {
    intros x hx,
    simp only [submodule.mem_comap, submodule.coe_subtype] at hx,
    let y := ↑x + u,
    have usp' : u ∈ span_points ℝ A,
    {
      apply mem_span_points,
      exact relint_subset_self _ h.1,
    },
    have usp : u ∈ span_points ℝ (A ∩ E),
    {
      apply affine_span_inter' h.1 h.2 _,
      exact ⟨usp', h.2⟩,
    },
    have ysp : y ∈ span_points ℝ A,
    {
      apply vadd_mem_span_points_of_mem_span_points_of_mem_vector_span ℝ,
      {
        exact usp',
      },
      {
        exact hx,
      },
    },
    by_cases hc : x = 0,
    {
      rw [hc],
      exact submodule.zero_mem _,
    },
    have huy : u ≠ y,
    {
      simp only [ne.def, self_eq_add_left, submodule.coe_eq_zero],
      exact hc,
    },  
    have := relint_mem_between h.1 ysp huy,
    rcases this with ⟨z, hz₁, hz₂⟩,
    simp only [open_segment, set.mem_set_of] at hz₁,
    rcases hz₁ with ⟨a, b, ha, hb, hab, rfl⟩,
    simp only [y] at hz₂,
    rw [smul_add, add_comm, add_assoc, ←add_smul] at hz₂,
    rw [add_comm] at hab,
    rw [hab, one_smul] at hz₂,
    suffices hs : (b • x + ⟨u, h.2⟩) - ⟨u, h.2⟩ ∈ vector_span ℝ (E.subtype ⁻¹' A),
    {
      simp only [add_sub_cancel, submodule.coe_subtype] at hs,
      convert submodule.smul_mem _ b⁻¹ hs,
      rw [inv_smul_smul₀ (ne_of_gt hb)],
    },
    apply vsub_mem_vector_span_of_mem_span_points_of_mem_span_points ℝ,
    {
      apply mem_span_points,
      simp only [set.mem_preimage, submodule.coe_subtype, submodule.coe_add, submodule.coe_smul_of_tower, submodule.coe_mk],
      exact hz₂,
    },
    {
      apply mem_span_points,
      simp only [set.mem_preimage, submodule.coe_subtype, submodule.coe_add, submodule.coe_smul_of_tower, submodule.coe_mk],
      exact relint_subset_self _ h.1,
    },
  }
end

lemma span_inter {A : set V} {E : submodule ℝ V} {u : V}
(h : u ∈ (relint A) ∩ E) :
submodule.span ℝ (E.subtype ⁻¹' A) = (submodule.span ℝ A).comap E.subtype :=
begin
  apply le_antisymm,
  { -- easy direction
    rw [submodule.span_le],
    intros x hx,
    simp only [submodule.mem_comap, submodule.coe_subtype, set_like.mem_coe] at hx ⊢,
    apply submodule.subset_span,
    exact hx,
  },
  {
    intros x hx,
    simp only [submodule.mem_comap, submodule.coe_subtype] at hx,
    rw [←set_like.mem_coe, span_eq_hom_aspan, set.mem_set_of] at hx ⊢,
    rcases hx with ⟨a, y, ha, hxy⟩,
    {
      by_cases hc : a = 0,
      {
        rw [set.mem_inter_iff] at h,
        left,
        refine ⟨0, ⟨u, _⟩, _⟩,
        {
          exact h.2,
        },
        simp only [hc, zero_smul, submodule.coe_eq_zero] at hxy,
        rw [hxy],
        simp only [submodule.coe_subtype, zero_smul, eq_self_iff_true, exists_prop, and_true],
        apply mem_span_points ℝ,
        simp only [set.mem_preimage, submodule.coe_mk],
        exact relint_subset_self _ h.1,
      },
      left,
      refine ⟨a, ⟨y, _⟩, _, _⟩,
      {
        convert E.smul_mem a⁻¹ x.property,
        simp only [hxy, subtype.val_eq_coe, inv_smul_smul₀ hc],
      },
      {
        suffices h : y ∈ coe '' span_points ℝ ((E.subtype) ⁻¹' A),
        {
          rw [set.mem_image] at h,
          rcases h with ⟨z, h₁, rfl⟩,
          have : z = ⟨↑z, z.property⟩ := by simp only [set_like.eta],
          rw [←set_like.eta z z.property] at h₁,
          exact h₁,
        },
        rw [←aspan_inter_eq_aspan_preimage],
        apply affine_span_inter' h.1 h.2,
        refine ⟨ha, _⟩,
        simp only [set_like.mem_coe],
        convert E.smul_mem a⁻¹ x.property,
        rw [subtype.val_eq_coe, hxy, inv_smul_smul₀ hc],
      },
      {
        apply subtype.coe_injective,
        simp only [hxy, submodule.coe_smul_of_tower, submodule.coe_mk],
      },
    },
    {
      right,
      rw [vspan_inter h, submodule.mem_comap],
      exact hx,
    },
  },
end

lemma inner_orthogonal_eq_inner (E : submodule ℝ V)
(u : E) (x : V) : ⟪((proj E) x : V), (u : V)⟫_ℝ = ⟪x, u⟫_ℝ :=
begin
  symmetry,
  apply eq_of_sub_eq_zero,
  -- simp only [submodule.coe_inner],
  rw [←inner_sub_left],
  simp only [proj, continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe, orthogonal_projection_inner_eq_zero,
  submodule.coe_mem],
end

lemma map_proj_orthogonal (E F : submodule ℝ V) :
Fᗮ.map (proj E) = (F.comap E.subtype)ᗮ :=
begin
  rw [←submodule.orthogonal_orthogonal (Fᗮ.map (proj E))],
  refine congr_arg submodule.orthogonal _,
  ext,
  simp only [submodule.mem_map, submodule.mem_comap, submodule.mem_orthogonal, submodule.coe_subtype, submodule.coe_inner],
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  split,
  {
    intros h,
    have : x.val ∈ Fᗮᗮ,
    {
      simp only [submodule.mem_orthogonal],
      intros u hu,
      have := h u hu,
      simpa only [inner_orthogonal_eq_inner] using this,
    },
    {
      simpa only [submodule.orthogonal_orthogonal] using this,
    },
  },
  {
    intros xF v hv,
    simp only [real_inner_comm] at hv,
    simpa only [inner_orthogonal_eq_inner] using hv x xF,
  },
end

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

lemma mem_orthogonal_span (A : set V) (x : V) :
x ∈ (submodule.span ℝ A)ᗮ ↔ ∀ u : V, u ∈ A → ⟪u, x⟫_ℝ = 0 :=
begin
  split,
  {
    rw [submodule.mem_orthogonal],
    intros hx u hu,
    refine hx u _,
    apply submodule.subset_span,
    exact hu,
  },
  {
    intro h,
    rw [submodule.mem_orthogonal],
    intros u hu,
    apply submodule.span_induction hu,
    {
      exact h,
    },
    {
      simp only [inner_zero_left],
    },
    {
      intros y z hy hz,
      simp only [inner_add_left, hy, hz, add_zero],
    },
    {
      intros a y hy,
      simp only [inner_smul_left, hy, mul_zero],
    },
  },
end

lemma face_subset' {A : set V} (F : faces A) :
↑F ⊆ A :=
begin
  apply face_subset,
  exact F.property,
end

lemma touching_cone_subset_pre (A : set V) (u : V) :
touching_cone A u ⊆ pre_touching_cone A u :=
begin
  simp only [touching_cone],
  exact face_subset' _,
end

lemma mem_vspan_normal_face (A : set V) (u : V) :
u ∈ (vector_span ℝ (normal_face A u))ᗮ :=
begin
  simp only [vector_span, mem_orthogonal_span],
  rintro - ⟨a, b, ha, hb, rfl⟩,
  simp only [mem_normal_face] at ha hb,
  simp only [vsub_eq_sub, inner_sub_left, sub_eq_zero],
  apply le_antisymm,
  all_goals {tauto},
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

lemma TS_poly_eq_vspan_face {P : set V} (hP : is_polytope P) (u : V) :
TS P u = vector_span ℝ (normal_face P u) :=
begin
  apply le_antisymm,
  {
    admit,
  },
  {
    refine le_trans _ (submodule.orthogonal_le (submodule.span_mono (touching_cone_subset_pre _ _))),
    simp only [TS, pre_touching_cone],
    apply outer_normal_cone_orthogonal,
  }
end