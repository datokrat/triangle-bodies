import convex linalg

open_locale pointwise

variables {V : Type} [inner_product_space ℝ V]
[finite_dimensional ℝ V]

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

-- linalg
lemma aspan_le_span (A : set V) :
affine_span ℝ A ≤ (submodule.span ℝ A).to_affine_subspace :=
begin
  rw [affine_span_le],
  apply submodule.subset_span,
end

lemma span_eq_hom_aspan {A : set V} :
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
    rcases hx with ⟨a, x', hx', rfl⟩,
    {
      -- replace hx' := this hx',
      simp only [set_like.mem_coe],
      apply submodule.smul_mem _ _ _,
      exact aspan_le_span _ hx',
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