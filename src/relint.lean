import convex linalg
  analysis.normed_space.hahn_banach.separation

open_locale pointwise
open_locale topological_space

variables {V : Type} [inner_product_space ℝ V]
[finite_dimensional ℝ V]


def relint (A : set V) : set V :=
coe '' interior ((coe : affine_span ℝ A → V) ⁻¹' A)

def relbd (A : set V) : set V :=
(closure A) \ (relint A)

def is_relopen (A : set V) : Prop :=
is_open ((coe : affine_span ℝ A → V) ⁻¹' A)

theorem open_in_subspace (E : affine_subspace ℝ V) (A : set V) (h : is_open A) : is_open ((coe : E → V) ⁻¹' A) :=
begin
  let c := (coe : E → V),
  have : c = (coe : E → V) := rfl,
  let cc : continuous (coe : E → V) := continuous_subtype_coe,
  refine is_open.preimage cc h,
end

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

lemma mem_relint' (A : set V) (u : V) :
u ∈ relint A ↔ u ∈ span_points ℝ A ∧ ∃ (t : set V), t ∩ span_points ℝ A ⊆ A ∧ is_open t ∧ u ∈ t :=
begin
  rw [mem_relint], split,
  {
    rintro ⟨hu, ε, εpos, εball⟩,
    refine ⟨hu, metric.ball u ε, εball, metric.is_open_ball, metric.mem_ball_self εpos⟩,
  },
  {
    rintro ⟨hu, t, tsub, topen, tmem⟩,
    rw [metric.is_open_iff] at topen,
    rcases topen _ tmem with ⟨ε, εpos, εball⟩,
    refine ⟨hu, ε, εpos, _⟩,
    refine subset_trans _ tsub,
    apply set.inter_subset_inter_left,
    exact εball,
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

lemma relint_eq_int {A : set V} (hA : vector_span ℝ A = ⊤) :
relint A = interior A :=
begin
  cases A.eq_empty_or_nonempty with hs hs,
  {
    rw [hs],
    simp only [relint, set.preimage_empty, interior_empty, set.image_empty],
  },
  {
    rw [←affine_subspace.affine_span_eq_top_iff_vector_span_eq_top_of_nonempty] at hA,
    replace hA := congr_arg (coe : affine_subspace ℝ V → set V) hA,
    rw [coe_affine_span, affine_subspace.top_coe] at hA,
    {
      ext,
      rw [mem_relint', mem_interior, hA],
      simp only [set.mem_univ, set.inter_univ, true_and, exists_prop],
    },
    {
      exact hs,
    },
  },
end

lemma aspan_preimage_coe_le' {W : submodule ℝ V} (A : set V) :
span_points ℝ ((coe : W → V) ⁻¹' A) ⊆ coe ⁻¹' span_points ℝ A :=
begin
  have : coe ⁻¹' span_points ℝ A = (affine_subspace.comap W.subtype.to_affine_map (affine_span ℝ A) : set W) := rfl,
  rw [this, ←coe_affine_span, ←affine_subspace.le_def, affine_span_le],
  simp only [affine_subspace.coe_comap, linear_map.coe_to_affine_map, submodule.coe_subtype, coe_affine_span],
  exact set.preimage_mono (by apply subset_affine_span),
end

lemma relint_inter_flat {A : set V} {E : submodule ℝ V}
{x : V} (xA : x ∈ relint A) (xE : x ∈ E) :
(⟨x, xE⟩ : E) ∈ relint ((coe : E → V) ⁻¹' A) :=
begin
  have xA' := relint_subset_self A xA,
  simp only [mem_relint'] at xA ⊢,
  refine ⟨_, _⟩,
  {
    apply subset_affine_span,
    exact xA',
  },
  {
    rcases xA.2 with ⟨t, tsub, topen, tmem⟩,
    refine ⟨coe ⁻¹' t, _, _, _⟩,
    {
      refine subset_trans _ (set.preimage_mono tsub),
      rintro y ⟨hy₁, hy₂⟩,
      simp only [set.mem_inter_eq, set.mem_preimage, ←coe_affine_span] at hy₁ ⊢,
      exact ⟨hy₁, aspan_preimage_coe_le' _ hy₂⟩,
    },
    {
      exact open_in_subspace E.to_affine_subspace _ topen,
    },
    {
      exact tmem,
    },
  },
end

lemma relint_eq_iff_relopen {A : set V} :
relint A = A ↔ is_relopen A :=
begin
  simp only [is_relopen, relint],
  rw [←interior_eq_iff_open],
  split,
  {
    intro h,
    conv {
      to_rhs,
      congr, skip,
      rw [←h],
    },
    rw [set.preimage_image_eq],
    exact subtype.coe_injective,
  },
  {
    intro h,
    rw [h, set.image_preimage_eq_iff, subtype.range_coe],
    exact subset_affine_span ℝ A,
  },
end

lemma relint_relopen {A : set V} (hA : is_relopen A) :
relint A = A := relint_eq_iff_relopen.mpr hA

/- lemma interior_convex {A : set V} (Acv : convex ℝ A) :
convex ℝ (interior A) := sorry -/

/- lemma relint_convex {A : set V} (Acv : convex ℝ A) :
convex ℝ (relint A) := sorry -/

/- lemma cl_relint_eq_cl {A : set V} (Acv : convex ℝ A) :
closure (relint A) = closure A := sorry -/

lemma relint_nonempty {A : set V} (Acv : convex ℝ A)
(Ane : A.nonempty) : (relint A).nonempty := sorry

lemma exists_mem_open_segment_of_mem_relint {A : set V} {x y : V}
(xA : x ∈ relint A) (yA : y ∈ affine_span ℝ A) :
∃ z : V, z ∈ A ∧ x ∈ open_segment ℝ y z :=
begin
  rw [mem_relint'] at xA,
  obtain ⟨xA, U, hU₁, hU₂⟩ := xA,
  let f : ℝ → V := λ c, (1 + c) • x - c • y,
  have fc : continuous f := by continuity,
  have fz : f 0 = x,
  {
    simp only [f],
    rw [add_zero, one_smul, zero_smul, sub_zero],
  },
  haveI : (𝓝[set.Ioo (0 : ℝ) 1] 0).ne_bot := left_nhds_within_Ioo_ne_bot zero_lt_one,
  have mem_cl : (0 : ℝ) ∈ closure (set.Ioo (0 : ℝ) 1),
  {
    rw [closure_Ioo zero_ne_one],
    exact set.left_mem_Icc.mpr zero_le_one,
    all_goals {apply_instance},
  },
  rw [mem_closure_iff_seq_limit] at mem_cl,
  obtain ⟨t, ht₁, ht₂⟩ := mem_cl,
  have ftt : filter.tendsto (f ∘ t) filter.at_top (𝓝 (f 0)) :=
  filter.tendsto.comp fc.continuous_at ht₂,
  rw [fz, tendsto_at_top_nhds] at ftt,
  obtain ⟨n, hn⟩ := ftt U hU₂.2 hU₂.1,
  replace hn := hn n (le_refl n),
  have : (f ∘ t) n ∈ affine_span ℝ A,
  {
    simp only [f, function.comp_app],
    rw [add_smul, one_smul, add_sub_assoc, ←smul_sub, add_comm],
    refine affine_subspace.vadd_mem_of_mem_direction _ xA,
    {
      refine submodule.smul_mem _ _ _,
      refine affine_subspace.vsub_mem_direction xA yA,
    },
  },
  refine ⟨_, hU₁ ⟨hn, this⟩, _⟩,
  simp only [f, function.comp_app, mem_open_segment'],
  have dpos : 0 < (1 + t n) := add_pos zero_lt_one (ht₁ n).1,
  refine ⟨1 - (1 + t n)⁻¹, ⟨_, _⟩, _⟩,
  {
    simp only [sub_pos],
    apply inv_lt_one,
    rw [lt_add_iff_pos_right],
    exact (ht₁ n).1,
  },
  {
    rw [sub_lt_self_iff, inv_pos],
    exact add_pos zero_lt_one (ht₁ n).1,
  },
  {
    -- so tedious...
    simp only [sub_sub_cancel, smul_sub],
    rw [inv_smul_smul₀ (ne_of_gt dpos), sub_smul, smul_smul],
    rw [←sub_smul, add_sub_left_comm, self_eq_add_right, ←sub_smul],
    rw [smul_eq_zero],
    nth_rewrite 0 [←inv_mul_cancel (ne_of_gt dpos)],
    rw [sub_right_comm, ←mul_sub],
    simp only [add_tsub_cancel_right, mul_one, sub_self, eq_self_iff_true, true_or],
  },
end

lemma relopen_iff_exists_open_inter_aspan
{A : set V} :
is_relopen A ↔ ∃ B : set V, is_open B ∧ B ∩ affine_span ℝ A = A :=
begin
  simp only [is_relopen, is_open_induced_iff],
  apply exists_congr,
  simp only [and.congr_right_iff],
  intros B hB,
  simp only [←subtype.coe_injective.image_injective.eq_iff, subtype.image_preimage_coe],
  congr', -- Why does this work while congr doesn't?
  ext, simp only [set.mem_inter_eq, and_iff_left_iff_imp],
  intro xA,
  exact subset_affine_span ℝ A xA,
end

/- def make_relopen_open (A : set V) : set V :=
--{x : V | ∃ a : V, a ∈ A ∧ }
A + (vector_span ℝ A)ᗮ

lemma interior_make_relopen_open (A : set V) :
interior (make_relopen_open A) = make_relopen_open (relint A) :=
begin
  ext,
  simp only [mem_interior, make_relopen_open, set.mem_add, exists_prop, set_like.mem_coe, exists_and_distrib_left, vector_span_def, exists_prop],
  split,
  {
    rintro ⟨t, tss, topen, xt⟩,
    obtain ⟨y, z, yA, hz, rfl⟩ := tss xt,
    refine ⟨y, _, z, _, rfl⟩,
    {
      rw [mem_relint'],
      let t' := t + (vector_span ℝ A)ᗮ, --{x : V | ∃ y : V, y ∈ (vector_span ℝ A)ᗮ ∧ x + y ∈ t},
      refine ⟨subset_affine_span ℝ _ yA, t', _, _, _⟩,
      {
        have tss' : t' ⊆ A + (vector_span ℝ A)ᗮ,
        {
          simp only [t'],
          refine subset_trans (set.add_subset_add_right tss) _,
          rw [add_assoc],
          rintro - ⟨a, -, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩,
          refine ⟨a, b + c, ha, _, rfl⟩,
          rw [set_like.mem_coe],
          exact submodule.add_mem _ hb hc,
        },
        rintro w ⟨w₁, w₂⟩,
        obtain ⟨a, b, ha, hb, rfl⟩ := tss' w₁,
        have : b ∈ vector_span ℝ A,
        {
          rw [←add_sub_cancel' a b],
          apply vsub_mem_vector_span_of_mem_span_points_of_mem_span_points ℝ,
          exact w₂,
          exact subset_affine_span ℝ _ ha,
        },
        rw [set_like.mem_coe] at hb,
        replace hb := hb _ this,
        rw [inner_self_eq_zero] at hb,
        rw [hb, add_zero],
        exact ha,
      },
      {
        rw [metric.is_open_iff] at topen ⊢,
        rintro x ⟨x₁, x₂, hx₁, hx₂, rfl⟩,
        obtain ⟨ε, εpos, εball⟩ := topen x₁ hx₁,
        refine ⟨ε, εpos, _⟩,
        rw [←ball_add_singleton],
        rintro y ⟨y₁, y₂, hy₁, hy₂, rfl⟩,
        rw [set.mem_singleton_iff] at hy₂,
        obtain rfl := hy₂,
        exact ⟨y₁, y₂, εball hy₁, hx₂, rfl⟩,
      },
      {
        refine ⟨y + z, -z, xt, _, _⟩,
        {
          rw [set_like.mem_coe] at hz ⊢,
          exact submodule.neg_mem _ hz,
        },
        {
          simp only [add_neg_cancel_right],
        },
      },
    },
    {
      simp only [mem_orthogonal_span, set_like.mem_coe] at hz ⊢,
      intros u hu,
      apply hz u,
      obtain ⟨u₁, u₂, hu₁, hu₂, rfl⟩ := hu,
      exact ⟨u₁, u₂, relint_subset_self _ hu₁, relint_subset_self _ hu₂, rfl⟩,
    },
  },
  {
    rintro ⟨y, hy, z, hz, rfl⟩,
    rw [mem_relint] at hy,
    obtain ⟨ε, εpos, εball⟩ := hy.2,
    refine ⟨metric.ball (y + z) ε, _, _, _⟩,
    {
      intros w hw,
      let v := orthogonal_projection (vector_span ℝ A) (w - (y + z)),
      have : ∥v∥ < ε,
      {
        refine lt_of_le_of_lt _ (mem_ball_iff_norm.mp hw),
        refine le_trans (continuous_linear_map.le_op_norm (orthogonal_projection (vector_span ℝ A)) (w - (y + z))) _,
        refine le_trans
        (mul_le_mul_of_nonneg_right
        (orthogonal_projection_norm_le _) (norm_nonneg _)) _,
        rw [one_mul],
      },
      have hz': z ∈ (vector_span ℝ A)ᗮ,
      {
        admit,
      },
      have : ((w - (y + z)) - v) + z ∈ (vector_span ℝ A)ᗮ,
      {
        refine submodule.add_mem _ _ hz',
        exact sub_orthogonal_projection_mem_orthogonal _,
      },
      rw [←sub_sub, sub_add_eq_add_sub, sub_add_cancel, sub_sub] at this,
      refine ⟨y + v, w - (y + v), _, _, _⟩,
      {
        admit,
      },
      {
        exact this,
      },
      {
        simp only [add_sub_cancel'_right],
      },
    },
    {
      exact metric.is_open_ball,
    },
    {
      exact metric.mem_ball_self εpos,
    },
  },
end -/

/- lemma relopen_iff_open_preimage
{A : set V} :
is_relopen A ↔ is_open (make_relopen_open A) :=
begin
  rw [←relint_eq_iff_relopen],
  admit,
end -/

lemma cl_subset_aspan (A : set V) :
closure A ⊆ affine_span ℝ A :=
begin
  rw [is_closed.closure_subset_iff], rotate,
  {apply affine_subspace.closed_of_finite_dimensional},
  apply subset_affine_span,
end

lemma mem_open_segment_tendsto_left_of_tendsto_right {x y z : V}
(hy : y ∈ open_segment ℝ x z)
{t : ℕ → V}
(ht : filter.tendsto t filter.at_top (𝓝 z))
{E : affine_subspace ℝ V}
(yE : y ∈ E)
(zE : ∀ n, t n ∈ E) :
∃ u : ℕ → V, filter.tendsto u filter.at_top (𝓝 x) ∧
(∀ n : ℕ, y ∈ open_segment ℝ (u n) (t n)) ∧
(∀ n : ℕ, u n ∈ E) :=
begin
  rw [mem_open_segment'] at hy,
  obtain ⟨c, ⟨hc₁, hc₂⟩, hy⟩ := hy,
  let f : V → V := λ z', c⁻¹ • (y - (1 - c) • z'),
  have fc : continuous f := by continuity,
  have fz : f z = x :=
  by simp only [f, hy, smul_add, sub_smul, ne_of_gt hc₁, inv_smul_smul₀, ne.def, not_false_iff, add_sub_cancel],
  refine ⟨λ n, f (t n), _, _, _⟩,
  {
    rw [←fz],
    exact filter.tendsto.comp fc.continuous_at ht,
  },
  {
    intro n,
    rw [mem_open_segment'],
    refine ⟨c, ⟨hc₁, hc₂⟩, _⟩,
    simp only [ne_of_gt hc₁, smul_inv_smul₀, ne.def, not_false_iff, sub_add_cancel],
  },
  {
    intro n,
    simp only [f, smul_sub, sub_smul, one_smul, inv_smul_smul₀ (ne_of_gt hc₁)],
    rw [←sub_add, ←smul_sub],
    refine  affine_subspace.vadd_mem_of_mem_direction _ (zE n),
    {
      refine submodule.smul_mem _ _ _,
      exact affine_subspace.vsub_mem_direction yE (zE n),
    },
  },
end

lemma open_segment_subset_affine_subspace {x y : V}
{E : affine_subspace ℝ V} (xE : x ∈ E) (yE : y ∈ E) :
open_segment ℝ x y ⊆ E :=
begin
  rintro z hz,
  rw [mem_open_segment'] at hz,
  obtain ⟨c, ⟨hc₁, hc₂⟩, rfl⟩ := hz,
  rw [sub_smul, add_sub_left_comm, ←smul_sub, add_comm, one_smul],
  refine affine_subspace.vadd_mem_of_mem_direction _ yE,
  {
    refine submodule.smul_mem _ _ _,
    exact affine_subspace.vsub_mem_direction xE yE,
  },
end

lemma open_segment_subset_of_mem_relint_of_mem_cl {A : set V}
(Acv : convex ℝ A)
{x y : V} (hx : x ∈ relint A) (hy : y ∈ closure A) :
open_segment ℝ x y ⊆ A :=
begin
  rw [mem_relint'] at hx,
  obtain ⟨U, hU₁, hU₂⟩ := hx.2,
  intros a ha,
  let ha' := ha,
  rw [mem_open_segment'] at ha',
  obtain ⟨c, ⟨hc₁, hc₂⟩, ha'⟩ := ha',
  let hy' := hy,
  rw [mem_closure_iff_seq_limit] at hy,
  obtain ⟨t, ht₁, ht₂⟩ := hy,
  have : a ∈ affine_span ℝ A,
  {
    refine open_segment_subset_affine_subspace hx.1 _ ha,
    apply cl_subset_aspan,
    exact hy,
  },
  have ht₁' := λ n, subset_affine_span ℝ _ (ht₁ n),
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_open_segment_tendsto_left_of_tendsto_right ha ht₂ this ht₁',
  rw [tendsto_at_top_nhds] at hu₁,
  obtain ⟨n, hn⟩ := hu₁ U hU₂.2 hU₂.1,
  replace hn := hn n (le_refl n),
  replace hu₂ := hu₂ n,
  rw [convex_iff_open_segment_subset] at Acv,
  refine Acv (hU₁ ⟨hn, hu₃ n⟩) (ht₁ n) hu₂,
end

lemma closed_iff_segments_closable {A : set V}
(Acv : convex ℝ A):
is_closed A ↔ ∀ x y : V, open_segment ℝ x y ⊆ A → segment ℝ x y ⊆ A :=
begin
  split,
  {
    exact segments_closable_of_closed,
  },
  {
    intro h,
    rw [←closure_eq_iff_is_closed],
    refine subset_antisymm _ subset_closure,
    intros z hz,
    obtain ⟨x, hx⟩ := relint_nonempty Acv (closure_nonempty_iff.mp ⟨z, hz⟩),
    have := h _ _ (open_segment_subset_of_mem_relint_of_mem_cl Acv hx hz),
    exact this (right_mem_segment _ _ _),
  },
end