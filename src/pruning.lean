import convex convex_body multiset brunn_minkowski microid set_pi
  microid_ops sequence pre_pruning

open_locale pointwise
open_locale topological_space
open_locale nat

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma tendsto_polytope_of_tendsto_generator {k : ℕ}
{t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k}
(tt : filter.tendsto t filter.at_top (𝓝 tl)) :
filter.tendsto (λ n, convex_body_of_polytope (polytope_of_microid_generator (t n))) filter.at_top
  (𝓝 (convex_body_of_polytope (polytope_of_microid_generator tl))) :=
begin
  simp only [body_of_poly_of_gen_eq],
  exact filter.tendsto.comp (body_of_gen_continuous_at tl) tt,
end

lemma angle_self_zero {k : ℕ} (m : fin k.succ) (u : metric.sphere (0 : V) 1) :
angle m m u = (λ G : microid_generator_space V k, 0) :=
begin
  funext,
  simp only [angle, sub_self, norm_zero, div_zero],
end

lemma cuspiness_eq_angle {k : ℕ}
(u : metric.sphere (0 : V) 1) (t : prune_triple V k) :
cuspiness u t = angle (prune_secondary_index t) (prune_cusp_index t) u (prune_triple_generator t) :=
begin
  simp only [cuspiness, angle, prune_direction, prune_cusp,
  prune_secondary, prune_gen_fn, prune_triple_generator],
end

lemma fun_eq_lambda {α β : Type} (f : α → β) :
f = (λ a, f a) := rfl

lemma diam_norm_eq_one {k : ℕ}
{G : unbounded_microid_generator V k} (h : diam_generator' G > 0) :
diam_generator' (norm_generator' G) = 1 :=
begin
  cases diam_norm_generator G,
  {assumption},
  {linarith},
end

lemma pruning_lemma' {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → prune_triple V k}
(valid : ∀ n : ℕ, valid_prune_triple (t n) u)
-- (is_cusp : ∀ n : ℕ, prune_cusp_index (t n) ∈ generator_face (prune_triple_generator (t n)) u)
(tt : filter.tendsto ((cuspiness u) ∘ t) filter.at_top (𝓝 (0 : ℝ))) :
∃ (c : ℕ) (G : microid_generator_space V c),
c ≤ k ∧
vector_span ℝ (polytope_of_microid_generator G).val ≠ ⊥ ∧
vector_span ℝ (polytope_of_microid_generator G).val ≤ vector_orth u.val ∧
in_combinatorial_closure u
((body_of_microid_generator ∘ prune_triple_generator ∘ t) '' set.univ)
(body_of_microid_generator G) :=
begin
  have is_cusp : ∀ n : ℕ, prune_cusp_index (t n) ∈ generator_face (prune_triple_generator (t n)) u,
  {
    intro n,
    simp only [generator_face, finset.mem_coe, finset.mem_filter],
    refine ⟨finset.mem_fin_range _, (valid n).1⟩,
  },
  let s :=
  λ n : ℕ, (prune_cusp_index (t n), prune_secondary_index (t n)),
  -- have hs : ∀ n, (s n).nonempty := λ n, generator_face_nonempty (prune_triple_generator (t n)) u,
  -- rcases ex_const_mem_subseq_of_setvalued_seq hs with ⟨b, ϕ, hmon, hb⟩,
  rcases ex_const_subseq_of_finite_range
    (λ n : ℕ, (prune_cusp_index (t n), prune_secondary_index (t n)))
      with ⟨⟨m, l⟩, ϕ, mon, index_const⟩,
  simp only [prod.mk.inj_iff] at index_const,
  replace index_const := and.intro (λ n, (index_const n).1.symm) (λ n, (index_const n).2.symm),
  have hm : ∀ n : ℕ, m ∈ generator_face (prune_triple_generator ((t ∘ ϕ) n)) u,
  {
    intro n,
    rw [index_const.1],
    apply is_cusp,
  },
  -- change ∀ (n : ℕ), b ∈ (s ∘ ϕ) n at hb,
  rcases pre_pruning_lemma hm
    with ⟨c, φ, ϕ₂, tl, clek, ⟨hmon, htt, hg, ha⟩, exU⟩,
  refine ⟨c, tl, clek, _, _, _⟩,
  {
    suffices h : diam_generator' tl.val = 1,
    {
      intro vsz,
      have nz : set.subsingleton (set.range tl.val),
      {
        intros x hx y hy,
        simp only [polytope_of_microid_generator] at vsz,
        replace hx := subset_convex_hull ℝ _ hx,
        replace hy := subset_convex_hull ℝ _ hy,
        have := vsub_mem_vector_span ℝ hx hy,
        rw [vsz] at this,
        replace this := (submodule.mem_bot ℝ).mp this,
        exact eq_of_sub_eq_zero this,
      },
      have := metric.diam_subsingleton nz,
      simp only [diam_generator', set.image_univ] at h,
      linarith,
    },
    let t' := λ n : ℕ, (prunenorm_generator φ (prune_triple_generator (t (ϕ (ϕ₂ n))))).val,
    suffices h₂ : ∀ n : ℕ,
    diam_generator' (t' n) = 1,
    {
      have htt' : filter.tendsto t' filter.at_top (𝓝 tl.val),
      {
        exact filter.tendsto.comp continuous_subtype_val.continuous_at htt,
      },
      refine lim_norm_gen htt' h₂,
    },
    have mφ : m ∈ finset.image φ finset.univ,
    {
      refine ha m _,
      simp only [anglett, angle_self_zero],
      convert tendsto_const_nhds,
      tauto,
    },
    have lφ : l ∈ finset.image φ finset.univ,
    {
      refine ha l _,
      replace tt := tendsto_subseq_of_tendsto _ mon tt,
      rw [fun_eq_lambda ((cuspiness u ∘ t) ∘ ϕ)] at tt,
      simp only [function.comp_app, cuspiness_eq_angle] at tt,
      simp only [anglett],
      convert tt,
      funext n,
      simp only [function.comp_app],
      rw [index_const.1 n, index_const.2 n],
    },
    rcases finset.mem_image.mp mφ with ⟨pm, -, rfl⟩,
    rcases finset.mem_image.mp lφ with ⟨pl, -, rfl⟩,
    intro n,
    simp only [t', prunenorm_generator],
    refine diam_norm_eq_one _,
    simp only [diam_generator', chop_generator, chop_generator'],
    have hd : dist ((prune_triple_generator (t (ϕ (ϕ₂ n)))).val (φ pm))
                   ((prune_triple_generator (t (ϕ (ϕ₂ n)))).val (φ pl)) > 0,
    {
      rw [gt_iff_lt, dist_pos],
      rw [index_const.1 (ϕ₂ n), index_const.2 (ϕ₂ n)],
      simp only [valid_prune_triple] at valid,
      exact (valid _).2,
    },
    refine lt_of_lt_of_le hd _,
    simp only [set.image_univ],
    exact metric.dist_le_diam_of_mem (pi_range_bounded _) ⟨pm, rfl⟩ ⟨pl, rfl⟩,
  },
  {
    simp only [vector_span, polytope_of_microid_generator],
    simp only [set_vsub_eq_sub],
    rw [←convex_hull_sub],
    rw [submodule.span_le],
    refine convex_hull_subset_vector_space _ _ _,
    intros v hv,
    change v ∈ vector_orth u.val,
    rw [mem_vector_orth],
    rcases hv with ⟨a, b, ⟨pa, rfl⟩, ⟨pb, rfl⟩, rfl⟩,
    simp only [generator_face, finset.mem_coe, finset.mem_filter] at hg,
    apply le_antisymm,
    all_goals {
      simp only [inner_sub_left, sub_nonpos, sub_nonneg],
      refine (hg _).2 _,
    },
  },
  {
    have bodytt := filter.tendsto.comp (body_of_gen_continuous_at tl) htt,
    have polytt := tendsto_polytope_of_tendsto_generator htt,
    rw [set.image_comp],
    rcases exU with ⟨U, hU, hlfe⟩,
    let S := polytope_of_microid_generator '' (prune_triple_generator ∘ t '' set.univ),
    have : in_combinatorial_closure u (convex_body_of_polytope '' S) _,
    {
      refine comb_cl_of_lfe hU polytt _,
      simp only [S],
      rw [←set.image_comp],
      intro n,
      refine ⟨polytope_of_microid_generator (prune_triple_generator (t (ϕ (ϕ₂ n)))), _, _⟩,
      {
        refine ⟨ϕ (ϕ₂ n), set.mem_univ _, rfl⟩,
      },
      {
        apply lfe_symm,
        exact hlfe n,
      },
    },
    rw [←set.image_comp] at this,
    convert this,
    all_goals {
      funext,
      simp only [function.comp_app, body_of_poly_of_gen_eq],
    },
  },
end

def fin_retraction {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (l : fin k₂.succ) : fin k₁.succ :=
⟨min l.val k₁, lt_of_le_of_lt (min_le_right _ _) (nat.lt_succ_self _)⟩

lemma fin_retraction_comp_incl {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
fin_retraction h ∘ fin.cast_le (nat.succ_le_succ h) = id :=
begin
  funext,
  simp only [fin_retraction, fin.val_eq_coe, fin.coe_cast_le,
    function.comp_app, id.def],
  apply fin.coe_injective,
  simp only [fin.val_eq_coe, fin.coe_cast_le, fin.coe_mk, min_eq_left_iff],
  exact nat.le_of_lt_succ x.property,
end

def convert_generator {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (G : microid_generator_space V k₁) :
microid_generator_space V k₂ :=
begin
  refine ⟨G.val ∘ (fin_retraction h), _⟩,
  have Gmem := G.property,
  simp only [mem_closed_ball_zero_iff] at Gmem ⊢,
  apply (pi_norm_le_iff zero_le_one).mpr,
  simp only [function.comp_app],
  intro i,
  exact (pi_norm_le_iff zero_le_one).mp Gmem (fin_retraction h i),
end

lemma polytope_convert_eq {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (G : microid_generator_space V k₁) :
polytope_of_microid_generator (convert_generator h G) =
polytope_of_microid_generator G :=
begin
  simp only [polytope_of_microid_generator, convert_generator],
  simp only [subtype.mk_eq_mk],
  refine congr_arg _ _,
  apply le_antisymm,
  {
    exact set.range_comp_subset_range _ _,
  },
  {
    conv {
      to_lhs,
      rw [←function.comp.right_id G.val, ←fin_retraction_comp_incl h,
        ←function.comp.assoc],
    },
    exact set.range_comp_subset_range _ _,
  },
end

lemma body_convert_eq {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (G : microid_generator_space V k₁) :
body_of_microid_generator (convert_generator h G) =
body_of_microid_generator G :=
begin
  simp only [←body_of_poly_of_gen_eq],
  rw [polytope_convert_eq h],
end

lemma pruning_lemma {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → prune_triple V k}
(valid : ∀ n : ℕ, valid_prune_triple (t n) u)
(tt : filter.tendsto ((cuspiness u) ∘ t) filter.at_top (𝓝 (0 : ℝ))) :
∃ (G : microid_generator_space V k),
vector_span ℝ (polytope_of_microid_generator G).val ≠ ⊥ ∧
vector_span ℝ (polytope_of_microid_generator G).val ≤ vector_orth u.val ∧
in_combinatorial_closure u
((body_of_microid_generator ∘ prune_triple_generator ∘ t) '' set.univ)
(body_of_microid_generator G) :=
begin
  rcases pruning_lemma' valid tt with
    ⟨c, G', hle, hG'⟩,
  let G := convert_generator hle G',
  refine ⟨convert_generator hle G', _⟩,
  simp only [polytope_convert_eq hle, body_convert_eq hle],
  exact hG',
end
