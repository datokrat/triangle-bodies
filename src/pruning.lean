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
filter.tendsto (λ n, convex_body_of_polytope V (polytope_of_microid_generator (t n))) filter.at_top
  (𝓝 (convex_body_of_polytope V (polytope_of_microid_generator tl))) :=
begin
  simp only [body_of_poly_of_gen_eq],
  exact filter.tendsto.comp (body_of_gen_continuous_at tl) tt,
end

lemma pruning_lemma' {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → prune_triple V k}
(valid : ∀ n : ℕ, valid_prune_triple (t n) u)
(tt : filter.tendsto ((cuspiness u) ∘ t) filter.at_top (𝓝 (0 : ℝ))) :
∃ (c : ℕ) (G : microid_generator_space V c),
c ≤ k ∧
vector_span ℝ (polytope_of_microid_generator G).val ≤ vector_orth u.val ∧
in_combinatorial_closure u
((body_of_microid_generator ∘ prune_triple_generator ∘ t) '' set.univ)
(body_of_microid_generator G) :=
begin
  let s : ℕ → finset (fin k.succ) := λ n, generator_face (prune_triple_generator (t n)) u,
  have hs : ∀ n, (s n).nonempty := λ n, generator_face_nonempty (prune_triple_generator (t n)) u,
  rcases ex_const_mem_subseq_of_setvalued_seq hs with ⟨b, ϕ, hmon, hb⟩,
  change ∀ (n : ℕ), b ∈ (s ∘ ϕ) n at hb,
  rcases pre_pruning_lemma hb
    with ⟨c, φ, ϕ₂, tl, clek, ⟨hmon, htt, hg, ha⟩, exU⟩,
  refine ⟨c, tl, clek, _⟩,
  split,
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
    have : in_combinatorial_closure u (convex_body_of_polytope V '' S) _,
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
vector_span ℝ (polytope_of_microid_generator G).val ≤ vector_orth u.val ∧
in_combinatorial_closure u
((body_of_microid_generator ∘ prune_triple_generator ∘ t) '' set.univ)
(body_of_microid_generator G) :=
begin
  rcases pruning_lemma' valid tt with
    ⟨c, G', hle, hG'⟩,
  let G := convert_generator hle G',
  refine ⟨convert_generator hle G', _⟩,
  rw [polytope_convert_eq hle, body_convert_eq hle],
  exact hG',
end
