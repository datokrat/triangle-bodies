import convex convex_body multiset brunn_minkowski microid set_pi
  microid_ops sequence pre_pruning

open_locale pointwise
open_locale topological_space
open_locale nat

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma mem_msupport_prunenorm_sequence
{u : metric.sphere (0 : V) 1}
{s : ℕ → measure_theory.finite_measure (metric.sphere (0 : V) 1)}
{sl : measure_theory.finite_measure (metric.sphere (0 : V) 1)}
(htt : filter.tendsto s filter.at_top (𝓝 sl)) :
true := sorry

lemma pruning_lemma {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → prune_triple V k}
(valid : ∀ n : ℕ, valid_prune_triple (t n) u)
(tt : filter.tendsto ((cuspiness u) ∘ t) filter.at_top (𝓝 (0 : ℝ))) :
∃ (c : ℕ) (G : microid_generator_space V c),
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
    with ⟨c, φ, ϕ₂, tl, hmon, htt, hg, ha⟩,
  refine ⟨c, tl, _⟩,
  split,
  admit {
    simp only [vector_span, polytope_of_microid_generator],
    simp only [set_vsub_eq_sub],
    rw [←convex_hull_sub],
    rw [submodule.span_le],
    refine convex_hull_subset_vector_space _ _ _,
    intros v hv,
    change v ∈ vector_orth u.val,
    rw [mem_vector_orth],
    rcases hv with ⟨a, b, ⟨pa, rfl⟩, ⟨pb, rfl⟩, rfl⟩,
    admit,
  },
  {
    have bodytt := filter.tendsto.comp (body_of_gen_continuous_at tl) htt,
    rw [set.image_comp],
    convert comb_cl_of_lfe _ _ _ _,
    admit,
  },
end