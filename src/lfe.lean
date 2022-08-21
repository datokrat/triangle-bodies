import convex convex_body brunn_minkowski microid
  measure set_pi
  init.data.fin.ops

open_locale pointwise
open_locale topological_space
open_locale nat

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]


def lfe --locally face equivalent
(U : set (metric.sphere (0 : V) 1))
(P Q : polytope V) :=
∀ u : metric.sphere (0 : V) 1,
u ∈ U →
∃ (x : V) (c : ℝ), c > 0 ∧ normal_face P.val u = {x} + c • (normal_face Q.val u)

lemma lfe_refl (P : polytope V) : lfe ⊤ P P :=
begin
  intros u uU,
  refine ⟨0, 1, zero_lt_one, _⟩,
  simp only [one_smul, set.singleton_add, zero_add, set.image_id'],
end

lemma lfe_symm
{U : set (metric.sphere (0 : V) 1)}
{P Q : polytope V}
(h : lfe U P Q) : lfe U Q P :=
begin
  intros v hv,
  rcases h v hv with ⟨x, c, cpos, hxc⟩,
  rw [hxc],
  refine ⟨-c⁻¹ • x, c⁻¹, inv_pos_of_pos cpos, _⟩,
  rw [smul_add, ←add_assoc],
  simp only [neg_smul, set.smul_set_singleton,
  set.singleton_add_singleton, add_left_neg,
  set.singleton_add],
  simp only [subtype.val_eq_coe, set.image_add_left, neg_neg, set.preimage_add_left_singleton, add_left_neg, set.singleton_add,
  zero_add, set.image_id'],
  rw [inv_smul_smul₀ (ne_of_gt cpos)],
end

lemma lfe_trans
{U₁ U₂ : set (metric.sphere (0 : V) 1)}
{P Q R : polytope V}
(h₁ : lfe U₁ P Q)
(h₂ : lfe U₂ Q R) : lfe (U₁ ∩ U₂) P R :=
begin
  intros v hv,
  simp only [set.mem_inter_eq] at hv,
  rcases h₁ v hv.1 with ⟨x₁, c₁, c₁pos, hxc₁⟩,
  rcases h₂ v hv.2 with ⟨x₂, c₂, c₂pos, hxc₂⟩,
  rw [hxc₁, hxc₂],
  refine ⟨x₁ + c₁ • x₂, c₁ * c₂, _, _⟩,
  {
    exact mul_pos c₁pos c₂pos,
  },
  {
    simp only [smul_add, smul_smul, ←add_assoc],
    simp only [set.smul_set_singleton, set.singleton_add_singleton],
  },
end

lemma lfe_mono
{U₁ U₂ : set (metric.sphere (0 : V) 1)}
{P Q : polytope V}
(hPQ : lfe U₂ P Q)
(hU : U₁ ⊆ U₂) :
lfe U₁ P Q :=
begin
  intros u hu,
  exact hPQ u (hU hu),
end

def in_combinatorial_closure
(u : metric.sphere (0 : V) 1)
(S : set (convex_body V))
(K : convex_body V) :=
∀ Ps : multiset (convex_body V), dim V = Ps.card + 2 →
u ∈ msupport (bm.area (K ::ₘ Ps)) →
u ∈ closure (⋃ L ∈ S, msupport (bm.area (L ::ₘ Ps)))

/- lemma mem_closure_of_mem_closure_nhd
{A U : set V} {x : V} (hU : U ∈ 𝓝 x) :
x ∈ closure A ↔ x ∈ closure (A ∩ U) := sorry

lemma mem_closure_of_mem_closure_nhd'
{A B U : set V} {x : V} (hU : U ∈ 𝓝 x) (hAB : A ∩ U = B ∩ U) :
x ∈ closure A ↔ x ∈ closure B := sorry -/

lemma mem_closure_of_subset_within_of_mem_closure
{α : Type} [topological_space α]
{A B U : set α} {x : α} (hU : U ∈ 𝓝 x) (hAB : A ∩ U ⊆ B ∩ U) :
x ∈ closure A → x ∈ closure B :=
begin
  simp only [mem_closure_iff_cluster_pt, cluster_pt_iff],
  intros h X hX W hW,
  let W' := W ∪ A,
  have W'p : W' ∈ filter.principal A,
  {
    apply set.subset_union_right,
  },
  obtain ⟨x, ⟨xX, xU⟩, xW'⟩ := h (filter.inter_mem hX hU) W'p,
  refine ⟨x, xX, _⟩,
  cases xW' with xW xA,
  {
    exact xW,
  },
  {
    apply hW,
    apply set.inter_subset_left,
    refine hAB ⟨xA, xU⟩,
  },
end

lemma area_pos_iff_of_lfe
{P Q : polytope V} {U : set (metric.sphere (0 : V) 1)}
{Ks : multiset (convex_body V)}
(hPQ : lfe U P Q)
(hKs : dim V = Ks.card + 2) :
bm.area (convex_body_of_polytope P ::ₘ Ks) U > 0 ↔
bm.area (convex_body_of_polytope Q ::ₘ Ks) U > 0 :=
begin
  -- partition into face relints
  -- use that faces are, up to homothety, contained in each other
  -- possibly require U to be open (no problem!)
  -- Hausdorff measure of the area segment monotone?
  admit,
end

-- MOVETO measure.lean
lemma finite_measure_mono
{μ : measure_theory.finite_measure (metric.sphere (0 : V) 1)}
{U₁ U₂ : set (metric.sphere (0 : V) 1)}
(h : U₁ ⊆ U₂) :
μ U₁ ≤ μ U₂ :=
begin
  simp only [measure_theory.finite_measure.coe_fn_eq_to_nnreal_coe_fn_to_measure],
  apply ennreal.to_nnreal_mono,
  {
    apply measure_theory.measure_ne_top,
  },
  {
    exact measure_theory.measure_mono h,
  },
end

lemma msupport_eq_of_lfe
{P Q : polytope V} {U : set (metric.sphere (0 : V) 1)}
{Ks : multiset (convex_body V)}
(hPQ : lfe U P Q)
(hKs : dim V = Ks.card + 2) :
msupport (bm.area (convex_body_of_polytope P ::ₘ Ks)) ∩ (interior U) =
msupport (bm.area (convex_body_of_polytope Q ::ₘ Ks)) ∩ (interior U) :=
begin
  ext,
  simp only [msupport, set.mem_inter_iff, set.mem_set_of],
  split,
  all_goals {
    rintro ⟨h₁, h₂⟩,
    refine ⟨_, h₂⟩,
    intros W hW,
    refine lt_of_lt_of_le _
      (finite_measure_mono (set.inter_subset_left W (interior U))),
    have : W ∩ interior U ∈ 𝓝 x,
    {
      apply filter.inter_mem hW,
      rw [mem_nhds_iff],
      refine ⟨interior U, subset_refl _, _, h₂⟩,
      exact is_open_interior,
    },
    replace h₁ := h₁ _ this,
    simpa only [area_pos_iff_of_lfe _ /- magic!? -/ hKs] using h₁,
    /- have hQP := lfe_symm hPQ,
    refine lfe_mono (by assumption) _,
    exact subset_trans (set.inter_subset_right W _) interior_subset, -/
  },
end

lemma comb_cl_of_lfe
{U : set (metric.sphere (0 : V) 1)}
{u : metric.sphere (0 : V) 1}
{t : ℕ → polytope V}
{S : set (polytope V)}
{tl : convex_body V}
(hU : U ∈ nhds u)
(tt : filter.tendsto (λ n, convex_body_of_polytope (t n))
  filter.at_top (𝓝 tl))
(hl : ∀ n : ℕ, ∃ P ∈ S, lfe U (t n) P) :
in_combinatorial_closure u (convex_body_of_polytope '' S)
tl :=
begin
  intros Ps hdim hu,
  have := bm.area_continuous Ps _ _ _ tt,
  {
    have hiU : interior U ∈ nhds u := interior_mem_nhds.mpr hU,
    replace := msupport_subset_of_tendsto _ _ this hu,
    simp only at this,
    refine mem_closure_of_subset_within_of_mem_closure
      hiU _ this,
    rw [set.Union₂_inter, set.Union_inter, set.Union_subset_iff],
    intro n,
    rcases hl n with ⟨P, hS, hlfe⟩,
    rw [msupport_eq_of_lfe hlfe hdim],
    refine subset_trans _ (set.subset_Union₂ (convex_body_of_polytope P) _),
    {
      exact subset_refl _, -- why do I have to use subset_trans?
    },
    {
      exact set.mem_image_of_mem _ hS,
    },
  },
  {exact ⊤},
  {
    intro n,
    simp only [bm.is_area_coll],
    split,
    {
      simp only [dim_finrank, finrank_top, multiset.card_cons, add_assoc] at hdim ⊢,
      exact hdim,
    },
    {
      intros K hK,
      simp only [convex_body_subset, submodule.top_coe, set.subset_univ],
    },
  },
end