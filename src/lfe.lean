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
∃ (x : V) (c : ℝ), c > 0 ∧
bm.τ (convex_body_of_polytope P) U =
{x} + c • (bm.τ (convex_body_of_polytope Q) U)

lemma lfe_refl (P : polytope V) : lfe ⊤ P P :=
begin
  refine ⟨0, 1, zero_lt_one, _⟩,
  simp only [one_smul, set.singleton_add, zero_add, set.image_id'],
end

lemma lfe_symm
{U : set (metric.sphere (0 : V) 1)}
{P Q : polytope V}
(h : lfe U P Q) : lfe U Q P :=
begin
  obtain ⟨x, c, cpos, hxc⟩ := h,
  refine ⟨-c⁻¹ • x, c⁻¹, inv_pos_of_pos cpos, _⟩,
  rw [hxc, smul_add, ←add_assoc],
  simp only [neg_smul, set.smul_set_singleton,
  set.singleton_add_singleton, add_left_neg,
  set.singleton_add],
  simp only [subtype.val_eq_coe, set.image_add_left, neg_neg, set.preimage_add_left_singleton, add_left_neg, set.singleton_add,
  zero_add, set.image_id'],
  rw [inv_smul_smul₀ (ne_of_gt cpos)],
end

lemma lfe_mono
{U₁ U₂ : set (metric.sphere (0 : V) 1)}
{P Q : polytope V}
(hPQ : lfe U₂ P Q)
(hU : U₁ ⊆ U₂) :
lfe U₁ P Q :=
begin
  obtain ⟨x, c, cpos, hxc⟩ := hPQ,
  refine ⟨x, c, cpos, _⟩,
  simp only [τ_mono hU, hxc],
  rw [add_comm],
  simp only [face_translate, face_smul cpos],
  rw [add_comm],
  rw [set.smul_set_Union₂, set.Union₂_add],
end

lemma lfe_trans
{U₁ U₂ : set (metric.sphere (0 : V) 1)}
{P Q R : polytope V}
(h₁ : lfe U₁ P Q)
(h₂ : lfe U₂ Q R) : lfe (U₁ ∩ U₂) P R :=
begin
  obtain ⟨x₁, c₁, c₁pos, hxc₁⟩ := lfe_mono h₁ (set.inter_subset_left _ _),
  obtain ⟨x₂, c₂, c₂pos, hxc₂⟩ := lfe_mono h₂ (set.inter_subset_right _ _),
  refine ⟨x₁ + c₁ • x₂, c₁ * c₂, _, _⟩,
  {
    exact mul_pos c₁pos c₂pos,
  },
  {
    rw [hxc₁, hxc₂],
    simp only [smul_add, smul_smul, ←add_assoc],
    simp only [set.smul_set_singleton, set.singleton_add_singleton],
  },
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

/- lemma polytope_area_eq_face_area
{C : multiset (convex_body V)}
{P : polytope V}
(hPC : bm.is_area_coll (convex_body_of_polytope P ::ₘ C) ⊤)
{U : set (metric.sphere (0 : V) 1)} {u : metric.sphere (0 : V) 1}
(hU₁ : measurable_set U)
(hU₂ : ∀ v : metric.sphere (0 : V) 1, v ∈ U → normal_face P.val v.val = normal_face P.val u.val) :
bm.area (convex_body_of_polytope P ::ₘ C) U =
bm.area ((convex_body_of_polytope P).normal_face u.val ::ₘ C) U :=
begin
  refine bm.area_determined_by_τ hPC _ hU₁ _,
  {
    refine bm.is_area_coll_cons_of_head_subset _ hPC,
    apply normal_face_subset,
  },
  {
    intro M,
    simp only [bm.τ],
    congr,
    funext v,
    congr,
    funext hv,
    simp only [subtype.val_eq_coe, normal_face_add'],
    congr' 1,
    simp only [convex_body.normal_face, convex_body_of_polytope, subtype.val_eq_coe, subtype.coe_mk],
    simp only [subtype.val_eq_coe, subtype.coe_mk] at hU₂,
    rw [←hU₂ v hv],
    simp only [normal_face_idem_poly],
  },
end -/

-- MOVETO brunn_minkowski.lean
lemma area_determined_by_τ
{C : multiset (convex_body V)}
{K L : convex_body V}
(hC : bm.is_area_coll (K ::ₘ C))
(hD : bm.is_area_coll (L ::ₘ C))
{U : set (metric.sphere (0 : V) 1)}
(hU : measurable_set U)
(h : bm.τ K U = bm.τ L U) :
bm.area (K ::ₘ C) U = bm.area (L ::ₘ C) U :=
begin
  apply bm.area_determined_by_τ_add hC hD hU,
  intro M,
  exact τ_add_right_eq h,
end

-- MOVETO multiset.lean
@[simp]
lemma multiset.all_cons {α : Type}
(p : α → Prop) (a : α) (C : multiset α) :
multiset_all p (a ::ₘ C) ↔ p a ∧ multiset_all p C :=
begin
  simp only [multiset_all, multiset.mem_cons, forall_eq_or_imp],
end

-- MOVETO brunn_minkowski.lean
lemma is_area_coll_smul_cons
{K : convex_body V}
{C : multiset (convex_body V)}
(h : bm.is_area_coll (K ::ₘ C))
(c : nnreal) :
bm.is_area_coll (c • K ::ₘ C) :=
begin
  simp only [bm.is_area_coll, multiset.card_cons] at h ⊢,
  exact h,
end

lemma is_area_coll_add_singleton_cons
{K : convex_body V} {x : V}
{C : multiset (convex_body V)}
(h : bm.is_area_coll (K ::ₘ C)) :
bm.is_area_coll ((K + {x}) ::ₘ C) :=
begin
  simp only [bm.is_area_coll, multiset.card_cons] at h ⊢,
  exact h,
end

lemma area_pos_iff_of_lfe_aux
{P Q : polytope V} {U : set (metric.sphere (0 : V) 1)}
{Ks : multiset (convex_body V)}
(hPQ : lfe U P Q)
(ac₁ : bm.is_area_coll (convex_body_of_polytope P ::ₘ Ks))
(ac₂ : bm.is_area_coll (convex_body_of_polytope Q ::ₘ Ks))
(hU₁ : measurable_set U) :
∃ c : nnreal, 0 < c ∧
bm.area (convex_body_of_polytope Q ::ₘ Ks) U =
c • bm.area (convex_body_of_polytope P ::ₘ Ks) U :=
begin
  obtain ⟨x, c, cpos, hcx⟩ := lfe_symm hPQ,
  let c' := c.to_nnreal,
  have c'pos := real.to_nnreal_pos.mpr cpos,
  refine ⟨c', c'pos, _⟩,
  let P' := (c' • convex_body_of_polytope P) + {x},
  have : bm.area (convex_body_of_polytope Q ::ₘ Ks) U = bm.area (P' ::ₘ Ks) U,
  {
    simp only [P'],
    apply area_determined_by_τ,
    {exact ac₂},
    {
      apply is_area_coll_add_singleton_cons,
      apply is_area_coll_smul_cons,
      exact ac₁,
    },
    exact hU₁,
    {
      rw [τ_translate, τ_smul, add_comm],
      rw [hcx],
      simp only [c', nnreal.smul_def, real.coe_to_nnreal _ (le_of_lt cpos)],
    },
  },
  convert this using 1,
  simp only [P'],
  rw [bm.area_cons_translate,
      bm.area_cons_smul],
  {
    simp only [measure_theory.finite_measure.coe_fn_smul_apply],
  },
  {
    exact ac₁,
  },
  {
    apply is_area_coll_smul_cons,
    exact ac₁,
  },
end

-- MOVETO brunn_minkowski.lean
@[simp]
lemma is_area_coll_top
(C : multiset (convex_body V)) :
bm.is_area_coll C ↔ dim V = C.card + 1 :=
begin
  simp only [bm.is_area_coll],
end

lemma area_pos_iff_of_lfe
{P Q : polytope V} {U : set (metric.sphere (0 : V) 1)}
{Ks : multiset (convex_body V)}
(hPQ : lfe U P Q)
(hKs : dim V = Ks.card + 2)
(hU : measurable_set U) :
bm.area (convex_body_of_polytope P ::ₘ Ks) U > 0 ↔
bm.area (convex_body_of_polytope Q ::ₘ Ks) U > 0 :=
begin
  --have ac₁ : bm.is_area_coll (convex_body_of_polytope P ::ₘ Ks) ⊤,
  obtain ⟨c, cpos, hc⟩ := area_pos_iff_of_lfe_aux hPQ _ _ hU, rotate, rotate,
  any_goals {simp only [is_area_coll_top, multiset.card_cons, add_assoc, hKs]},
  simp only [hc, cpos, gt_iff_lt, algebra.id.smul_eq_mul, canonically_ordered_comm_semiring.mul_pos, true_and],
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
    intros W hW₁ hW₂,
    refine lt_of_lt_of_le _
      (finite_measure_mono (set.inter_subset_left W (interior U))),
    have : x ∈ W ∩ interior U := ⟨hW₁, h₂⟩,
    replace h₁ := h₁ _ this (is_open.inter hW₂ is_open_interior),
    rw [area_pos_iff_of_lfe _ hKs] at h₁, exact h₁,
    {exact (hW₂.inter is_open_interior).measurable_set},
    {
      exact lfe_mono (by exact hPQ <|> exact (lfe_symm hPQ)) (subset_trans (set.inter_subset_right W (interior U)) interior_subset : W ∩ interior U ⊆ U),
      -- refine lfe_mono (lfe_symm hPQ) _,
      -- refine subset_trans (set.inter_subset_right _ _) _,
      -- exact interior_subset, strange errors ????????
      -- -> all_goals!!!!
    },
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
  {
    intro n,
    simp only [bm.is_area_coll],
    simp only [dim_finrank, finrank_top, multiset.card_cons, add_assoc] at hdim ⊢,
    exact hdim,
  },
end