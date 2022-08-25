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

-- MOVETO brunn_minkowski.lean
lemma face_τ_eq_face_self
{U : set (metric.sphere (0 : V) 1)}
(K : convex_body V)
{u : metric.sphere (0 : V) 1} (hu : u ∈ U) :
normal_face (bm.τ K U) u.val = normal_face ↑K u :=
begin
  ext x,
  simp only [bm.τ, subtype.val_eq_coe, set.Union_coe_set, subtype.coe_mk],
  have hu' : (⟨u.val, u.property⟩ : metric.sphere (0 : V) 1) ∈ U,
  {
    simp only [subtype.val_eq_coe, subtype.coe_eta],
    exact hu,
  },
  split,
  {
    rintro ⟨hx₁, hx₂⟩,
    simp only [set.mem_Union] at hx₁,
    obtain ⟨v, hv₁, hv₂, xv⟩ := hx₁,
    have xK := normal_face_subset xv,
    refine ⟨xK, _⟩,
    intros y yK,
    obtain ⟨z, zu, hz⟩ := K.supp_exists_mem_face u,
    have := hx₂ z,
    simp only [set.mem_Union] at this,
    replace this := this ⟨u.val, u.property, hu', zu⟩,
    refine le_trans _ this,
    exact zu.2 y yK,
  },
  {
    intros xu,
    refine ⟨_, _⟩,
    {
      simp only [set.mem_Union],
      exact ⟨u.val, u.property, hu', xu⟩,
    },
    {
      intros y hy,
      simp only [set.mem_Union] at hy,
      obtain ⟨w, -, -, yw⟩ := hy,
      have yK := normal_face_subset yw,
      exact xu.2 y yK,
    },
  },
end

-- MOVETO brunn_minkowski.lean
lemma τ_mono
{U₁ U₂ : set (metric.sphere (0 : V) 1)}
{K : convex_body V}
(hU : U₁ ⊆ U₂) :
bm.τ K U₁ = ⋃ (u : metric.sphere (0 : V) 1) (hu : u ∈ U₁), normal_face (bm.τ K U₂) u :=
begin
  ext x,
  simp only [bm.τ, subtype.val_eq_coe, set.Union_coe_set, subtype.coe_mk, set.mem_Union, exists_prop,
  exists_and_distrib_right],
  split,
  {
    rintro ⟨v, ⟨hv₁, hv₂⟩, xK⟩,
    refine ⟨v, ⟨hv₁, hv₂⟩, _, _⟩,
    {
      simp only [set.mem_Union, exists_prop, exists_and_distrib_right],
      refine ⟨v, ⟨hv₁, hU hv₂⟩, xK⟩,
    },
    {
      intros y hy,
      simp only [set.mem_Union] at hy,
      obtain ⟨w, -, -, yK⟩ := hy,
      replace yK := normal_face_subset yK,
      exact xK.2 y yK,
    },
  },
  {
    rintro ⟨v, ⟨hv₁, hv₂⟩, xv⟩,
    refine ⟨v, ⟨hv₁, hv₂⟩, _, _⟩,
    {
      have := normal_face_subset xv,
      simp only [set.mem_Union] at this,
      obtain ⟨w, -, -, xw⟩ := this,
      exact normal_face_subset xw,
    },
    {
      intros y yK,
      obtain ⟨z, zv, hz⟩ := K.supp_exists_mem_face v,
      have := xv.2 z,
      simp only [set.mem_Union] at this,
      replace this := this ⟨v, hv₁, hU hv₂, zv⟩,
      refine le_trans _ this,
      exact zv.2 y yK,
    },
  },
end

-- MOVETO brunn_minkowski.lean
lemma τ_add_right_eq
{U : set (metric.sphere (0 : V) 1)}
{K₁ K₂ L : convex_body V}
(h : bm.τ K₁ U = bm.τ K₂ U) :
bm.τ (K₁ + L) U = bm.τ (K₂ + L) U :=
begin
  simp only [bm.τ],
  congr, funext u, congr, funext hu,
  simp only [subtype.val_eq_coe, normal_face_add'],
  rw [←face_τ_eq_face_self K₁ hu, ←face_τ_eq_face_self K₂ hu],
  rw [h],
end

-- MOVETO face.lean
@[simp]
lemma normal_face_singleton (x : V) (u : V) :
normal_face {x} u = {x} :=
begin
  ext,
  simp only [mem_normal_face, set.mem_singleton_iff, ge_iff_le, forall_eq, and_iff_left_iff_imp],
  rintro rfl,
  apply le_refl,
end

@[simp]
lemma normal_face_zero (u : V) :
normal_face 0 u = 0 :=
begin
  have : (0 : set V) = {0} := rfl,
  rw [this],
  apply normal_face_singleton,
end

-- MOVETO brunn_minkowski.lean
lemma τ_smul
{U : set (metric.sphere (0 : V) 1)}
{K : convex_body V}
{c : nnreal} :
bm.τ (c • K) U = c • (bm.τ K U) :=
begin
  simp only [bm.τ],
  by_cases h : c = 0,
  {
    obtain rfl := h,
    simp only [zero_smul, subtype.val_eq_coe, convex_body.coe_zero, set.Union_coe_set, subtype.coe_mk],
    simp only [normal_face_zero],
    simp only [set.smul_set_Union],
    congr, funext, congr, funext, congr, funext h,
    rw [←subtype.val_eq_coe],
    simp only [set.zero_smul_set (convex_body.normal_face_nonempty _ _)],
  },
  {
    have : (↑c : ℝ) > 0,
    {
      apply lt_of_le_of_ne,
      {apply nnreal.coe_nonneg},
      {
        intro hc,
        rw [←nnreal.coe_zero] at hc,
        exact h (nnreal.coe_injective hc.symm),
      },
    },
    simp only [subtype.val_eq_coe, convex_body.coe_smul, set.Union_coe_set, subtype.coe_mk],
    simp only [set.smul_set_Union],
    congr, funext, congr, funext, congr, funext x,
    apply face_smul this,
  },
end

lemma τ_translate
{U : set (metric.sphere (0 : V) 1)}
{K : convex_body V}
{x : V} :
bm.τ (K + {x}) U = (bm.τ K U) + {x} :=
begin
  simp only [bm.τ],
  simp only [subtype.val_eq_coe, convex_body.coe_add, set.Union_coe_set, subtype.coe_mk],
  simp only [set.Union_add],
  congr, funext, congr, funext, congr, funext x,
  apply face_translate,
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
(hC : bm.is_area_coll (K ::ₘ C) ⊤)
(hD : bm.is_area_coll (L ::ₘ C) ⊤)
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
{E : submodule ℝ V}
(h : bm.is_area_coll (K ::ₘ C) E)
(c : nnreal) :
bm.is_area_coll (c • K ::ₘ C) E :=
begin
  simp only [bm.is_area_coll, multiset.card_cons, multiset.all_cons] at h ⊢,
  obtain ⟨h₁, h₂, h₃⟩ := h,
  refine ⟨h₁, _, h₃⟩,
  rintro x ⟨x, hx, rfl⟩,
  replace hx := h₂ hx,
  apply submodule.smul_mem,
  exact hx,
end

lemma is_area_coll_add_singleton_cons
{K : convex_body V} {x : V}
{C : multiset (convex_body V)}
{E : submodule ℝ V}
(xE : x ∈ E)
(h : bm.is_area_coll (K ::ₘ C) E) :
bm.is_area_coll ((K + {x}) ::ₘ C) E :=
begin
  simp only [bm.is_area_coll, multiset.card_cons, multiset.all_cons] at h ⊢,
  obtain ⟨h₁, h₂, h₃⟩ := h,
  refine ⟨h₁, _, h₃⟩,
  rintro - ⟨k, y, hk, hy, rfl⟩,
  simp only [subtype.val_eq_coe, convex_body.coe_singleton, set.mem_singleton_iff] at hy,
  obtain rfl := hy,
  apply submodule.add_mem,
  exact h₂ hk,
  exact xE,
end

lemma area_pos_iff_of_lfe_aux
{P Q : polytope V} {U : set (metric.sphere (0 : V) 1)}
{Ks : multiset (convex_body V)}
(hPQ : lfe U P Q)
(ac₁ : bm.is_area_coll (convex_body_of_polytope P ::ₘ Ks) ⊤)
(ac₂ : bm.is_area_coll (convex_body_of_polytope Q ::ₘ Ks) ⊤)
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
      apply is_area_coll_add_singleton_cons submodule.mem_top,
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
  rw [bm.area_cons_translate submodule.mem_top,
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
bm.is_area_coll C ⊤ ↔ dim V = C.card + 1 :=
begin
  simp only [bm.is_area_coll, dim_finrank, finrank_top, and_iff_left_iff_imp],
  rintro -,
  intros K hK x xK,
  simp only [submodule.top_coe],
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