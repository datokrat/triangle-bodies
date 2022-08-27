import convex convex_body linalg measure criticality
  polytope face
  submodule_pair
  analysis.convex.basic
  data.multiset.basic
  measure_theory.measure.measure_space
  measure_theory.measure.hausdorff
  topology.basic
  data.mv_polynomial.basic

open_locale pointwise
open_locale ennreal -- for ∞ notation
open_locale topological_space -- for 𝓝 notation

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V: Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]

noncomputable instance sph_borel :=
borel (metric.sphere (0 : V) 1)

instance sph_borel_space : borel_space (metric.sphere (0 : V) 1) :=
⟨rfl⟩

noncomputable instance vspace_borel :=
borel V

instance vspace_borel_space : borel_space V := ⟨rfl⟩

-- instance : opens_measurable_space (metric.sphere (0 : V) 1) := sorry

def set_res_amb
(E : submodule ℝ V)
(A : set V) : set E :=
E.subtype ⁻¹' A

def coll_res_amb
(C : multiset (set V))
(E : submodule ℝ V) : multiset (set E) :=
C.map (set_res_amb E)

def coe_sph (E : submodule ℝ V) : metric.sphere (0 : E) 1 → metric.sphere (0 : V) 1 :=
begin
  intro x,
  refine ⟨x.val.val, x.property⟩,
end

def uncoe_sph (E : submodule ℝ V) (u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) : metric.sphere (0 : E) 1 :=
begin
  refine ⟨⟨u, uE⟩, _⟩,
  simp only [mem_sphere_zero_iff_norm, submodule.coe_norm, submodule.coe_mk,
             norm_eq_of_mem_sphere],
end

lemma coe_uncoe_sph {E : submodule ℝ V}
(u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) :
coe_sph E (uncoe_sph E u uE) = u :=
begin
  simp only [coe_sph, uncoe_sph],
  apply subtype.coe_injective,
  simp only [subtype.coe_eta],
end

namespace bm

axiom vol
(C : multiset (convex_body V))
: nnreal

axiom area
(C : multiset (convex_body V))
: measure_theory.finite_measure (metric.sphere (0 : V) 1)

def is_vol_coll (C : multiset (convex_body V)) (E : submodule ℝ V) : Prop :=
dim E = C.card ∧ multiset_all (convex_body_subset E) C

def is_area_coll (C : multiset (convex_body V))  : Prop :=
dim V = C.card + 1

def is_almost_area_coll (C : multiset (convex_body V)) : Prop :=
dim V = C.card + 2

lemma factorize_vol
{C : multiset (convex_body V)}
{D : multiset (convex_body V)}
{E F : submodule ℝ V}
(hC : is_vol_coll C E)
(hCD : is_vol_coll (C + D) F)
(hEF : E ≤ F) :
vol (C + D) = vol C * vol (proj_coll Eᗮ D) :=
sorry

-- What happens if F is not ⊤?
lemma factorize_area
{E : submodule ℝ V}
{C : multiset (convex_body V)}
{D : multiset (convex_body V)}
(hC : is_vol_coll C E)
(hCD : is_area_coll (C + D))
(hsc : semicritical_spaces (C.map span_of_convex_body)) :
msupport (area (C + D)) = coe_sph Eᗮ '' msupport (area (proj_coll Eᗮ D)) :=
sorry

lemma vol_continuous
{E : submodule ℝ V}
(C : multiset (convex_body V))
(C1 : ℕ → convex_body V)
(C1lim : convex_body V)
(hC : ∀ n : ℕ, is_vol_coll (C1 n ::ₘ C) E)
(ht : filter.tendsto
  C1
  filter.at_top
  (𝓝 C1lim))
: filter.tendsto (λ n, vol (C1 n ::ₘ C)) filter.at_top (𝓝 (vol (C1lim ::ₘ C))) :=
sorry

lemma area_cons_translate
{K : convex_body V}
{C : multiset (convex_body V)} {x : V}
(hC : is_area_coll (K ::ₘ C)) :
area ((K + {x}) ::ₘ C) = area (K ::ₘ C) := sorry

lemma area_cons_smul
{K : convex_body V}
{C : multiset (convex_body V)} {c : nnreal}
(hC : is_area_coll (K ::ₘ C)) :
area ((c • K) ::ₘ C) = c • area (K ::ₘ C) := sorry

lemma area_cons_add
{K L : convex_body V}
{C : multiset (convex_body V)}
(hC : is_almost_area_coll C) :
area ((K + L) ::ₘ C) = area (K ::ₘ C) + area (L ::ₘ C) := sorry

lemma area_continuous
(C : multiset (convex_body V))
(C1 : ℕ → convex_body V)
(C1lim : convex_body V)
(hC : ∀ n : ℕ, is_area_coll (C1 n ::ₘ C))
(ht : filter.tendsto
  C1
  filter.at_top
  (𝓝 C1lim))
: filter.tendsto (λ n, area (C1 n ::ₘ C)) filter.at_top (𝓝 (area (C1lim ::ₘ C))) :=
sorry

lemma area_empty : msupport (area (0 : multiset (convex_body V))) = ⊤ :=
sorry

def τ' (A : set V) (U : set (metric.sphere (0 : V) 1)) : set V :=
⋃ (u : metric.sphere (0 : V) 1) (uU : u ∈ U),
normal_face A u.val

def τ (K : convex_body V) (U : set (metric.sphere (0 : V) 1)) : set V :=
⋃ (u : metric.sphere (0 : V) 1) (H : u ∈ U),
normal_face K.val u.val

lemma is_area_coll_cons_of_head_subset
{C : multiset (convex_body V)} {K L : convex_body V}
{E : submodule ℝ V}
(CD : K.val ⊆ L.val)
(h : is_area_coll (L ::ₘ C)) :
is_area_coll (K ::ₘ C) :=
begin
  simp only [is_area_coll, multiset.card_cons] at h ⊢,
  exact h,
end

/- noncomputable def area_polynomial {σ : Type} [fintype σ] (K : σ → convex_body V)
(U : set (metric.sphere (0 : V) 1)) :
mv_polynomial σ ℝ :=
begin
  apply finsupp.on_finset, rotate,
  {
    refine finset.image (_ : (σ → fin (dim V)) → σ →₀ ℕ) finset.univ,
    {
      intro φ,
      apply finsupp.on_finset, rotate,
      exact finset.univ,
      exact λ i, φ i,
      simp only [finset.mem_univ, implies_true_iff],
    },
  },
  {
    intro φ,
    exact ite (dim V = φ.sum (λ a, id) + 1)
      (area (φ.to_multiset.map K) U)
      0,
  },
  {
    intros φ h,
    rw [ite_ne_right_iff] at h,
    replace h := le_of_eq h.1.symm,
    --rw [nat.add_one_le_iff] at h,
    /- have dpos : 0 < dim V := lt_of_le_of_lt (nat.zero_le _) h,
    replace h := nat.le_pred_of_lt h, -/
    rw [finset.mem_image],
    refine ⟨_, finset.mem_univ _, _⟩,
    {
      intro i,
      refine ⟨φ i, _⟩,
      rw [←nat.succ_le_iff, ←nat.add_one],
      refine le_trans (add_le_add_right _ 1) h,
      by_cases hc : i ∈ φ.support,
      {
        refine finset.single_le_sum _ hc,
        simp only [nat.zero_le, imp_true_iff],
      },
      {
        rw [finsupp.mem_support_iff] at hc,
        push_neg at hc,
        rw [hc],
        apply nat.zero_le,
      },
    },
    {
      simp only [fin.coe_mk, finsupp.ext_iff, finsupp.on_finset_apply, implies_true_iff, eq_self_iff_true],
    },
  },
end

lemma area_polynomial_eq_area {σ : Type} [fintype σ] (K : σ → convex_body V)
{U : set (metric.sphere (0 : V) 1)}
(hU : measurable_set U) (φ : σ →₀ nnreal) :
mv_polynomial.eval (φ.map_range coe nnreal.coe_zero) (area_polynomial K U) =
area (multiset.repeat (finset.univ.sum (λ i, φ i • K i)) (dim V - 1)) U :=
begin
end -/

-- only makes sense if dim V ≥ 1
noncomputable def diagonal_area (K : convex_body V) := area (multiset.repeat K (dim V - 1))

noncomputable def diagonal_area' (K : convex_body V) (U : set (metric.sphere (0 : V) 1)) : nnreal :=
diagonal_area K U

lemma diagonal_area'_def (K : convex_body V) (U : set (metric.sphere (0 : V) 1)) :
diagonal_area' K U = diagonal_area K U := rfl

lemma area_determined_by_diagonals
{ι : Type}
{C : multiset ι}
(hC : dim V = C.card + 1)
{U : set (metric.sphere (0 : V) 1)}
(hU : measurable_set U)
{f g : ι → convex_body V}
(hfg : ∀ w : ι →₀ nnreal, diagonal_area (finsupp.total ι _ _ f w) U = diagonal_area (finsupp.total ι _ _ g w) U) :
area (C.map f) U = area (C.map g) U := sorry

-- Schneider, Theorem 4.2.3
lemma area_eq_hausdorff_τ
{K : convex_body V}
(hK : vector_span ℝ K.val = ⊤)
(hdim : dim V > 0) :
∀ U : set (metric.sphere (0 : V) 1),
measurable_set U →
diagonal_area K U =
(measure_theory.measure.hausdorff_measure
(dim V - 1)
(τ K U)).to_nnreal := sorry

def multiset.cons_index {β : Type}
(B : multiset β) : multiset (unit ⊕ β) := sum.inl unit.star ::ₘ B.map sum.inr

def unit_oplus_fn {α β : Type}
(b : β) (f : α → β) : unit ⊕ α → β
| (sum.inl _) := b
| (sum.inr a) := f a

lemma multiset.cons_eq_map {β : Type}
(a : β) (B : multiset β) :
(multiset.cons_index B).map (unit_oplus_fn a id) = a ::ₘ B :=
begin
  simp only [multiset.cons_index, unit_oplus_fn, multiset.map_cons, multiset.map_map, function.comp_app, multiset.map_id', id.def],
end

lemma is_area_coll_diagonal
(hdim : dim V > 0)
(K : convex_body V) :
is_area_coll (multiset.repeat K (dim V - 1)) :=
begin
  obtain ⟨n, hn⟩ := nat.exists_eq_succ_of_ne_zero (ne_of_gt hdim),
  simp only [hn, nat.succ_sub_succ_eq_sub, tsub_zero],
  simp only [is_area_coll, multiset.card_repeat],
  exact hn,
end

lemma apply_unit_oplus_fn {α β γ : Type}
(x : unit ⊕ α) (b : β) (f : α → β) (g : β → γ) :
g (unit_oplus_fn b f x) = unit_oplus_fn (g b) (g ∘ f) x :=
begin
  cases x with x x,
  all_goals {refl},
end

lemma finsupp.sum_unit_oplus {α : Type}
(w : unit ⊕ α →₀ nnreal) (K : unit ⊕ α → nnreal → convex_body V)
(hK₁ : ∀ i, K i 0 = 0)
(hK₂ : ∀ j c₁ c₂, K j (c₁ + c₂) = K j c₁ + K j c₂):
w.sum K =
K (sum.inl unit.star) (w (sum.inl unit.star)) +
(w.comap_domain _ (sum.inr_injective.inj_on _)).sum (K ∘ sum.inr) :=
begin
  let w' : unit ⊕ α →₀ nnreal := w.update (sum.inl unit.star) 0,
  have h₁: w = w'.update (sum.inl unit.star) (w (sum.inl unit.star)),
  {
    ext,
    simp only [finsupp.coe_update, function.update_idem, function.update_eq_self],
  },
  rw [h₁],
  have bla := finsupp.sum_update_add w' (sum.inl unit.star) (w (sum.inl unit.star)) K _ _,
  any_goals {assumption},
  rw [h₁] at bla,
  simp only [w', hK₁, finsupp.coe_update, function.update_same, add_zero] at bla,
  simp only [finsupp.coe_update, function.update_idem, function.update_eq_self],
  rw [add_comm],
  convert bla using 2,
  have h₂ : w.comap_domain _ (sum.inr_injective.inj_on _) = w'.comap_domain _ (sum.inr_injective.inj_on _),
  {
    ext,
    simp only [finsupp.comap_domain_apply, finsupp.coe_update, sum.update_inl_apply_inr],
  },
  simp only [w'] at h₁,
  rw [←h₁, h₂],
  rw [finsupp.sum_comap_domain],
  refine ⟨_, _, _⟩,
  {
    intro x,
    exact id,
  },
  {
    exact sum.inr_injective.inj_on _,
  },
  {
    intros x hx,
    cases x,
    {
      cases x,
      simp only [finsupp.support_update_zero, finset.coe_erase, set.mem_diff, set.mem_singleton, not_true, and_false] at hx,
      contradiction,
    },
    {
      exact set.mem_image_of_mem _ hx,
    },
  },
end

lemma finsupp.total_unit_oplus {α : Type}
(w : unit ⊕ α →₀ nnreal) (K : unit ⊕ α → convex_body V) :
finsupp.total _ _ _ K w =
(w (sum.inl unit.star)) • K (sum.inl unit.star) +
finsupp.total _ _ _ (K ∘ sum.inr)
(w.comap_domain _ (sum.inr_injective.inj_on _)) :=
begin
  simp only [finsupp.total, finsupp.lsum, linear_map.coe_smul_right, linear_map.id_coe, id.def, linear_equiv.coe_mk,
  linear_map.coe_mk, function.comp_app],
  let K' : unit ⊕ α → nnreal → convex_body V := λ i c, c • K i,
  refine finsupp.sum_unit_oplus w K' _ _,
  {
    simp only [zero_smul, forall_const],
  },
  {
    simp only [add_smul, eq_self_iff_true, forall_const],
  },
end

-- MOVETO set_pi.lean
lemma set.vsub_eq_sub
(A B : set V) :
A -ᵥ B = A - B := rfl

lemma convex_body.full_dimensional_smul
{c : nnreal}
(cpos : c ≠ 0)
{K : convex_body V}
(hK : vector_span ℝ K.val = ⊤) :
vector_span ℝ (c • K).val = ⊤ :=
begin
  rw [←hK],
  simp only [vector_span_def],
  simp only [subtype.val_eq_coe, convex_body.coe_smul,
    nnreal.smul_def, set.vsub_eq_sub],
  have : ∀ (c : ℝ) (K L : set V), c • (K - L) = c • K - c • L,
  {
    intros c K L,
    ext, split,
    {
      rintro ⟨-, ⟨k, l, hk, hl, rfl⟩, rfl⟩,
      refine ⟨c • k, c • l, ⟨k, hk, rfl⟩, ⟨l, hl, rfl⟩, (smul_sub c k l).symm⟩,
    },
    {
      rintro ⟨-, -, ⟨k, hk, rfl⟩, ⟨l, hl, rfl⟩, h⟩,
      refine ⟨k - l, ⟨k, l, hk, hl, rfl⟩, _⟩,
      rw [←h, smul_sub],
    },
  },
  rw [←this, submodule.span_smul_eq_of_is_unit],
  replace cpos : (↑c : ℝ) ≠ 0,
  {simp only [cpos, ne.def, nnreal.coe_eq_zero, not_false_iff]},
  exact ne.is_unit cpos,
end

lemma convex_body.vspan_le_vspan_add_right
(L : convex_body V)
{K : convex_body V} :
vector_span ℝ K.val ≤ vector_span ℝ (K + L).val :=
begin
  obtain ⟨l, hl⟩ := nonempty_convex_body L.property,
  simp only [vector_span, subtype.val_eq_coe, convex_body.coe_add, submodule.span_le] at hl ⊢,
  rintro - ⟨k₁, k₂, hk₁, hk₂, rfl⟩,
  apply submodule.subset_span,
  refine ⟨k₁ + l, k₂ + l, ⟨k₁, l, hk₁, hl, rfl⟩, ⟨k₂, l, hk₂, hl, rfl⟩, _⟩,
  simp only [vsub_eq_sub, add_sub_add_right_eq_sub],
end

lemma convex_body.full_dimensional_add_right
(L : convex_body V)
{K : convex_body V}
(hK : vector_span ℝ K.val = ⊤) :
vector_span ℝ (K + L).val = ⊤ :=
begin
  apply le_antisymm le_top,
  rw [←hK],
  apply convex_body.vspan_le_vspan_add_right,
end

lemma convex_body.full_dimensional_add_left
(L : convex_body V)
{K : convex_body V}
(hK : vector_span ℝ K.val = ⊤) :
vector_span ℝ (L + K).val = ⊤ :=
begin
  rw [add_comm],
  exact convex_body.full_dimensional_add_right L hK,
end

lemma convex_body.add_smul_left_pos
{c : nnreal}
(cpos : c ≠ 0)
(K L : convex_body V) :
c • K + L = c • (K + c⁻¹ • L) :=
begin
  simp only [cpos, smul_add, smul_inv_smul₀, ne.def, not_false_iff],
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

lemma area_determined_by_τ_add'
{C : multiset (convex_body V)}
{K L : convex_body V}
(hC₁ : is_area_coll (K ::ₘ C))
(hC₂ : vector_span ℝ K.val = ⊤)
(hD₂ : vector_span ℝ L.val = ⊤)
{U : set (metric.sphere (0 : V) 1)}
(hU : measurable_set U)
(h : ∀ M : convex_body V, τ (K + M) U = τ (L + M) U) :
area (K ::ₘ C) U = area (L ::ₘ C) U :=
begin
  have hdim : dim V = C.card + 1 + 1,
  {
    simpa only [is_area_coll, multiset.card_cons] using hC₁,
  },
  have hdim' : dim V > 0,
  {
    rw [hdim],
    simp only [gt_iff_lt, nat.succ_pos'],
  },
  simp only [←multiset.cons_eq_map],
  apply area_determined_by_diagonals,
  {
    simpa only [is_area_coll, multiset.card_cons, multiset.card_map, multiset.cons_index] using hC₁,
  },
  exact hU,
  intro w,
  simp only [finsupp.total_unit_oplus],
  by_cases hw : sum.inl unit.star ∈ w.support,
  {
    rw [finsupp.mem_support_iff] at hw,
    rw [area_eq_hausdorff_τ, area_eq_hausdorff_τ], rotate,
    any_goals {assumption},
    any_goals {
      apply convex_body.full_dimensional_add_right,
      apply convex_body.full_dimensional_smul hw,
      assumption,
    },
    congr' 2,
    simp only [convex_body.add_smul_left_pos hw],
    simp only [τ_smul],
    simp only [unit_oplus_fn, h],
    refl,
  },
  {
    rw [finsupp.mem_support_iff] at hw,
    push_neg at hw,
    simp only [hw, zero_smul, zero_add],
    refl,
  },
end

-- MOVETO convex_body.lean
def convex_body.ball
(x : V) {ε : ℝ} (εnn : 0 ≤ ε) : convex_body V :=
begin
  refine ⟨metric.closed_ball x ε, _, _, _⟩,
  {
    apply convex_closed_ball,
  },
  {
    apply proper_space.is_compact_closed_ball,
  },
  {
    exact metric.nonempty_closed_ball.mpr εnn,
  },
end

noncomputable def convex_body.unit_ball : convex_body V :=
convex_body.ball 0 zero_le_one

lemma convex_body.full_dimensional_ball
{x : V} {ε : ℝ} (εpos : 0 < ε) :
vector_span ℝ (convex_body.ball x (le_of_lt εpos)).val = ⊤ :=
begin
  have : metric.ball (0 : V) ε ⊆ vector_span ℝ (metric.closed_ball x ε),
  {
    refine subset_trans metric.ball_subset_closed_ball _,
    simp only [vector_span_def],
    refine subset_trans _ submodule.subset_span,
    intros y hy,
    refine ⟨y + x, x, _, metric.mem_closed_ball_self (le_of_lt εpos), _⟩,
    {
      simpa only [mem_closed_ball_iff_norm, add_sub_cancel, sub_zero] using hy,
    },
    {
      simp only [vsub_eq_sub, add_sub_cancel],
    },
  },
  rw [←submodule.span_le] at this,
  simp only [convex_body.ball],
  apply le_antisymm le_top,
  apply le_trans _ this,
  replace := ball_spans_submodule ⊤ (0 : V) submodule.mem_top εpos,
  simp only [submodule.top_coe, set.inter_univ] at this,
  rw [this],
  exact le_refl ⊤,
end

lemma convex_body.full_dimensional_unit_ball :
vector_span ℝ (convex_body.unit_ball : convex_body V).val = ⊤ :=
convex_body.full_dimensional_ball zero_lt_one

-- This is tricky.
-- If K, L are full-dimensional, follows by polarization and the formula for the "unmixed" area.
-- The area measures of all sums appearing in the polarization formula are equal:
-- If K/L is not part of the sum, trivial
-- Otherwise, use the τ formula (Schneider, Theorem 4.2.3)
-- If K, L are not full-dimensional, apply the above special case
-- for K+B/L+B and B/B and use additivity of area
lemma area_determined_by_τ_add
{C : multiset (convex_body V)}
{K L : convex_body V}
(hC : is_area_coll (K ::ₘ C))
(hD : is_area_coll (L ::ₘ C))
{U : set (metric.sphere (0 : V) 1)}
(hU : measurable_set U)
(h : ∀ M : convex_body V, τ (K + M) U = τ (L + M) U) :
area (K ::ₘ C) U = area (L ::ₘ C) U :=
begin
  have : area ((K + convex_body.unit_ball) ::ₘ C) U = area ((L + convex_body.unit_ball) ::ₘ C) U,
  {
    apply area_determined_by_τ_add',
    {
      simpa only [is_area_coll, multiset.card_cons] using hC,
    },
    any_goals {
      apply convex_body.full_dimensional_add_left,
      exact convex_body.full_dimensional_unit_ball,
    },
    exact hU,
    {
      simp only [add_assoc],
      intro M,
      apply h,
    },
  },
  rw [area_cons_add, area_cons_add] at this, rotate,
  any_goals {
    simp only [is_almost_area_coll],
    simpa only [is_area_coll, multiset.card_cons, add_assoc] using hC,
  },
  simp only [measure_theory.finite_measure.coe_fn_add, pi.add_apply, add_left_inj] at this,
  exact this,
end

end bm