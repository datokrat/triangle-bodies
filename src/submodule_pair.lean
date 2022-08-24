import linalg
  analysis.inner_product_space.basic

variables {V : Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]



def submodule_pair (V : Type)
[inner_product_space ℝ V] := Σ E : submodule ℝ V, {F : submodule ℝ V // F ≤ E}

def submodule_pair.big (M : submodule_pair V) : submodule ℝ V :=
M.fst

def submodule_pair.small (M : submodule_pair V) : submodule ℝ V :=
M.snd.val

def submodule_pair.le (M : submodule_pair V) :
M.small ≤ M.big := M.snd.property


def multiset.elem_le (C D : multiset (submodule ℝ V)) :=
∃ CD : multiset (submodule_pair V),
CD.map submodule_pair.small = C ∧
CD.map submodule_pair.big = D

reserve infix ` ⊑ₘ `:50
notation C ` ⊑ₘ ` D := multiset.elem_le C D

lemma elem_le_refl (C : multiset (submodule ℝ V)) : C ⊑ₘ C :=
begin
  refine ⟨C.map (λ W, ⟨W, ⟨W, le_refl W⟩⟩), _, _⟩,
  {
    simp only [submodule_pair.small, multiset.map_map, multiset.map_id'],
  },
  {
    simp only [submodule_pair.big, multiset.map_map, multiset.map_id'],
  },
end

/- lemma elem_le_antisymm {C D : multiset (submodule ℝ V)}
(CD : C ⊑ₘ D) (DC : D ⊑ₘ C) : C = D := sorry -/

lemma elem_le_trans {C D E : multiset (submodule ℝ V)}
(CD : C ⊑ₘ D) (DE : D ⊑ₘ E) : C ⊑ₘ E :=
begin
  obtain ⟨CD, hCD⟩ := CD,
  obtain ⟨DE, hDE⟩ := DE,
  obtain rfl := hDE.1,
  obtain ⟨T, TCD, TDE⟩ := multiset.exists_join' hCD.2,
  refine ⟨T.map (λ t, ⟨t.val.snd.big, ⟨t.val.fst.small, _⟩⟩), _⟩,
  {
    refine le_trans t.val.fst.le _,
    rw [t.property],
    exact t.val.snd.le,
  },
  {
    obtain rfl := TCD,
    obtain rfl := TDE,
    simp only [subtype.val_eq_coe, multiset.map_map, function.comp_app, eq_self_iff_true, true_and] at hCD hDE,
    simp only [submodule_pair.small, submodule_pair.big, subtype.val_eq_coe, multiset.map_map, function.comp_app, subtype.coe_mk],
    exact ⟨hCD.1, hDE⟩,
  },
end

lemma card_eq_of_elem_le {C D : multiset (submodule ℝ V)}
(CD : C ⊑ₘ D) : C.card = D.card :=
begin
  obtain ⟨CD, ⟨rfl, rfl⟩⟩ := CD,
  simp only [multiset.card_map],
end

lemma cons_elem_le_cons_head
{U W : submodule ℝ V} {C : multiset (submodule ℝ V)}
(h : U ≤ W) : U ::ₘ C ⊑ₘ W ::ₘ C :=
begin
  obtain ⟨X, ⟨hX₁, hX₂⟩⟩ := elem_le_refl C,
  refine ⟨⟨W, ⟨U, h⟩⟩ ::ₘ X, _, _⟩,
  {
    simp only [submodule_pair.small, subtype.val_eq_coe, multiset.map_cons, subtype.coe_mk, multiset.cons_inj_right],
    exact hX₁,
  },
  {
    simp only [submodule_pair.big, multiset.map_cons, multiset.cons_inj_right],
    exact hX₂,
  },
end

lemma add_elem_le_add {C D E F: multiset (submodule ℝ V)}
(CE : C ⊑ₘ E) (DF : D ⊑ₘ F) : C + D ⊑ₘ E + F :=
begin
  obtain ⟨X, ⟨rfl, rfl⟩⟩ := CE,
  obtain ⟨Y, ⟨rfl, rfl⟩⟩ := DF,
  refine ⟨X + Y, _, _⟩,
  all_goals {simp only [multiset.map_add]},
end

lemma add_elem_le_add_left {C D E : multiset (submodule ℝ V)}
(DE : D ⊑ₘ E) : C + D ⊑ₘ C + E :=
add_elem_le_add (elem_le_refl _) DE

lemma add_elem_le_add_right {C D E : multiset (submodule ℝ V)}
(DE : D ⊑ₘ E) : D + C ⊑ₘ E + C :=
add_elem_le_add DE (elem_le_refl _)

noncomputable def submodule_pair.proj_keep_big (E : submodule ℝ V)
(M : submodule_pair V) : submodule_pair E × submodule ℝ V :=
begin
  refine ⟨⟨project_subspace E M.big, _⟩, M.big⟩,
  refine ⟨project_subspace E M.small, _⟩,
  simp only [project_subspace],
  exact submodule.map_mono M.le,
end

noncomputable def submodule_pair.proj (E : submodule ℝ V)
(M : submodule_pair V) : submodule_pair E :=
begin
  refine ⟨project_subspace E M.big, project_subspace E M.small, _⟩,
  simp only [project_subspace],
  exact submodule.map_mono M.le,
end

--MOVETO linalg.lean
lemma exists_equiv_to_image
{W : Type} [inner_product_space ℝ W] [finite_dimensional ℝ V]
(E : submodule ℝ V)
(f : V →ₗ[ℝ] W) :
∃ (T : submodule ℝ V), T ≤ E ∧ T ⊓ f.ker = ⊥ ∧ T.map f = E.map f :=
begin
  let g := (f.dom_restrict E).range_restrict,
  -- linear_map.range_range_restrict
  obtain ⟨h, hh⟩ := g.exists_right_inverse_of_surjective (linear_map.range_range_restrict _),
  let H := h.range,
  refine ⟨H.map E.subtype, submodule.map_subtype_le _ _, _, _⟩,
  {
    rw [submodule.eq_bot_iff],
    intros x hx,
    rw [submodule.mem_inf, submodule.mem_map] at hx,
    obtain ⟨⟨y, yH, rfl⟩, hx⟩ := hx,
    rw [linear_map.mem_range] at yH,
    obtain ⟨z, rfl⟩ := yH,
    rw [linear_map.mem_ker, submodule.coe_subtype] at hx,
    simp only [submodule.coe_subtype, submodule.coe_eq_zero],
    simp only [linear_map.ext_iff, linear_map.id_coe, id.def] at hh,
    replace hh := hh z,
    simp only [g, linear_map.comp_apply, linear_map.range_restrict] at hh,
    replace hh := congr_arg (submodule.subtype _) hh,
    simp only [submodule.coe_subtype, linear_map.cod_restrict_apply, linear_map.dom_restrict_apply] at hh,
    rw [hh] at hx,
    have : (0 : W) = ↑(0 : (f.dom_restrict E).range) := rfl,
    rw [this] at hx,
    replace hx := subtype.coe_injective hx,
    rw [hx],
    simp only [map_zero],
  },
  {
    simp only [H, linear_map.range_eq_map, ←submodule.map_comp, ←linear_map.dom_restrict],
    rw [←linear_map.comp_assoc],
    ext,
    simp only [submodule.mem_map],
    split,
    {
      rintro ⟨y, -, rfl⟩,
      refine ⟨E.subtype.comp h y, _⟩,
      simp only [linear_map.comp_apply, submodule.coe_subtype],
      simp only [submodule.coe_mem, eq_self_iff_true, and_self],
    },
    {
      rintro ⟨y, yE, rfl⟩,
      refine ⟨⟨(f.dom_restrict E) ⟨y, yE⟩, linear_map.mem_range_self _ _⟩, _, _⟩,
      {
        apply submodule.mem_top,
      },
      simp only [g, linear_map.dom_restrict, linear_map.ext_iff] at hh,
      simp only [linear_map.comp_apply, linear_map.range_restrict] at hh ⊢,
      replace hh := congr_arg (submodule.subtype _) (hh ⟨(f.dom_restrict E ⟨y, yE⟩), linear_map.mem_range_self _ _⟩),
      simp only [submodule.coe_subtype, linear_map.cod_restrict_apply] at hh,
      simp only [linear_map.id_coe, id.def, linear_map.dom_restrict_apply, submodule.coe_subtype] at hh ⊢,
      rw [hh, submodule.coe_mk, submodule.coe_mk],
    },
  },
end

lemma exists_dim_eq_dim_image
{W : Type} [inner_product_space ℝ W] [finite_dimensional ℝ V]
{E : submodule ℝ V}
(f : V →ₗ[ℝ] W) :
∃ T : submodule ℝ V, T ≤ E ∧ f.ker ⊓ T = ⊥ ∧ T.map f = E.map f :=
begin
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := exists_equiv_to_image E f,
  refine ⟨T, hT₁, _, hT₃⟩,
  {
    rw [inf_comm, hT₂],
  },
end

lemma exists_dim_eq_dim_image'
{W : Type} [inner_product_space ℝ W] [finite_dimensional ℝ V]
{E : submodule ℝ V} {F : submodule ℝ W}
(f : V →ₗ[ℝ] W)
(FE : F ≤ E.map f) :
∃ T : submodule ℝ V, T ≤ E ∧ f.ker ⊓ T = ⊥ ∧ T.map f = F :=
begin
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := exists_equiv_to_image E f,
  refine ⟨T ⊓ F.comap f, _, _, _⟩,
  {
    exact le_trans inf_le_left hT₁,
  },
  {
    rw [inf_comm] at hT₂,
    refine le_antisymm _ bot_le,
    refine le_trans (inf_le_inf_left _ inf_le_left) _,
    exact le_of_eq hT₂,
  },
  {
    apply le_antisymm,
    {
      refine le_trans (submodule.map_mono inf_le_right) _,
      apply submodule.map_comap_le,
    },
    {
      rw [←hT₃] at FE,
      intros f hf,
      have := FE hf,
      rw [submodule.mem_map] at this ⊢,
      obtain ⟨y, yT, rfl⟩ := this,
      refine ⟨y, _, rfl⟩,
      rw [submodule.mem_inf, submodule.mem_comap],
      exact ⟨yT, hf⟩,
    },
  },
end

-- MOVETO multiset.lean
lemma multiset.exists_of_exists_elementwise {α β: Type}
{C : multiset α}
{p : α → β → Prop}
(h : multiset_all (λ a, ∃ b : β, p a b) C) :
∃ D : multiset ({x : α × β // p x.fst x.snd }), C = D.map (λ x, x.val.fst) :=
begin
  induction C using pauls_multiset_induction with C a ih,
  {
    refine ⟨0, _⟩,
    rw [multiset.map_zero],
  },
  {
    obtain ⟨b, pab⟩ := h a (multiset.mem_cons_self _ _),
    obtain ⟨D, hD⟩ := ih (multiset.all_of_le (multiset.le_cons_self _ _) h),
    refine ⟨⟨⟨a, b⟩, pab⟩ ::ₘ D, _⟩,
    simp only [hD, subtype.val_eq_coe, multiset.map_cons, subtype.coe_mk, multiset.cons_inj_right],
  },
end

lemma multiset.lift_submodules
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
{D : multiset (submodule ℝ E)}
(DC : D ⊑ₘ C.map (project_subspace E)) :
∃ F, F ⊑ₘ C ∧ D = F.map (project_subspace E) ∧
multiset_all (λ W, (proj E).ker ⊓ W = ⊥) F :=
begin
  obtain ⟨X, ⟨hX', hX⟩⟩ := DC,
  obtain ⟨Y, YX, YC⟩ := multiset.exists_join' hX,
  let Z : multiset {pr : submodule ℝ V × submodule ℝ E // pr.snd ≤ project_subspace E pr.fst} :=
  Y.map (λ pr, ⟨⟨pr.val.snd, pr.val.fst.small⟩, _⟩), rotate,
  {
    rw [←pr.property],
    exact pr.val.fst.le,
  },
  have ZC : C = Z.map (λ x, x.val.fst),
  {
    rw [←YC, multiset.map_map],
  },
  have ZD : D = Z.map (λ x, x.val.snd),
  {
    rw [←hX', ←YX, multiset.map_map, multiset.map_map],
  },
  clear_value Z,
  clear' X hX' hX Y YX YC,
  have : multiset_all (λ z : {z : submodule ℝ V × submodule ℝ E // z.snd ≤ project_subspace E z.fst},
  ∃ U : submodule ℝ V, U ≤ z.val.fst ∧ project_subspace E U = z.val.snd ∧ (proj E).ker ⊓ U = ⊥) Z,
  {
    intros z hz,
    have := z.property,
    simp only [project_subspace] at this,
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := exists_dim_eq_dim_image' _ this,
    exact ⟨U, hU₁, hU₃, hU₂⟩,
  },
  obtain ⟨W, hW⟩ := multiset.exists_of_exists_elementwise this,
  let K : multiset (submodule_pair V) := W.map (λ w, ⟨w.val.fst.val.fst, ⟨w.val.snd, w.property.1⟩⟩),
  have KC: C = K.map (λ k, k.fst),
  {
    simp only [ZC, hW, multiset.map_map],
  },
  refine ⟨K.map (λ k, k.snd.val), _, _, _⟩,
  {
    refine ⟨K, rfl, _⟩,
    {
      rw [KC],
      refl,
    },
  },
  {
    rw [ZD, hW],
    simp only [subtype.val_eq_coe, multiset.map_map, function.comp_app, subtype.coe_mk],
    congr, funext x,
    exact x.property.2.1.symm,
  },
  {
    intros W hW,
    rw [multiset.mem_map] at hW,
    obtain ⟨k, kK, rfl⟩ := hW,
    rw [multiset.mem_map] at kK,
    obtain ⟨w, wW, rfl⟩ := kK,
    exact w.property.2.2,
  },
end

noncomputable def span_singleton (x : V) : submodule ℝ V := submodule.span ℝ {x}