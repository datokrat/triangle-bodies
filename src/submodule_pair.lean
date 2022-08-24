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

lemma multiset.lift_submodules
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
{D : multiset (submodule ℝ E)}
(DC : D ⊑ₘ C.map (project_subspace E)) :
∃ F, F ⊑ₘ C ∧ D = F.map (project_subspace E) ∧
multiset_all (λ W, (proj E).ker ⊓ W = ⊥) F :=
begin
  admit,
end

noncomputable def span_singleton (x : V) : submodule ℝ V := submodule.span ℝ {x}