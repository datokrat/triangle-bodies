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

lemma multiset.lift_submodule_pair
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
{D : multiset (submodule_pair E)}
(CD : D.map submodule_pair.big = C.map (project_subspace E)) :
∃ F : multiset (submodule_pair V),
F.map (submodule_pair.big) = C ∧
F.map (submodule_pair.proj E) = D :=
begin
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := multiset.exists_join CD,
  obtain ⟨G, hG⟩ := F.exists_elementwise_preimage
    (submodule_pair.proj_keep_big E) _, rotate,
  {
    intros x xF,
    have : x.fst.small ≤ project_subspace E x.snd :=
      hF₃ x xF ▸ x.fst.le,
    --simp only [project_subspace] at this,
    --obtain ⟨y, yx, hy⟩ := this,
    refine ⟨⟨x.snd, ⟨x.fst.small.comap (proj E) ⊓ x.snd, _⟩⟩, _⟩,
    admit,
    admit,
    -- simp only [pointed_submodule.proj_keep_space, proj, hy, submodule.coe_mk],
    -- dsimp only,
    -- rw [prod.ext_iff, sigma.subtype_ext_iff],
    -- simp only [eq_self_iff_true, and_true],
    -- split,
    -- {rw [←hF₃ _ xF], refl},
    -- {refl},
  },
  refine ⟨G, _, _⟩,
  {
    admit,
  },
  {
    admit,
  },
end

noncomputable def span_singleton (x : V) : submodule ℝ V := submodule.span ℝ {x}

def pointed_submodule (V : Type)
[inner_product_space ℝ V] := Σ E : submodule ℝ V, E

def pointed_submodule.to_vector (M : pointed_submodule V) : V :=
M.snd.val

def pointed_submodule.to_space (M : pointed_submodule V) : submodule ℝ V :=
M.fst

def pointed_submodule.mem (M : pointed_submodule V) : M.to_vector ∈ M.to_space :=
M.snd.property

noncomputable def pointed_submodule.proj_keep_space (E : submodule ℝ V)
(M : pointed_submodule V) : pointed_submodule E × submodule ℝ V :=
begin
  refine ⟨⟨project_subspace E M.fst, _⟩, M.fst⟩,
  refine ⟨proj E M.snd, _⟩,
  exact submodule.mem_map_of_mem M.snd.property,
end

noncomputable def pointed_submodule.proj (E : submodule ℝ V)
(M : pointed_submodule V) : pointed_submodule E :=
begin
  refine ⟨project_subspace E M.fst, proj E M.snd, _⟩,
  exact submodule.mem_map_of_mem M.snd.property,
end

lemma multiset.lift_pointed
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
{D : multiset (pointed_submodule E)}
(CD : D.map pointed_submodule.to_space = C.map (project_subspace E)) :
∃ F : multiset (pointed_submodule V),
F.map (pointed_submodule.to_space) = C ∧
F.map (pointed_submodule.proj E) = D :=
begin
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := multiset.exists_join CD,
  obtain ⟨G, hG⟩ := F.exists_elementwise_preimage
    (pointed_submodule.proj_keep_space E) _, rotate,
  {
    intros x xF,
    have : x.fst.to_vector ∈ project_subspace E x.snd :=
      hF₃ x xF ▸ x.fst.mem,
    simp only [project_subspace, submodule.mem_map] at this,
    obtain ⟨y, yx, hy⟩ := this,
    refine ⟨⟨x.snd, ⟨y, yx⟩⟩, _⟩,
    simp only [pointed_submodule.proj_keep_space, proj, hy, submodule.coe_mk],
    dsimp only,
    rw [prod.ext_iff, sigma.subtype_ext_iff],
    simp only [eq_self_iff_true, and_true],
    split,
    {rw [←hF₃ _ xF], refl},
    {refl},
  },
  refine ⟨G, _, _⟩,
  {
    admit,
  },
  {
    admit,
  },
end