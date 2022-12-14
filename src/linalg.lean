import multiset data.fintype.basic linear_algebra.dimension
  set_pi arithmetic measure_theory.measure.measure_space_def
  data.multiset
  linear_algebra.finite_dimensional
  analysis.inner_product_space.projection
  analysis.inner_product_space.dual
  data.multiset.basic
  data.nat.basic

open_locale pointwise

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]


instance submodule.complete_space (E : submodule ℝ V) : complete_space E :=
is_complete.complete_space_coe (submodule.complete_of_finite_dimensional E)


noncomputable def vector_orth (u : V) : submodule ℝ V :=
(submodule.span ℝ ({u} : set V))ᗮ

lemma mem_vector_orth {u : V} {x : V} :
x ∈ vector_orth u ↔ ⟪x, u⟫_ℝ = 0 :=
begin
  simp only [vector_orth, submodule.mem_orthogonal, submodule.mem_span_singleton],
  split,
  {
    intro h,
    rw [real_inner_comm],
    refine h u _,
    exact ⟨1, one_smul _ _⟩,
  },
  {
    rintro h u ⟨a, rfl⟩,
    simp only [inner_smul_left, is_R_or_C.conj_to_real, mul_eq_zero],
    right, rw [real_inner_comm], exact h,
  }
end

noncomputable abbreviation dim := finite_dimensional.finrank ℝ
abbreviation diff (A : set V) := A -ᵥ A

noncomputable def common_dimension
  (C : multiset (set V)) : ℕ :=
  finite_dimensional.finrank ℝ (vector_span ℝ C.sum)

lemma mem_of_mem_of_generator
  {A : set V} {x : V} (h : x ∈ A) : x ∈ submodule.span ℝ A :=
begin
  refine (set.mem_of_mem_of_subset h _ : x ∈ ↑(submodule.span ℝ A)),
  apply submodule.subset_span,
end

lemma vector_span_zero
  (A : set V) (h : (0 : V) ∈ A) : vector_span ℝ A = submodule.span ℝ A :=
begin
  simp only [vector_span],
  apply submodule.complete_lattice.le_antisymm,
  begin
    refine submodule.span_le.mpr (_ : A -ᵥ A ⊆ ↑(submodule.span ℝ A)),
    rw [set.subset_def],
    intros x hmem,
    rcases set.mem_sub.mp hmem with ⟨a, b, ⟨ha, hb, rfl⟩⟩,
    refine (submodule.sub_mem _ _ _ : a - b ∈ submodule.span ℝ A),
    exact  mem_of_mem_of_generator ha,
    exact mem_of_mem_of_generator hb,
  end,
  begin
    apply submodule.span_mono,
    simp only [has_subset.subset, has_le.le],
    intros x x_in_A,
    refine set.mem_sub.mpr ⟨x, 0, _⟩,
    simp [h, x_in_A],
  end
end

lemma exists_zero_translate
  (A : set V) : ∃ x : V, A + {x} = ∅ ∨ (0 : V) ∈ (A + {x}) :=
begin
  by_cases A = ∅,
  begin
    rcases h with rfl,
    simp,
  end,
  begin
    have := set.ne_empty_iff_nonempty.mp h,
    rcases set.nonempty_def.mp this with ⟨y, hy⟩,
    refine ⟨-y, or.inr _⟩,
    rw [show 0 = y + (-y), by simp],
    apply set.mem_add.mpr,
    tauto,
  end
end

lemma submodule_sum_eq_sup
  (E F : submodule ℝ V) : E + F = E ⊔ F := rfl

lemma zero_subset_submodule (E : submodule ℝ V) : {(0 : V)} ⊆ (E : set V) :=
begin
  simp,
end

lemma set_add_zero (A : set V) : A + {(0 : V)} = A :=
begin
  simp,
end

lemma set_add_le_add_right (A B C : set V) (h : B ⊆ C) : A + B ⊆ A + C :=
begin
  rintro x ⟨a, b, ⟨ha, hb, rfl⟩⟩,
  refine ⟨a, b, _⟩, -- exists.intro; interesting that it works
  tauto,
end

lemma set_add_le_add_left (A B C : set V) (h : A ⊆ B) : A + C ⊆ B + C :=
begin
  rintro x ⟨a, b, ⟨ha, hb, rfl⟩⟩,
  refine ⟨a, b, _⟩, -- exists.intro; interesting that it works
  tauto,
end

lemma set_le_add_right (E F : set V) (h : (0: V) ∈ F) : E ⊆ E + F :=
begin
  conv {to_lhs, rw [←@set_add_zero V _ _ E]},
  apply_rules [set_add_le_add_right, set.singleton_subset_iff.mpr h],
end

lemma set_le_add_left (E F : set V) (h : (0: V) ∈ F) : E ⊆ F + E :=
begin
  rw [add_comm],
  exact set_le_add_right E F h,
end

lemma submodule_sum_eq_mink_sum
  {E F : submodule ℝ V} : ((E + F : submodule ℝ V) : set V) = (E : set V) + (F : set V) :=
begin
  have E_le : E ≤ E + F := by simp,
  have F_le : F ≤ E + F := by simp,
  apply le_antisymm,
  begin
    let G := submodule.span ℝ ((E : set V) + (F : set V)),
    have inG : E + F ≤ G :=
    begin
      have : Π(H K : submodule ℝ V), (H : set V) ⊆ (H : set V) + (K : set V) :=
      begin
        intros H K,
        conv {
          to_lhs,
          rw [←@set_add_zero V _ _ H],
        },
        apply_rules [set_add_le_add_right, zero_subset_submodule],
      end,
      begin
        refine complete_lattice.sup_le E F G _ _,
        begin
          rw [←submodule.span_eq E],
          apply submodule.span_mono,
          refine set_le_add_right E F _,
          apply submodule.zero_mem,
        end,
        begin
          rw [←submodule.span_eq F],
          apply submodule.span_mono,
          refine set_le_add_left F E _,
          apply submodule.zero_mem,
        end
      end
    end,
    have G_EF : (G : set V) ≤ (E : set V) + (F : set V) :=
    begin
      intros x hx,
      refine submodule.span_induction hx _ _ _ _,
      begin
        tauto,
      end,
      begin
        refine ⟨0, 0, ⟨_, _, _⟩⟩,
        apply submodule.zero_mem,
        apply submodule.zero_mem,
        simp,
      end,
      begin
        rintro x y ⟨ex, fx, ⟨hex, hfx, rfl⟩⟩ ⟨ey, fy, ⟨hey, hfy, rfl⟩⟩,
        refine ⟨ex + ey, fx + fy, _, _, _⟩,
        apply submodule.add_mem E hex hey,
        apply submodule.add_mem F hfx hfy,
        abel,
      end,
      begin
        rintro a x ⟨e, f, ⟨he, hf, rfl⟩⟩,
        refine ⟨a • e, a • f, _, _, _⟩,
        apply submodule.smul_mem E a he,
        apply submodule.smul_mem F a hf,
        simp,
      end
    end,
    refine le_trans inG G_EF,
  end,
  begin
    rintro x ⟨e, f, he, hf, rfl⟩,
    refine submodule.add_mem (E + F) _ _,
    exact E_le he,
    exact F_le hf,
  end
end

lemma add_subset_submodule
  {A B : set V} {E : submodule ℝ V} (hA : A ⊆ E) (hB : B ⊆ E): A + B ⊆ E :=
begin
  intros s hs,
  rcases set.mem_add.mp hs with ⟨a, b, ⟨ha, hb, rfl⟩⟩,
  apply submodule.add_mem,
  exact @set.mem_of_mem_of_subset _ _ _ _ ha hA,
  exact @set.mem_of_mem_of_subset _ _ _ _ hb hB,
end

lemma submodule_subset_of_le
  {E F : submodule ℝ V} : E ≤ F = ((E : set V) ⊆ (F : set V)) :=
begin
  apply propext,
  apply iff.intro,
  all_goals {
    intros h e he,
    exact h he,
  }
end

lemma set_ABAB_AABB
  {A B : set V} : (A + B) - (A + B) = (A - A) + (B - B) :=
begin
  apply le_antisymm,
  all_goals {
    rintro _ ⟨_, _, ⟨a, b, ha, hb, rfl⟩, ⟨c, d, hc, hd, rfl⟩, rfl⟩,
  },
  begin
    refine ⟨a - c, b - d, ⟨a, c, _, _, rfl⟩, ⟨b, d, _, _, rfl⟩, _⟩,
    any_goals {assumption},
    abel,
  end,
  begin
    refine ⟨a + c, b + d, ⟨a, c, _, _, rfl⟩, ⟨b, d, _, _, rfl⟩, _⟩,
    any_goals {assumption},
    abel,
  end
end

lemma zero_mem_diff_of_nonempty
  {A : set V} (ne : A.nonempty) : (0 : V) ∈ A - A :=
begin
  letI ne' := set.nonempty.to_subtype ne,
  rcases set.exists_mem_of_nonempty A with ⟨⟨x, hx⟩, -⟩,
  rw [show (0 : V) = x - x, by simp],
  refine set.sub_mem_sub _ _,
  all_goals {assumption},
end

lemma nonempty_sets_of_nonempty_sum {A B : set V}
(h : set.nonempty (A + B)) : set.nonempty A ∧ set.nonempty B :=
begin
  rcases h with ⟨x, ⟨a, b, ha, hb, rfl⟩⟩,
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩,
end

lemma multiset_sum_nonempty_of_elements {A : multiset (set V)}
(h : ∀ a : set V, a ∈ A → a.nonempty): A.sum.nonempty :=
begin
  unfreezingI {
    induction A using pauls_multiset_induction with as b ih,
    {
      simp [set.zero_nonempty],
    },
    {
      simp only [multiset.sum_cons],
      apply set.add_nonempty.mpr,
      split,
      {
        refine h b _,
        simp,
      },
      {
        apply ih,
        intros c hc,
        refine h c _,
        simp [hc],
      }
    }
  }
end

lemma diff_set_le_add (A B : set V) (Bne : set.nonempty B) :
diff A ⊆ diff (B + A) :=
begin
  rcases Bne with ⟨b, hb⟩,
  rintro d ⟨a, a', ha, ha', rfl⟩,
  refine ⟨b + a, b + a', ⟨b, a, _⟩, ⟨b, a', _⟩, _⟩,
  any_goals {simp},
  all_goals {tauto},
end

def multiset_all_nonempty (F : multiset (set V))
:= ∀ x ∈ F, set.nonempty x

lemma all_nonempty_of_le {F G : multiset (set V)}
(h : F ≤ G) : multiset_all_nonempty G → multiset_all_nonempty F :=
begin
  intros neG x hx,
  refine neG x _,
  exact multiset.mem_of_le h hx,
end

lemma diff_multiset_sum_mono {F G : multiset (set V)}
(h : F ≤ G) (hne : ∀ x ∈ G, set.nonempty x) :
diff F.sum ⊆ diff G.sum :=
begin
  rcases multiset.le_iff_exists_add.mp h with ⟨E, rfl⟩,
  simp only [multiset.sum_add],
  rw [add_comm],
  refine diff_set_le_add F.sum E.sum _,
  refine multiset_sum_nonempty_of_elements _,
  intros a ha,
  refine hne a _,
  apply multiset.mem_add.mpr,
  tauto,
end

-- I almost forgot that the sets must not be empty...
lemma vector_span_sum_commute
  (A B : set V) (Ane : A.nonempty) (Bne : B.nonempty) : vector_span ℝ (A + B) = (vector_span ℝ A) + (vector_span ℝ B) :=
begin
  apply submodule.complete_lattice.le_antisymm,
  begin
    simp only [vector_span],
    refine submodule.span_le.mpr _,
    rintros x ⟨ab1, ab2,
      ⟨⟨a1, b1, ⟨ha1, hb1, rfl⟩⟩, ⟨a2, b2, ⟨ha2, hb2, rfl⟩⟩, rfl⟩⟩,
      have : a1 + b1 - (a2 + b2) = a1 - a2 + (b1 - b2) := by abel,
      simp only [has_vsub.vsub, this],
      rw [submodule_sum_eq_mink_sum],
      apply set.add_mem_add,
      begin
        refine submodule.subset_span _,
        refine ⟨a1, a2, ha1, ha2, rfl⟩,
      end,
      begin
        refine submodule.subset_span _,
        refine ⟨b1, b2, hb1, hb2, rfl⟩,
      end
  end,
  begin
    simp only [submodule_subset_of_le, submodule_sum_eq_mink_sum],
    rintro x ⟨a, b, ha, hb, rfl⟩,
    change a + b ∈ vector_span ℝ (A + B),
    simp only [vector_span] at *,
    simp only [set_vsub_eq_sub] at *,
    simp only [set_ABAB_AABB],
    refine submodule.add_mem _ _ _,
    all_goals {refine submodule.span_mono _ (by assumption)}, --wow, it works!
    begin
      refine set_le_add_right _ _ _,
      exact zero_mem_diff_of_nonempty Bne,
    end,
    begin
      refine set_le_add_left _ _ _,
      exact zero_mem_diff_of_nonempty Ane,
    end
  end
end


def semicritical (C : multiset (set V)) :=
  ∀ τ : multiset (set V), τ ≤ C → common_dimension τ ≥ τ.card

def project_set (E : submodule ℝ V): set V → set E :=
λ A, orthogonal_projection E '' A

def project_collection (E : submodule ℝ V) (C : multiset (set V)) :
multiset (set E) :=
C.map (project_set E)

lemma minksum_proj_commute (E : submodule ℝ V) (A B : set V) :
project_set E (A + B) = project_set E A + project_set E B :=
begin
  apply set.ext,
  intro x,
  simp only [project_set, set.mem_add, set.mem_image] at *,
  apply iff.intro,
  begin
    intro h,
    rcases h with ⟨-, ⟨⟨a, b, ⟨ha, hb, rfl⟩⟩, rfl⟩⟩,
    rw [continuous_linear_map.map_add],
    tauto,
  end,
  begin
    intro h,
    rcases h with ⟨pa, pb, ⟨⟨a, ⟨ha, rfl⟩⟩, ⟨b, ⟨hb, rfl⟩⟩, rfl⟩⟩,
    rw [←continuous_linear_map.map_add],
    tauto,
  end
end

lemma minksum_proj_commute_list (E : submodule ℝ V) (C : list (set V)) :
project_set E C.sum = (C.map $ project_set E).sum :=
begin
  induction C,
  begin
    simp [project_set],
    trivial,
  end,
  begin
    simp [←C_ih, minksum_proj_commute],
  end,
end

lemma minksum_proj_commute_multiset (E : submodule ℝ V) (C : multiset (set V)) :
project_set E C.sum = (project_collection E C).sum :=
begin
  induction C,
  begin
    simp only [multiset.quot_mk_to_coe'', project_collection, multiset.coe_map, multiset.coe_sum],
    apply minksum_proj_commute_list,
  end,
  trivial,
end

lemma subcollection_semicritical {C D: multiset (set V)} (hDC : D ≤ C) (hsc : semicritical C) :
semicritical D :=
begin
  intro S,
  intro hSD,
  apply hsc,
  apply le_trans hSD hDC,
end

def cart_prod {V W : Type} (A : set V) (B : set W) : set (V × W) :=
{ x : V × W | x.fst ∈ A ∧ x.snd ∈ B }

lemma set_image2_eq_image_times {V W : Type} {A B : set V}
{f : V → V → W} : set.image2 f A B = set.image (function.uncurry f) (cart_prod A B) :=
begin
  simp [set.image2, set.image, function.uncurry, cart_prod],
  apply le_antisymm,
  {
    rintro _ ⟨a, ⟨ha, b, hb, h⟩⟩,
    refine ⟨a, b, ⟨ha, hb⟩, h⟩,
  },
  {
    rintro _ ⟨a, b, ⟨ha, hb⟩, h⟩,
    exact ⟨a, ha, b, hb, h⟩,
  }
end

lemma set_sum_project_commute (A B : set V) (E : submodule ℝ V) :
project_set E (A + B) = (project_set E A) + (project_set E B) :=
begin
  simp only [project_set],
  apply le_antisymm,
  {
    rintro e ⟨x, ⟨⟨a, b, ha, hb, rfl⟩, rfl⟩⟩,
    rw [(orthogonal_projection E).map_add],
    apply set.add_mem_add,
    {
      refine ⟨a, _⟩,
      tauto,
    },
    {
      refine ⟨b, _⟩,
      tauto,
    }
  },
  {
    rintro e ⟨pa, pb, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, rfl⟩,
    rw [←(orthogonal_projection E).map_add],
    refine ⟨a+b, _⟩,
    split,
    any_goals {refl},
    apply set.add_mem_add,
    all_goals {assumption},
  }
end

-- maybe generalizable to the situation when add commutes with any f
lemma multiset_sum_project_set_commute (C : multiset (set V)) (E : submodule ℝ V) :
project_set E C.sum = (C.map (project_set E)).sum :=
begin
  induction C using pauls_multiset_induction with C c ih,
  {
    simp only [project_set, multiset.sum_zero, set.image_zero, map_zero, multiset.map_zero],
    trivial,
  },
  {
    simp only [multiset.sum_cons, set_sum_project_commute],
    simp only [multiset.map_cons, multiset.sum_cons],
    rw [ih],
  }
end

noncomputable def proj (E : submodule ℝ V) := (orthogonal_projection E).to_linear_map

lemma ker_of_orthogonal_projection (E : submodule ℝ V) : (proj E).ker = Eᗮ :=
begin
  apply le_antisymm,
  {
    rintro x hx,
    have hx' : orthogonal_projection E x = 0 := hx,
    rw [show x = x - orthogonal_projection E x, by simp [hx']],
    apply sub_orthogonal_projection_mem_orthogonal,
  },
  {
    rintro x hx,
    refine orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hx,
  }
end

lemma ker_of_complementary_orthogonal_projection (E : submodule ℝ V) : (proj Eᗮ).ker = E :=
begin
  conv {to_rhs, rw [←submodule.orthogonal_orthogonal E]},
  apply ker_of_orthogonal_projection,
end

lemma surjective_orthogonal_projection (E : submodule ℝ V): function.surjective (proj E) :=
begin
  rintro e,
  refine ⟨e, _⟩,
  simp only [proj, continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe,
  orthogonal_projection_mem_subspace_eq_self],
end

lemma range_of_orthogonal_projection (E : submodule ℝ V): (proj E).range = ⊤ :=
begin
  apply linear_map.range_eq_top.mpr,
  simp only [proj, continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe],
  apply surjective_orthogonal_projection,
end

lemma dim_add_dim_orthogonal (E : submodule ℝ V) :
dim E + dim Eᗮ = dim V :=
begin
  have : dim E = dim (⊤ : submodule ℝ E) := finrank_top.symm,
  rw [←ker_of_orthogonal_projection E, this, ←range_of_orthogonal_projection E],
  apply linear_map.finrank_range_add_finrank_ker,
end

def submodule_inclusion (W : submodule ℝ V) : W →ₗ[ℝ] V :=
begin
  refine ⟨_, _, _⟩,
  exact (coe : W → V),
  tauto,
  tauto,
end

lemma submodule_inclusion_injective {W : submodule ℝ V} : function.injective (submodule_inclusion W) :=
begin
  rintro x y,
  simp [submodule_inclusion],
end

def submodule_to_submodule_inclusion {S T : submodule ℝ V} (h : S ≤ T)
: S →ₗ[ℝ] T :=
begin
  refine ⟨_, _, _⟩,
  {
    rintro x,
    exact ⟨x.1, h x.2⟩,
  },
  {tauto},
  {tauto},
end

def submodule_to_submodule_inclusion_injective {S T : submodule ℝ V} (h : S ≤ T)
: function.injective (submodule_to_submodule_inclusion h) :=
begin
  intros x y,
  simp [submodule_to_submodule_inclusion],
end

noncomputable def submodule_submodule_to_submodule {W : submodule ℝ V} (U : submodule ℝ W) :
submodule ℝ V := submodule.span ℝ ((coe : W → V) '' U)

lemma submod_submod_eq_submod_set {W : submodule ℝ V} (U : submodule ℝ W) :
(submodule_submodule_to_submodule U : set V) = ((coe : W → V) '' U) :=
begin
  apply le_antisymm,
  {
    rintro x hx,
    refine submodule.span_induction hx _ _ _ _,
    {
      tauto,
    },
    {
      simp only [set.mem_image, set_like.mem_coe, submodule.coe_eq_zero, exists_eq_right, submodule.zero_mem],
    },
    {
      rintro y z ⟨py, hyU, rfl⟩ ⟨pz, hzU, rfl⟩,
      refine ⟨py + pz, _⟩,
      split,
      {
        apply submodule.add_mem _ hyU hzU,
      },
      simp only [submodule.coe_add],
    },
    {
      rintro a y ⟨py, pyU, rfl⟩,
      refine ⟨a • py, _⟩,
      split,
      {
        apply submodule.smul_mem _ a pyU,
      },
      simp only [submodule.coe_smul_of_tower],
    },
  },
  {
    apply submodule.subset_span,
  }
end

def submodule_submodule_mapsto_submodule {W : submodule ℝ V} (U : submodule ℝ W) :
U →ₗ[ℝ] submodule_submodule_to_submodule U :=
begin
  refine ⟨_, _, _⟩,
  {
    rintro v,
    refine ⟨v.1.1, _⟩,
    simp only [submodule_submodule_to_submodule],
    refine submodule.subset_span _,
    refine ⟨v.1, _⟩,
    simp,
  },
  {
    tauto,
  },
  {
    tauto,
  },
end

lemma sub_inequality_from_add_inequality
{a b c : ℕ} : a + b ≥ c → a ≥ c - b :=
begin
  exact tsub_le_iff_right.mpr,
end

lemma image_eq_range_dom_restrict
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂] [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
  W.map f = (f.dom_restrict W).range :=
begin
  apply le_antisymm,
  {
    rintro y ⟨x, ⟨hx, rfl⟩⟩,
    rw [show f x = f.dom_restrict W ⟨x, hx⟩, by refl],
    apply linear_map.mem_range_self,
  },
  {
    rintro y ⟨⟨x, hx⟩, rfl⟩,
    rw [show f.dom_restrict W ⟨x, hx⟩ = f x, by refl],
    apply submodule.mem_map_of_mem hx,
  }
end

lemma map_ker_restrict
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
(f.dom_restrict W).ker.map W.subtype = f.ker ⊓ W :=
begin
  unfold linear_map.dom_restrict,
  rw [linear_map.ker_comp],
  apply le_antisymm,
  {
    refine le_inf _ _,
    {apply submodule.map_comap_le},
    {
      conv {to_rhs, rw [←submodule.range_subtype W]},
      apply linear_map.map_le_range,
    }
  },
  {
    rintro x ⟨hxf, hxW⟩,
    refine ⟨⟨x, hxW⟩, _⟩,
    simp only [hxf, submodule.comap_coe, submodule.coe_subtype, set.mem_preimage, submodule.coe_mk, eq_self_iff_true, and_self],
  }
end

def ker_restrict_equiv
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
(f.dom_restrict W).ker ≃ₗ[K] (f.ker ⊓ W : submodule K V) :=
begin
  rw [←map_ker_restrict],
  apply submodule.equiv_subtype_map,
end


def ker_dom_restrict_inclusion
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂] [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
  (f.dom_restrict W).ker →ₗ[K] f.ker :=
begin
  let g := W.subtype,
  let h := (f.dom_restrict W).ker.subtype,
  let k := g ∘ₗ h,
  refine k.cod_restrict f.ker _,
  rintro ⟨c, hc⟩,
  exact hc,
end

def ker_dom_restrict_inclusion_injective
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂] [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
function.injective (ker_dom_restrict_inclusion f W) :=
begin
  have : function.injective (coe : f.ker → V) := subtype.coe_injective,
  rintro x y,
  unfold ker_dom_restrict_inclusion,
  simp only, -- remove let
  intro h,
  replace h := congr_arg (coe : f.ker → V) h,
  simp only [linear_map.cod_restrict_apply, linear_map.comp_apply] at h,
  simp only [submodule.coe_subtype] at h,
  exact subtype.coe_injective (subtype.coe_injective h),
end

lemma subspace_rank_nullity
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂] [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
finite_dimensional.finrank K (W.map f) + finite_dimensional.finrank K (f.ker ⊓ W : submodule K V)
= finite_dimensional.finrank K W :=
begin
  let g := f.dom_restrict W,
  rw [image_eq_range_dom_restrict],
  have := ker_restrict_equiv f W,
  rw [←linear_equiv.finrank_eq this],
  apply linear_map.finrank_range_add_finrank_ker g,
end

lemma dim_image_le_self
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂] [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
finite_dimensional.finrank K (W.map f) ≤ finite_dimensional.finrank K W :=
begin
  rw [←subspace_rank_nullity f W],
  simp only [le_add_iff_nonneg_right, zero_le'],
end

lemma dim_image_ge_dim_domain_sub_dim_ker
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂] [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
  finite_dimensional.finrank K (W.map f) ≥ finite_dimensional.finrank K W - finite_dimensional.finrank K f.ker :=
begin
  let g := f.dom_restrict W,
  have hrange : W.map f = g.range := image_eq_range_dom_restrict f W,
  have hker : finite_dimensional.finrank K g.ker ≤ finite_dimensional.finrank K f.ker :=
  begin
    let incl : g.ker →ₗ[K] f.ker := ker_dom_restrict_inclusion f W,
    have incl_inj : function.injective incl := ker_dom_restrict_inclusion_injective f W,
    apply linear_map.finrank_le_finrank_of_injective incl_inj,
  end,
  have rn := linear_map.finrank_range_add_finrank_ker g,
  rw [←hrange] at rn,
  apply tsub_le_iff_right.mpr,
  rw [←rn],
  refine add_le_add (le_refl _) _,
  assumption,
  apply_instance,
end

noncomputable def project_subspace (E F : submodule ℝ V) : submodule ℝ E :=
F.map (orthogonal_projection E).to_linear_map

@[simp]
lemma multiset.sum_project_subspace
(E : submodule ℝ V)
(C : multiset (submodule ℝ V)) :
project_subspace E C.sum = (C.map (project_subspace E)).sum :=
begin
  apply C.sum_linear_map,
  apply_instance,
end

lemma map_vector_span {R : Type} {M : Type} {M₂ : Type} [field R]
[add_comm_group M] [module R M] {σ₁₂ : R →+* R} [add_comm_group M₂] 
[module R M₂] [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : set M)
: submodule.map f (vector_span R s) = vector_span R (f '' s) :=
begin
  simp only [vector_span],
  simp only [submodule.map_span],
  congr,
  apply le_antisymm,
  {
    rintro x ⟨d, ⟨a, b, ha, hb, rfl⟩, rfl⟩,
    refine ⟨f a, f b, _⟩,
    refine ⟨⟨a, ⟨ha, rfl⟩⟩, ⟨b, ⟨hb, rfl⟩⟩, _⟩,
    simp only [linear_map.map_sub, vsub_eq_sub],
  },
  {
    rintro x ⟨fa, fb, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, rfl⟩,
    refine ⟨a - b, _⟩,
    split,
    {
      refine ⟨a, b, ha, hb, rfl⟩,
    },
    simp only [linear_map.map_sub],
    refl,
  },
end

lemma project_subspace_vector_span {A : set V} {E : submodule ℝ V} :
project_subspace E (vector_span ℝ A) = vector_span ℝ (project_set E A) :=
begin
  simp only [project_subspace, map_vector_span, continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe],
  refl,
end

lemma vector_span_projection_sum_commute {C : multiset (set V)} {E : submodule ℝ V} :
vector_span ℝ (project_collection Eᗮ C).sum = project_subspace Eᗮ (vector_span ℝ C.sum) :=
begin
  simp only [project_collection],
  rw [←multiset_sum_project_set_commute C Eᗮ],
  simp only [project_subspace, project_set],
  rw [map_vector_span (orthogonal_projection Eᗮ).to_linear_map],
  simp only [continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe],
end

lemma common_dimension_projection {C : multiset (set V)} {E : submodule ℝ V} :
common_dimension (project_collection Eᗮ C) =
finite_dimensional.finrank ℝ (project_subspace Eᗮ (vector_span ℝ C.sum)) :=
begin
 simp only [common_dimension],
 rw [vector_span_projection_sum_commute],
end

lemma kernel_eq (E : submodule ℝ V) :
(orthogonal_projection E).ker = (orthogonal_projection E).to_linear_map.ker :=
begin
  simp only [continuous_linear_map.ker],
  refl,
end

lemma common_dimension_project_collection (C : multiset (set V)) (E : submodule ℝ V) :
common_dimension (project_collection Eᗮ C) ≥ common_dimension C - finite_dimensional.finrank ℝ E :=
begin
  simp only [common_dimension_projection],
  dsimp only [project_subspace, common_dimension, vector_span],
  have rn := dim_image_ge_dim_domain_sub_dim_ker (orthogonal_projection Eᗮ).to_linear_map (submodule.span ℝ (C.sum -ᵥ C.sum)),
  have : (orthogonal_projection Eᗮ).to_linear_map.ker = E :=
  begin
    rw [←kernel_eq Eᗮ],
    convert ker_of_orthogonal_projection Eᗮ,
    simp only [submodule.orthogonal_orthogonal E],
  end,
  rw [this] at rn,
  assumption,
end



lemma finrank_le_of_le {E F : submodule ℝ V} (h : E ≤ F) : dim E ≤ dim F :=
begin
  have ok : ∀ x : E, E.subtype x ∈ F :=
  begin
    intro x,
    apply h,
    simp only [submodule.coe_subtype, submodule.coe_mem],
  end,
  let f := E.subtype.cod_restrict F ok,
  have f_inj : function.injective f :=
  begin
    refine (@set.injective_cod_restrict _ _ E.subtype F ok).mpr _,
    apply submodule.injective_subtype,
  end,
  apply linear_map.finrank_le_finrank_of_injective f_inj,
end



/- lemma vector_span_ball {x : V} {ε : ℝ} (εpos : ε > 0) :
vector_span ℝ (metric.ball x ε) = ⊤ := sorry -/

lemma span_top_of_ball_subset {A : set V} {x : V} {ε : ℝ} (εpos : ε > 0)
(h : metric.ball x ε ⊆ A) : submodule.span ℝ A = ⊤ :=
begin
  simp only [←top_le_iff],
  rintro v -,
  by_cases he : v = x,
  {
    rw [he],
    apply submodule.subset_span,
    apply h,
    apply metric.mem_ball_self εpos,
  },
  let w := (ε / (2 * ∥v - x∥)) • (v - x) + x,
  have hz := he ∘ norm_sub_eq_zero_iff.mp,
  have hpos := norm_sub_pos_iff.mpr he,
  have hw : w ∈ submodule.span ℝ A,
  {
    simp only [w],
    apply submodule.subset_span,
    apply h,
    simp only [metric.mem_ball, dist_eq_norm],
    simp only [one_div, mul_inv_rev, add_sub_cancel, norm_smul],
    simp only [real.norm_eq_abs, abs_div, abs_mul, abs_two, abs_norm_eq_norm],
    simp only [abs_eq_self.mpr (le_of_lt εpos), div_mul_eq_div_div],
    simp only [div_mul],
    rw [div_self hz, div_one],
    exact half_lt_self εpos,
  },
  have hx : x ∈ submodule.span ℝ A,
  {
    apply submodule.subset_span,
    apply h,
    apply metric.mem_ball_self εpos,
  },
  have hvw : v = (2 * ∥v - x∥ / ε) • (w - x) + x,
  {
    simp only [w, add_sub_cancel, smul_smul],
    rw [div_mul_div_cancel _ (ne_of_gt εpos)],
    rw [div_self (double_ne_zero hz)],
    simp only [one_smul, sub_add_cancel],
  },
  rw [hvw],
  refine submodule.add_mem _ _ _,
  {
    refine submodule.smul_mem _ _ _,
    refine submodule.sub_mem _ _ _,
    all_goals {assumption},
  },
  {assumption},
end

lemma vector_span_top_of_ball_subset {A : set V} {x : V} {ε : ℝ} (εpos : ε > 0)
(h : metric.ball x ε ⊆ A) : vector_span ℝ A = ⊤ :=
begin
  simp only [vector_span],
  suffices hh : metric.ball 0 ε ⊆ diff A,
  {
    exact span_top_of_ball_subset εpos hh,
  },
  intros y hy,
  simp only [metric.mem_ball] at hy,
  refine ⟨x + y, x, _, _, _⟩,
  {
    apply h,
    simp only [metric.mem_ball, dist_self_add_left],
    simpa only [dist_eq_norm, sub_zero] using hy,
  },
  {
    apply h,
    exact metric.mem_ball_self εpos,
  },
  {
    simp only [vsub_eq_sub, add_sub_cancel'],
  },
end

lemma le_orthogonal_symm (E F : submodule ℝ V) :
E ≤ Fᗮ ↔ F ≤ Eᗮ :=
begin
  suffices h : ∀ E F : submodule ℝ V, E ≤ Fᗮ → F ≤ Eᗮ,
  {
    split,
    all_goals {exact h _ _},
  },
  clear E F,
  intros E F h,
  rw [←submodule.orthogonal_orthogonal F],
  apply submodule.orthogonal_le,
  exact h,
end

lemma inner_orthogonal_eq_inner (E : submodule ℝ V)
(u : E) (x : V) : ⟪((proj E) x : V), (u : V)⟫_ℝ = ⟪x, u⟫_ℝ :=
begin
  symmetry,
  apply eq_of_sub_eq_zero,
  -- simp only [submodule.coe_inner],
  rw [←inner_sub_left],
  simp only [proj, continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe, orthogonal_projection_inner_eq_zero,
  submodule.coe_mem],
end

lemma map_proj_orthogonal (E F : submodule ℝ V) :
Fᗮ.map (proj E) = (F.comap E.subtype)ᗮ :=
begin
  rw [←submodule.orthogonal_orthogonal (Fᗮ.map (proj E))],
  refine congr_arg submodule.orthogonal _,
  ext,
  simp only [submodule.mem_map, submodule.mem_comap, submodule.mem_orthogonal, submodule.coe_subtype, submodule.coe_inner],
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  split,
  {
    intros h,
    have : x.val ∈ Fᗮᗮ,
    {
      simp only [submodule.mem_orthogonal],
      intros u hu,
      have := h u hu,
      simpa only [inner_orthogonal_eq_inner] using this,
    },
    {
      simpa only [submodule.orthogonal_orthogonal] using this,
    },
  },
  {
    intros xF v hv,
    simp only [real_inner_comm] at hv,
    simpa only [inner_orthogonal_eq_inner] using hv x xF,
  },
end

lemma mem_orthogonal_span (A : set V) (x : V) :
x ∈ (submodule.span ℝ A)ᗮ ↔ ∀ u : V, u ∈ A → ⟪u, x⟫_ℝ = 0 :=
begin
  split,
  {
    rw [submodule.mem_orthogonal],
    intros hx u hu,
    refine hx u _,
    apply submodule.subset_span,
    exact hu,
  },
  {
    intro h,
    rw [submodule.mem_orthogonal],
    intros u hu,
    apply submodule.span_induction hu,
    {
      exact h,
    },
    {
      simp only [inner_zero_left],
    },
    {
      intros y z hy hz,
      simp only [inner_add_left, hy, hz, add_zero],
    },
    {
      intros a y hy,
      simp only [inner_smul_left, hy, mul_zero],
    },
  },
end

lemma singleton_add_space_eq {E : submodule ℝ V} {x : V}
(xE : x ∈ E) :
({x} : set V) + ↑E = ↑E :=
begin
  ext y, split,
  {
    rintro ⟨xx, e, hxx, eE, rfl⟩,
    rcases (set.eq_of_mem_singleton hxx).symm with rfl,
    exact E.add_mem xE eE,
  },
  {
    intros yE,
    exact ⟨x, y - x, set.mem_singleton _,
      E.sub_mem yE xE, add_sub_cancel'_right _ _⟩,
  },
end

lemma eq_orthogonal_symm (E F : submodule ℝ V) :
E = Fᗮ ↔ F = Eᗮ :=
begin
  split,
  all_goals {
    intro h,
    rw [h, submodule.orthogonal_orthogonal],
  },
end

lemma inner_left_continuous (u : V) :
continuous (flip inner u : V → ℝ) :=
begin
  let f : V → V × V := λ v, (v, u),
  let g : V × V → ℝ := λ x, ⟪x.fst, x.snd⟫_ℝ,
  let h := g ∘ f,
  have gc : continuous g := continuous_inner,
  have hc : continuous h := by continuity,
  exact hc,
end

lemma inner_right_continuous (u : V) :
continuous (inner u : V → ℝ) :=
begin
  let f : V → V × V := λ v, (u, v),
  let g : V × V → ℝ := λ x, ⟪x.fst, x.snd⟫_ℝ,
  let h := g ∘ f,
  have gc : continuous g := continuous_inner,
  have hc : continuous h := by continuity,
  exact hc,
end

lemma inner_product_space.to_dual_symm_apply'
{x : V} {y : normed_space.dual ℝ V} :
⟪x, (inner_product_space.to_dual ℝ V).symm y⟫_ℝ =
y x :=
begin
  rw [real_inner_comm],
  exact inner_product_space.to_dual_symm_apply,
end

noncomputable def of_dual' (f : V →ₗ[ℝ] ℝ) : V :=
(inner_product_space.to_dual ℝ V).symm
⟨f, linear_map.continuous_of_finite_dimensional f⟩

lemma coe_ball_submodule {E : submodule ℝ V} (u : E) (ε : ℝ) :
coe '' metric.ball u ε = metric.ball (u : V) ε ∩ E :=
begin
  ext,
  simp only [set.mem_image, metric.mem_ball, set.mem_inter_iff],
  split,
  {
    rintro ⟨e, he, rfl⟩,
    refine ⟨_, e.property⟩,
    simpa only [subtype.dist_eq] using he,
  },
  {
    rintro ⟨h, xE⟩,
    refine ⟨⟨x, xE⟩, _, rfl⟩,
    {
      simpa only [subtype.dist_eq, subtype.coe_mk] using h,
    },
  },
end

lemma ball_spans_submodule (E : submodule ℝ V) (u : V) (uE : u ∈ E)
{ε : ℝ} (εpos : ε > 0) :
submodule.span ℝ (metric.ball u ε ∩ E) = E :=
begin
  let u' : E := ⟨u, uE⟩,
  suffices h : submodule.span ℝ (metric.ball u' ε) = ⊤,
  {
    simp only [u'] at h,
    replace h := congr_arg (submodule.map E.subtype) h,
    simp only [submodule.map_span] at h,
    simp only [submodule.coe_subtype, submodule.map_subtype_top] at h,
    simpa only [coe_ball_submodule, submodule.coe_mk] using h,
  },
  exact span_top_of_ball_subset εpos (subset_refl _),
end

lemma dist_inner_inner
(v₁ v₂ w₁ w₂ : V) :
⟪v₁, w₁⟫_ℝ ≤ ⟪v₂, w₂⟫_ℝ + (∥v₂ - v₁∥ * ∥w₁∥ + ∥v₂∥ * ∥w₂ - w₁∥) :=
begin
  conv {
    to_lhs,
    rw [←add_sub_cancel'_right v₂ v₁],
    simp only [inner_add_left],
  },
  conv {
    to_lhs,
    congr,
    {
      rw [←add_sub_cancel'_right w₂ w₁],
      simp only [inner_add_right],
    },
  },
  simp only [add_assoc],
  refine add_le_add_left _ _,
  refine le_trans (add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)) _,
  simp only [←dist_eq_norm],
  rw [dist_comm v₁ v₂, dist_comm w₁ w₂, add_comm],
end