import multiset convex data.fintype.basic linear_algebra.dimension
  measure_theory.measure.measure_space_def
  data.multiset
  linear_algebra.finite_dimensional
  analysis.inner_product_space.projection
  data.multiset.basic
  data.nat.basic

open_locale pointwise

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

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
  conv {to_lhs, rw [←@set_add_zero V _ E]},
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
          rw [←@set_add_zero V _ H],
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

lemma set_vsub_eq_sub
  {A B : set V} : A -ᵥ B = A - B :=
begin
  refl,
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

/- axiom mixed_volume {k : ℕ} {ι : Type} [fintype ι]
  (hcard : fintype.card ι = k)
  (C : ι → convex_body V)
  (hdim : common_dimension (subtype.val ∘ C) ≤ k) : ℝ

axiom mixed_area [measurable_space V] [borel_space V] {k : ℕ} {ι : Type} [fintype ι]
  (hcard : fintype.card ι = k)
  (C : ι → convex_body V)
  (hdim : common_dimension (subtype.val ∘ C) ≤ k + 1) : measure_theory.measure (metric.sphere (0 : V) 1)

axiom mixed_volume_nonneg {k : ℕ} {ι : Type} [fintype ι]
  (hcard : fintype.card ι = k)
  (C : ι → convex_body V)
  (hdim : common_dimension (subtype.val ∘ C) ≤ k) : mixed_volume hcard C hdim ≥ 0

axiom mixed_area_nonneg {k : ℕ} {ι : Type} [fintype ι]
  (hcard : fintype.card ι = k)
  (C : ι → convex_body V)
  (hdim : common_dimension (subtype.val ∘ C) ≤ k + 1) : ??? -/

instance pauls_completeness_foo (E : submodule ℝ V) : complete_space E := sorry


/- def project_set (E : submodule ℝ V) (A : set V) : set E :=
orthogonal_projection E '' A -/
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

lemma multiset_exists_of_le_map {α β : Type} {f : α → β} {b : multiset β} {l : multiset α} :
b ≤ multiset.map f l → ∃ as : multiset α, as ≤ l ∧ multiset.map f as = b :=
begin
  induction b,
  begin
    induction b generalizing l,
    begin
      simp,
    end,
    begin
      intro h,
      simp only [multiset.quot_mk_to_coe''] at *,
      rw [←multiset.cons_coe] at *,
      have := multiset.mem_of_le h (multiset.mem_cons_self b_hd b_tl),
      simp only [multiset.mem_map] at this,
      rcases this with ⟨a, ⟨a_mem_l, a_to_b_hd⟩⟩,
      rcases (multiset.exists_cons_of_mem a_mem_l) with ⟨l_tl, rfl⟩,
      simp only [multiset.map_cons, a_to_b_hd] at h,
      have := multiset.erase_le_erase b_hd h,
      simp only [multiset.erase_cons_head] at this,
      rcases b_ih this with ⟨as_tl, ⟨hle, heq⟩⟩,
      apply exists.intro (a ::ₘ as_tl),
      simp only [multiset.cons_le_cons_iff, hle, multiset.map_cons, a_to_b_hd],
      simp [multiset.cons_eq_cons, heq],
    end,
  end,
  begin
    simp,
  end
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

set_option trace.simp_lemmas true

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
    simp [project_set],
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
      simp,
    },
    {
      rintro y z ⟨py, hyU, rfl⟩ ⟨pz, hzU, rfl⟩,
      refine ⟨py + pz, _⟩,
      split,
      {
        apply submodule.add_mem _ hyU hzU,
      },
      simp,
    },
    {
      rintro a y ⟨py, pyU, rfl⟩,
      refine ⟨a • py, _⟩,
      split,
      {
        apply submodule.smul_mem _ a pyU,
      },
      simp,
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
    simp [hxf],
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
  apply_fun linear_map.ker_le_ker_comp _ _ at hc,
  simp,
end

def ker_dom_restrict_inclusion_injective
  {K : Type} {V : Type} [field K] [add_comm_group V] [module K V]
  {V₂ : Type} [add_comm_group V₂] [module K V₂] [finite_dimensional K V]
  (f : V →ₗ[K] V₂) (W : submodule K V) :
function.injective (ker_dom_restrict_inclusion f W) :=
begin
  rintro x y,
  unfold ker_dom_restrict_inclusion,
  simp,
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
  admit,
end

noncomputable def project_subspace (E F : submodule ℝ V) : submodule ℝ E :=
F.map (orthogonal_projection E).to_linear_map

lemma map_vector_span {R : Type} {M : Type} {M₂ : Type} [field R]
[add_comm_group M] [module R M] {σ₁₂ : R →+* R} [add_comm_group M₂] 
[module R M₂] [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : set M)
: submodule.map f (vector_span R s) = vector_span R (f '' s) :=
begin
  simp only [vector_span],
  have : f '' s -ᵥ f '' s = f '' (s -ᵥ s) :=
  begin
    apply le_antisymm,
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
    {
      rintro x ⟨d, ⟨a, b, ha, hb, rfl⟩, rfl⟩,
      refine ⟨f a, f b, _⟩,
      refine ⟨⟨a, ⟨ha, rfl⟩⟩, ⟨b, ⟨hb, rfl⟩⟩, _⟩,
      simp [linear_map.map_sub],
    }
  end
end

lemma project_subspace_vector_span {A : set V} {E : submodule ℝ V} :
project_subspace E (vector_span ℝ A) = vector_span ℝ (project_set E A) :=
begin
  simp [project_subspace, map_vector_span],
  refl,
end

lemma vector_span_projection_sum_commute {C : multiset (set V)} {E : submodule ℝ V} :
vector_span ℝ (project_collection Eᗮ C).sum = project_subspace Eᗮ (vector_span ℝ C.sum) :=
begin
  simp only [project_collection],
  rw [←multiset_sum_project_set_commute C Eᗮ],
  simp only [project_subspace, project_set],
  rw [map_vector_span (orthogonal_projection Eᗮ).to_linear_map],
  simp,
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
  dsimp,
  norm_cast,
end

lemma common_dimension_project_collection (C : multiset (set V)) (E : submodule ℝ V) :
common_dimension (project_collection Eᗮ C) ≥ common_dimension C - finite_dimensional.finrank ℝ E :=
begin
  simp only [common_dimension_projection],
  dsimp [project_subspace, common_dimension, vector_span],
  have rn := dim_image_ge_dim_domain_sub_dim_ker (orthogonal_projection Eᗮ).to_linear_map (submodule.span ℝ (C.sum -ᵥ C.sum)),
  have : (orthogonal_projection Eᗮ).to_linear_map.ker = E :=
  begin
    rw [←kernel_eq Eᗮ],
    simp [ker_of_orthogonal_projection Eᗮ, submodule.orthogonal_orthogonal E],
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
    simp,
  end,
  let f := E.subtype.cod_restrict F ok,
  have f_inj : function.injective f :=
  begin
    refine (@set.injective_cod_restrict _ _ E.subtype F ok).mpr _,
    apply submodule.injective_subtype,
  end,
  apply linear_map.finrank_le_finrank_of_injective f_inj,
end
