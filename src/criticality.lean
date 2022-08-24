import convex linalg multiset data.fintype.basic linear_algebra.dimension
  submodule_pair data.multiset.fintype
  measure_theory.measure.measure_space_def
  data.multiset
  linear_algebra.finite_dimensional
  analysis.inner_product_space.projection
  data.multiset.basic
  data.nat.basic
  tactic.congr

open_locale pointwise

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma dim_finrank : dim = finite_dimensional.finrank ℝ := rfl

lemma project_subspace_def (E F : submodule ℝ V) : project_subspace E F = F.map (orthogonal_projection E).to_linear_map
:= rfl

/- lemma zero_projection_of_le {E F : subspace ℝ V}
(h : F ≤ E) : project_subspace Eᗮ F = ⊥ :=
begin
  apply linear_map.le_ker_iff_map.mp,
  change F ≤ (proj Eᗮ).ker,
  simp only [ker_of_complementary_orthogonal_projection E, h],
end


lemma common_dimension_of_empty {a : set V}
(he : a = ∅) : common_dimension ({a} : multiset (set V)) = 0 :=
begin
  simp [common_dimension, vector_span, he],
end

lemma nonempty_of_semicritical {A : multiset (set V)} (hsc : semicritical A)
(a : set V) (ha : a ∈ A) : a.nonempty :=
begin
  by_contradiction h,
  have he : a = ∅,
  {
    simpa only [set.not_nonempty_iff_eq_empty] using h,
  },
  have : common_dimension {a} = 0 := common_dimension_of_empty he,
  have h2 := hsc {a} (multiset.singleton_le.mpr ha),
  rw [multiset.card_singleton] at h2,
  rw [this] at h2,
  linarith,
end -/

def semicritical_spaces (C : multiset (submodule ℝ V)) :=
  ∀ τ, τ ≤ C → dim τ.sum ≥ τ.card

def critical_spaces (C : multiset (submodule ℝ V)) :=
  ∀ τ, τ ≠ 0 → τ ≤ C → dim τ.sum > τ.card

def subcritical_spaces (C : multiset (submodule ℝ V)) :=
  ∃ τ, τ ≠ 0 ∧ τ ≤ C ∧ dim τ.sum ≤ τ.card

def minimally_subcritical_spaces (C : multiset (submodule ℝ V)) :=
  subcritical_spaces C ∧
  ∀ D : multiset (submodule ℝ V), D ≤ C ∧ subcritical_spaces D → D = C

def perfect_collection (C : multiset (submodule ℝ V)) :=
∀ D, D ≤ C → dim D.sum = D.card

def subcritical_collection_nonempty {C : multiset (submodule ℝ V)}
(h : subcritical_spaces C) : C.card > 0 :=
begin
  rcases h with ⟨τ, τne, τle, -⟩,
  refine lt_of_lt_of_le _ (multiset.card_mono τle),
  exact multiset.card_pos.mpr τne,
end

def dim_le_card_of_minimally_subcritical {C : multiset (submodule ℝ V)}
(h : minimally_subcritical_spaces C) :
dim C.sum ≤ C.card :=
begin
  rcases h.1 with ⟨τ, τne, τle, τdim⟩,
  rw [←h.2 τ ⟨τle, ⟨τ, τne, le_refl _, τdim⟩⟩],
  exact τdim,
end

/- lemma nonempty_of_subcritical_spaces {C : multiset (submodule ℝ V)}
(h : subcritical_spaces C):
C.card > 0 := h.1 -/

noncomputable def prod_sum
(p : submodule ℝ V × submodule ℝ V) : submodule ℝ V :=
p.fst + p.snd

lemma semicritical_of_le
{C D : multiset (submodule ℝ V)}
(h : C ≤ D)
(hsc : semicritical_spaces D) :
semicritical_spaces C :=
begin
  simp only [semicritical_spaces] at hsc ⊢,
  intros τ hτ,
  exact hsc τ (le_trans hτ h),
end

lemma semicritical_mono
{C : multiset (submodule ℝ V × submodule ℝ V)}
(h : semicritical_spaces (C.map prod.fst)) :
semicritical_spaces (C.map prod_sum) :=
begin
  intros D hD,
  rcases multiset_exists_of_le_map hD with ⟨D, hD', rfl⟩,
  have : (prod.fst : submodule ℝ V × submodule ℝ V → submodule ℝ V) ≤ prod_sum,
  {
    intro pr,
    simp only [prod_sum, submodule.add_eq_sup, le_sup_left],
  },
  rw [dim_finrank],
  refine le_trans _ (submodule.finrank_mono (multiset_sum_mono this)),
  simpa only [multiset.card_map] using h (D.map prod.fst) (multiset.map_mono _ hD'),
end

-- MOVETO submodule_pair.lean
lemma submodule_pair.small_le_big :
(submodule_pair.small : submodule_pair V → submodule ℝ V) ≤ submodule_pair.big :=
begin
  exact submodule_pair.le,
end

lemma semicritical_mono'
{C D : multiset (submodule ℝ V)}
(CD : C ⊑ₘ D)
(Csc : semicritical_spaces C) :
semicritical_spaces D :=
begin
  obtain ⟨X, ⟨rfl, rfl⟩⟩ := CD,
  intros D hD,
  obtain ⟨D, hD', rfl⟩ := multiset_exists_of_le_map hD,
  rw [dim_finrank],
  refine le_trans _ (submodule.finrank_mono (multiset_sum_mono submodule_pair.le)),
  simpa only [multiset.card_map] using
  Csc (D.map submodule_pair.small) (multiset.map_mono _ hD'),
end

lemma proj_def (E : submodule ℝ V) :
proj E = (orthogonal_projection E).to_linear_map := rfl

lemma multiset_sum_project_space_commute
(C : multiset (submodule ℝ V)) (E : submodule ℝ V) :
C.sum.map (proj E) = (C.map (submodule.map (proj E))).sum :=
begin
  induction C using pauls_multiset_induction with C c ih,
  {
    simp only [multiset.sum_zero, submodule.zero_eq_bot, submodule.map_bot, multiset.map_zero],
  },
  {
    simp only [multiset.sum_cons, submodule.add_eq_sup,
      submodule.map_sup, multiset.map_cons],
    congr,
    exact ih,
  }
end

lemma semicritical_spaces_factorization
(C D : multiset (submodule ℝ V))
{E : submodule ℝ V}
(hC : dim E = C.card ∧ multiset_all (λ W, W ≤ E) C)
(hCD : semicritical_spaces (C + D)) :
semicritical_spaces (D.map (λ W, W.map (proj Eᗮ))) :=
begin
  intros τ' hτ',
  rcases multiset_exists_of_le_map hτ' with ⟨τ, hτ, rfl⟩,
  rcases multiset.le_iff_exists_add.mp hτ with ⟨π, rfl⟩,
  let κ := C + τ,
  have hκ : κ ≤ C + (τ + π),
  {
    rw [←add_assoc],
    simp only [κ],
    apply multiset.le_add_right,
  },
  have dimκ : dim κ.sum ≥ C.card + τ.card,
  {
    simp only [←multiset.card_add],
    exact hCD _ hκ,
  },
  have κ_def : κ = C + τ := rfl,
  have rn := subspace_rank_nullity (orthogonal_projection Eᗮ).to_linear_map κ.sum,
  rw [←proj_def, ←dim_finrank] at rn,
  rw [←rn, ker_of_complementary_orthogonal_projection E] at dimκ,
  rw [κ_def, multiset.sum_add, submodule.add_eq_sup, submodule.map_sup,
    dim_finrank] at dimκ,
  have h₁ : C.sum.map (proj Eᗮ) = ⊥,
  {
    apply le_bot_iff.mp,
    intros x hx,
    rw [submodule.mem_map] at hx,
    rcases hx with ⟨px, hpx, rfl⟩,
    replace hpx := sum_multiset_le hC.2 hpx,
    rw [←ker_of_complementary_orthogonal_projection E] at hpx,
    exact hpx,
  },
  have h₂ : dim (@has_inf.inf (submodule ℝ V) _ E (C.sum ⊔ τ.sum)) ≤ C.card,
  {
    rw [←hC.1],
    apply submodule.finrank_mono,
    exact inf_le_left,
  },
  rw [h₁] at dimκ,
  replace dimκ := le_trans dimκ (add_le_add_left h₂ _),
  rw [bot_sup_eq] at dimκ,
  nth_rewrite 1 [add_comm] at dimκ,
  zify at dimκ,
  simp only [add_le_add_iff_left, nat.cast_le] at dimκ,
  rw [multiset_sum_project_space_commute] at dimκ,
  rw [multiset.card_map] at ⊢,
  exact dimκ,
end

lemma semicritical_spaces_factorization'
(C D : multiset (submodule ℝ V))
{E : submodule ℝ V}
(hC : dim E = C.card ∧ multiset_all (λ W, W ≤ E) C)
(Csc : semicritical_spaces C)
(Dsc : semicritical_spaces (D.map (λ W, W.map (proj Eᗮ)))) :
semicritical_spaces (C + D) :=
begin
  intros τ hτ,
  rcases multiset_split_le hτ with ⟨G, H, hGC, hHD, rfl⟩,
  have : dim G.sum + dim (H.map (λ W : submodule ℝ V, W.map (proj Eᗮ))).sum
    ≤ dim (G + H).sum,
  {
    have rn := subspace_rank_nullity (proj Eᗮ) (G + H).sum,
    rw [multiset.sum_add, submodule.add_eq_sup, submodule.map_sup] at rn,
    have h₀ : G.sum ≤ E,
    {
      apply sum_multiset_le,
      intros W hW,
      exact hC.2 W (multiset.subset_of_le hGC hW),
    },
    have h₁ : G.sum.map (proj Eᗮ) = ⊥,
    {
      apply le_bot_iff.mp,
      intros x hx,
      rw [submodule.mem_map] at hx,
      rcases hx with ⟨px, hpx, rfl⟩,
      replace hpx := h₀ hpx,
      rw [←ker_of_complementary_orthogonal_projection E] at hpx,
      exact hpx,
    },
    rw [h₁, bot_sup_eq, ker_of_complementary_orthogonal_projection E] at rn,
    rw [multiset.sum_add, submodule.add_eq_sup, dim_finrank, ←rn],
    nth_rewrite 1 [add_comm],
    rw [multiset_sum_project_space_commute, add_le_add_iff_right],
    apply submodule.finrank_mono,
    exact le_inf h₀ le_sup_left,
  },
  refine le_trans _ this,
  rw [multiset.card_add],
  refine add_le_add _ _,
  {
    apply Csc _ hGC,
  },
  {
    have := Dsc (H.map (λ W, W.map (proj Eᗮ)))
      (multiset.map_le_map hHD),
    rw [multiset.card_map] at this,
    exact this,
  },
end

-- MOVETO multiset
lemma multiset.lt_nonzero_add {α : Type} {C : multiset α}
(hC : C > 0) (D : multiset α) : D < C + D :=
begin
  have := add_lt_add_of_lt_of_le hC (le_refl D),
  simpa only [zero_add] using this,
end


def multiset.linear_independent
(C : multiset V) : Prop :=
semicritical_spaces (C.map span_singleton)


lemma ne_bot_of_semicritical_spaces_of_mem
{C : multiset (submodule ℝ V)}
{W : submodule ℝ V}
(Csc : semicritical_spaces C)
(WC : W ∈ C) : W ≠ ⊥ :=
begin
  intro h,
  rw [←finrank_eq_zero] at h,
  have := Csc {W} (multiset.singleton_le.mpr WC),
  rw [multiset.card_singleton, multiset.sum_singleton, ge_iff_le] at this,
  linarith,
end


-- MOVETO multiset.lean
lemma multiset.card_pos_iff_exists_cons {α : Type}
{C : multiset α} :
0 < C.card ↔ ∃ a D, C = a ::ₘ D :=
begin
  rw [multiset.card_pos_iff_exists_mem],
  apply exists_congr,
  intro a,
  refine ⟨multiset.exists_cons_of_mem, _⟩,
  rintro ⟨D, rfl⟩,
  exact multiset.mem_cons_self _ _,
end

@[simp]
lemma not_critical_iff_subcritical
{C : multiset (submodule ℝ V)} :
¬critical_spaces C ↔ subcritical_spaces C :=
begin
  simp only [critical_spaces, subcritical_spaces],
  push_neg,
  trivial,
end

lemma critical_tail_of_minimally_subcritical_cons
{W : submodule ℝ V} {C : multiset (submodule ℝ V)}
(WC : minimally_subcritical_spaces (W ::ₘ C)) :
critical_spaces C :=
begin
  simp only [minimally_subcritical_spaces] at WC,
  by_contradiction hc,
  simp only [not_critical_iff_subcritical] at hc,
  have := WC.2 C ⟨(multiset.le_cons_self _ _), hc⟩,
  replace := congr_arg multiset.card this,
  rw [multiset.card_cons] at this,
  linarith,
end

lemma semicritical_cons_of_supercritical_tail
{W : submodule ℝ V} {C : multiset (submodule ℝ V)}
(Csc : critical_spaces C)
(hW : W ≠ ⊥) : semicritical_spaces (W ::ₘ C) :=
begin
  intros U hU,
  by_cases h : W ∈ U,
  {
    obtain ⟨T, rfl⟩ := multiset.exists_cons_of_mem h,
    by_cases hT : T = 0,
    {
      obtain rfl := hT,
      simp only [multiset.card_cons, multiset.card_zero, zero_add, ge_iff_le],
      rw [multiset.sum_cons, multiset.sum_zero, add_zero],
      change 0 < dim W,
      apply nat.pos_of_ne_zero,
      change ¬(finite_dimensional.finrank ℝ W = 0),
      rw [finrank_eq_zero],
      exact hW,
    },
    --rw [multiset.sum_cons],
    rw [multiset.cons_le_cons_iff] at hU,
    rw [multiset.card_cons, multiset.sum_cons, ge_iff_le],
    have : T.sum ≤ W + T.sum := by simp only [submodule.add_eq_sup, le_sup_right],
    refine le_trans _ (submodule.finrank_mono this),
    apply Csc, exact hT, exact hU,
  },
  {
    by_cases hz : U = 0,
    {
      obtain rfl := hz,
      rw [multiset.sum_zero, multiset.card_zero],
      exact nat.zero_le _,
    },
    rw [multiset.le_cons_of_not_mem h] at hU,
    refine le_trans (nat.le_succ _) _,
    apply Csc, exact hz, exact hU,
  },
end

lemma semicritical_perforation {C : multiset (submodule ℝ V)}
(Csc : semicritical_spaces C) (h : 1 < C.card) :
∃ D, D ⊑ₘ C ∧ semicritical_spaces D ∧
(∃ E, 0 < E ∧ E < D ∧ dim E.sum = E.card) :=
begin
  by_cases hc : ∃ E, 0 < E ∧ E < C ∧ dim E.sum = E.card,
  {
    exact ⟨C, elem_le_refl _, Csc, hc⟩,
  },
  push_neg at hc,
  have := lt_trans zero_lt_one h,
  rw [multiset.card_pos_iff_exists_cons] at this,
  obtain ⟨W, T, rfl⟩ := this,
  have := ne_bot_of_semicritical_spaces_of_mem Csc
    (multiset.mem_cons_self _ _),
  rw [submodule.ne_bot_iff] at this,
  obtain ⟨x, xW, hx⟩ := this,
  refine ⟨submodule.span ℝ {x} ::ₘ T, _, _, _⟩,
  {
    apply cons_elem_le_cons_head,
    rw [←submodule.span_singleton_le_iff_mem] at xW,
    exact xW,
  },
  {
    -- it would have been nicer to have used this in by_cases
    have Tsup : critical_spaces T,
    {
      intros U hU₁ hU₂,
      refine lt_of_le_of_ne _ _,
      {
        apply Csc,
        exact le_trans hU₂ (multiset.le_cons_self _ _),
      },
      {
        symmetry,
        apply hc,
        {
          exact lt_of_le_of_ne (multiset.zero_le _) hU₁.symm,
        },
        {
          exact lt_of_le_of_lt hU₂ (multiset.lt_cons_self _ _),
        },
      },
    },
    apply semicritical_cons_of_supercritical_tail Tsup,
    intro hs,
    rw [submodule.span_singleton_eq_bot] at hs,
    exact hx hs,
  },
  refine ⟨{submodule.span ℝ {x}}, multiset.lt_cons_self _ _, _, _⟩,
  {
    rw [←multiset.singleton_add, lt_add_iff_pos_right],
    refine lt_of_le_of_ne (multiset.zero_le _) _,
    intro hc,
    obtain rfl := hc,
    simpa only [multiset.card_cons, multiset.card_zero, nat.lt_one_iff, nat.one_ne_zero] using h,
  },
  {
    rw [multiset.card_singleton, multiset.sum_singleton],
    exact finrank_span_singleton hx,
  },
end

lemma semicritical_of_proj_semicritical
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
(h : semicritical_spaces (C.map (project_subspace E))) :
semicritical_spaces C :=
begin
  intros W hW,
  suffices hs : dim (W.map (project_subspace E)).sum ≥ (W.map (project_subspace E)).card,
  {
    rw [multiset.card_map, ←multiset.sum_project_subspace] at hs,
    exact le_trans hs (dim_image_le_self (proj E) W.sum),
  },
  apply h,
  exact multiset.map_le_map hW,
end

lemma perfect_collection_iff_semicritical_dim_one
{C : multiset (submodule ℝ V) } :
perfect_collection C ↔ semicritical_spaces C ∧
multiset_all (λ W : submodule ℝ V, dim W = 1) C :=
begin
  split,
  {
    rintro Cpc,
    split,
    {
      intros G hG,
      rw [Cpc G hG],
      exact le_refl _,
    },
    {
      intros W hW,
      rw [←multiset.sum_singleton W],
      rw [←multiset.singleton_le] at hW,
      exact Cpc {W} hW,
    },
  },
  {
    rintro ⟨Csc, Cdim⟩,
    intros G hG,
    apply le_antisymm,
    {
      convert G.dim_sum_le_sum_dim,
      rw [multiset.sum_one], rotate,
      {
        rw [multiset.all_map],
        exact multiset.all_of_le hG Cdim,
      },
      rw [multiset.card_map],
    },
    {exact Csc G hG},
  },
end

lemma perfect_collection_zero :
perfect_collection (0 : multiset (submodule ℝ V)) :=
begin
  intros G hG,
  simp only [nonpos_iff_eq_zero] at hG,
  obtain rfl := hG,
  rw [multiset.sum_zero, multiset.card_zero, finrank_eq_zero, submodule.zero_eq_bot],
end

-- MOVETO multiset.lean
@[simp]
lemma multiset.le_singleton_iff {α : Type} {x : α}
{C : multiset α} :
C ≤ {x} ↔ C = 0 ∨ C = {x} :=
begin
  cases C.empty_or_exists_mem with hc hc,
  {
    obtain rfl := hc,
    simp only [zero_le, eq_self_iff_true, true_or],
  },
  {
    obtain ⟨a, aC⟩ := hc,
    obtain ⟨T, rfl⟩ := multiset.exists_cons_of_mem aC,
    simp only [multiset.cons_ne_zero, false_or],
    split,
    {
      intro h,
      have := multiset.subset_of_le h (multiset.mem_cons_self a T),
      rw [multiset.mem_singleton] at this,
      obtain rfl := this,
      simp only [multiset.singleton_eq_cons, multiset.cons_le_cons_iff, nonpos_iff_eq_zero] at h,
      obtain rfl := h,
      refl,
    },
    {
      simp only [multiset.singleton_le, multiset.mem_singleton, eq_self_iff_true, implies_true_iff] {contextual := tt},
    },
  },
end

lemma perfect_collection_singleton_span_singleton {x : V}
(h : x ≠ 0) :
perfect_collection ({submodule.span ℝ {x}} : multiset (submodule ℝ V)) :=
begin
  intros G hG,
  simp only [multiset.le_singleton_iff] at hG,
  cases hG with hc hc,
  {
    obtain rfl := hc,
    simp only [multiset.card_zero, finrank_eq_zero, multiset.sum_zero, submodule.zero_eq_bot],
  },
  {
    obtain rfl := hc,
    rw [multiset.card_singleton, multiset.sum_singleton, dim_finrank, finrank_span_singleton],
    exact h,
  },
end

lemma lift_dim1_collection
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
{D : multiset (submodule ℝ E)}
(DC : D ⊑ₘ C.map (project_subspace E))
(hD : multiset_all (λ W : submodule ℝ E, dim W = 1) D) :
∃ F, F ⊑ₘ C ∧ D = F.map (project_subspace E) ∧
multiset_all (λ W : submodule ℝ V, dim W = 1) F :=
begin
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := multiset.lift_submodules DC,
  refine ⟨F, hF₁, hF₂, _⟩,
  intros W hW,
  rw [hF₂, multiset.all_map] at hD,
  replace hD := hD W hW,
  replace hF₃ := hF₃ W hW,
  symmetry,
  convert subspace_rank_nullity (proj E) W,
  rw [hF₃, finrank_bot, add_zero],
  symmetry,
  exact hD,
end

lemma lift_perfect_collection
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
{D : multiset (submodule ℝ E)}
(DC : D ⊑ₘ C.map (project_subspace E))
(hD : perfect_collection D) :
∃ F, F ⊑ₘ C ∧ perfect_collection F :=
begin
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := multiset.lift_submodules DC,
  refine ⟨F, hF₁, _⟩,
  rw [perfect_collection_iff_semicritical_dim_one] at hD ⊢,
  rw [hF₂, multiset.all_map] at hD,
  split,
  {
    exact semicritical_of_proj_semicritical hD.1,
  },
  {
    intros W hW,
    replace hD := hD.2 W hW,
    replace hF₃ := hF₃ W hW,
    symmetry,
    convert subspace_rank_nullity (proj E) W,
    rw [hF₃, finrank_bot, add_zero],
    symmetry,
    exact hD,
  },
end

lemma perfect_collection_gluing
{C D : multiset (submodule ℝ V)}
{E : submodule ℝ V}
{D' : multiset (submodule ℝ Eᗮ)}
(h₁ : dim E = C.card)
(h₂ : multiset_all (λ W : submodule ℝ V, W ≤ E) C)
(h₃ : perfect_collection C)
(h₄ : D' ⊑ₘ D.map (project_subspace Eᗮ))
(h₅ : perfect_collection D') :
∃ F, F ⊑ₘ C + D ∧ perfect_collection F :=
begin
  simp only [perfect_collection_iff_semicritical_dim_one] at h₃ h₅ ⊢,
  obtain ⟨F, hF₁, hF₂⟩ := lift_dim1_collection h₄ h₅.2,
  refine ⟨C + F, _, _, _⟩,
  {
    exact add_elem_le_add_left hF₁,
  },
  {
    apply semicritical_spaces_factorization',
    {
      exact ⟨h₁, h₂⟩,
    },
    {
      exact h₃.1,
    },
    {
      obtain rfl := hF₂.1,
      exact h₅.1,
    },
  },
  {
    simp only [multiset.all_add, h₃.2, hF₂.2, and_true],
  },
end

lemma semicritical_perfecting
{C : multiset (submodule ℝ V)} :
semicritical_spaces C ↔ ∃ D, D ⊑ₘ C ∧ perfect_collection D :=
begin
  split,
  {
    unfreezingI {
      generalize hn : C.card = n,
      replace hn : C.card ≤ n := le_of_eq hn,
      induction n with n ih generalizing V,
      {
        intro Csc,
        rw [nat.le_zero_iff, multiset.card_eq_zero] at hn,
        obtain rfl := hn,
        refine ⟨0, elem_le_refl _, _⟩,
        simp only [perfect_collection, nonpos_iff_eq_zero, forall_eq, multiset.card_zero, finrank_eq_zero, multiset.sum_zero,
        submodule.zero_eq_bot],
      },
      {
        intro Csc,
        by_cases hc : 1 < C.card,
        {
          obtain ⟨D, DC, Dsc, ⟨F, Fpos, FD, hF⟩⟩ := semicritical_perforation Csc hc,
            rw [←card_eq_of_elem_le DC] at hn,
          have cF : F.card ≤ n,
          {
            apply nat.le_of_lt_succ,
            exact lt_of_lt_of_le (multiset.card_lt_of_lt FD) hn,
          },
          obtain ⟨fF, hfF, fFp⟩ := ih cF (semicritical_of_le (le_of_lt FD) Dsc),
          obtain ⟨G, rfl⟩ := multiset.le_iff_exists_add.mp (le_of_lt FD),
          let G' := G.map (project_subspace F.sumᗮ),
          have cG' : G'.card ≤ n,
          {
            apply nat.le_of_lt_succ,
            refine lt_of_lt_of_le _ hn,
            rw [multiset.card_map, multiset.card_add, lt_add_iff_pos_left],
            exact multiset.card_lt_of_lt Fpos,
          },
          obtain ⟨fG', hfG', fGp'⟩ := ih cG' _, rotate,
          {
            simp only [G', project_subspace],
            apply semicritical_spaces_factorization _ _ _ Dsc,
            refine ⟨hF, _⟩,
            intros W hW,
            exact le_sum_multiset_of_mem hW,
          },
          have h₁ : dim F.sum = fF.card,
          {
            rw [card_eq_of_elem_le hfF],
            exact hF,
          },
          have h₂ : multiset_all (λ W : submodule ℝ V, W ≤ F.sum) fF,
          {
            obtain ⟨X, hX⟩ := hfF,
            intros W hW,
            rw [←hX.1, multiset.mem_map] at hW,
            rw [←hX.2],
            obtain ⟨pr, prX, rfl⟩ := hW,
            refine le_trans pr.le _,
            exact le_sum_multiset_of_mem (multiset.mem_map_of_mem _ prX),
          },
          obtain ⟨H, hH, Hp⟩ := perfect_collection_gluing h₁ h₂ fFp hfG' fGp',
          refine ⟨H, elem_le_trans (elem_le_trans hH _) DC, Hp⟩,
          exact add_elem_le_add_right hfF,
        },
        {
          push_neg at hc,
          cases multiset.empty_or_exists_mem C with hh hh,
          {
            obtain rfl := hh,
            exact ⟨0, elem_le_refl _, perfect_collection_zero⟩,
          },
          {
            -- this has to be changed.
            -- idea: induction over the number of entries with
            -- dimension greater than one
            obtain ⟨W, hW⟩ := hh,
            have := ne_bot_of_semicritical_spaces_of_mem Csc hW,
            rw [submodule.ne_bot_iff] at this,
            obtain ⟨x, xW, hx⟩ := this,
            refine ⟨{submodule.span ℝ {x}}, _, _⟩,
            {
              refine ⟨{⟨W, ⟨submodule.span ℝ {x}, _⟩⟩}, _⟩,
              {simp only [xW, submodule.span_singleton_le_iff_mem]},
              {
                simp only [submodule_pair.small, submodule_pair.big, multiset.map_singleton, eq_self_iff_true, true_and],
                obtain ⟨T, rfl⟩ := multiset.exists_cons_of_mem hW,
                simp only [multiset.singleton_eq_cons, multiset.cons_inj_right],
                simp only [multiset.card_cons, add_le_iff_nonpos_left, le_zero_iff, multiset.card_eq_zero] at hc,
                rw [hc],
              },
            },
            {
              exact perfect_collection_singleton_span_singleton hx,
            },
          },
        },
      },
    },
  },
  {
    rintro ⟨D, DC, Dp⟩,
    rw [perfect_collection_iff_semicritical_dim_one] at Dp,
    exact semicritical_mono' DC Dp.1,
  },
end

-- MOVETO multiset.lean
lemma multiset.sum_le_sum_of_le
{C D : multiset (submodule ℝ V)}
(h : C ≤ D) :
C.sum ≤ D.sum :=
begin
  induction C using pauls_multiset_induction with C W ih,
  {
    simp only [multiset.sum_zero, submodule.zero_eq_bot, bot_le],
  },
  {
    simp only [multiset.sum_cons, submodule.add_eq_sup, sup_le_iff],
    split,
    {
      apply le_sum_multiset_of_mem,
      apply multiset.subset_of_le h,
      exact multiset.mem_cons_self _ _,
    },
    {
      apply ih,
      exact le_trans (multiset.le_cons_self _ _) h,
    },
  },
end

lemma semicritical_cons_iff_not_le_of_perfect
{C : multiset (submodule ℝ V)}
{W : submodule ℝ V}
(h : perfect_collection C) :
semicritical_spaces (W ::ₘ C) ↔ ¬W ≤ C.sum :=
begin
  split,
  {
    intros sc WC,
    have h₁ := sc _ (le_refl _),
    rw [multiset.sum_cons, submodule.add_eq_sup, multiset.card_cons] at h₁,
    replace h₁ := le_trans h₁ (submodule.finrank_mono (sup_le WC (le_refl _))),
    have h₂ := h _ (le_refl _),
    simp only [←dim_finrank] at h₁,
    linarith,
  },
  {
    intro WC,
    simp only [semicritical_spaces],
    by_contradiction hc,
    push_neg at hc,
    obtain ⟨G, hG₁, hG₂⟩ := hc,
    by_cases WG : W ∈ G,
    {
      obtain ⟨T, rfl⟩ := multiset.exists_cons_of_mem WG, clear WG,
      rw [multiset.cons_le_cons_iff] at hG₁,
      rw [multiset.card_cons, multiset.sum_cons, ←h _ hG₁,
        nat.add_one, nat.lt_succ_iff] at hG₂,
      have := finite_dimensional.eq_of_le_of_finrank_le _ hG₂, rotate,
      {exact le_add_left (le_refl _)},
      replace : W ≤ T.sum := this.symm ▸ le_self_add,
      replace := le_trans this (multiset.sum_le_sum_of_le hG₁),
      exact WC this,
    },
    {
      rw [multiset.le_cons_of_not_mem WG] at hG₁,
      have := h _ hG₁,
      rw [this, ←not_le] at hG₂,
      exact hG₂ (le_refl _),
    },
  },
end

-- MOVETO linalg.lean
lemma submodule.not_le_iff
{E F: submodule ℝ V} :
¬E ≤ F ↔ ∃ x : V, x ∈ E ∧ x ∉ F :=
begin
  rw [←not_iff_not],
  push_neg,
  tauto,
end

-- MOVETO linalg.lean
lemma submodule.add_le_iff
{E F G : submodule ℝ V} :
E + F ≤ G ↔ E ≤ G ∧ F ≤ G :=
begin
  rw [submodule.add_eq_sup],
  simp only [sup_le_iff],
end

-- MOVETO submodule_pair.lean
lemma cons_elem_le_cons_tail
{C D : multiset (submodule ℝ V)}
{W : submodule ℝ V}
(CD : C ⊑ₘ D) : W ::ₘ C ⊑ₘ W ::ₘ D :=
begin
  obtain ⟨X, hX₁, hX₂⟩ := CD,
  refine ⟨⟨W, ⟨W, le_refl W⟩⟩ ::ₘ X, _, _⟩,
  {
    simpa only [submodule_pair.small, multiset.map_cons, multiset.cons_inj_right] using hX₁,
  },
  {
    simpa only [submodule_pair.big, multiset.map_cons, multiset.cons_inj_right] using hX₂,
  },
end

lemma perfect_collection_of_le
{C D : multiset (submodule ℝ V)}
(CD : C ≤ D)
(Dp : perfect_collection D) : perfect_collection C :=
begin
  simp only [perfect_collection] at Dp ⊢,
  intros G hG,
  exact Dp G (le_trans hG CD),
end

lemma semicritical_additivity''
{C : multiset (submodule ℝ V)}
{W₁ W₂ : submodule ℝ V}
(sc : semicritical_spaces ((W₁ + W₂) ::ₘ C)) :
semicritical_spaces (W₁ ::ₘ C) ∨ semicritical_spaces (W₂ ::ₘ C) :=
begin
  rw [semicritical_perfecting] at sc,
  obtain ⟨D, DW, Dp⟩ := sc,
  --let DW' := DW,
  obtain ⟨X, rfl, hX⟩ := DW,
  have := multiset.mem_cons_self (W₁ + W₂) C,
  rw [←hX, multiset.mem_map] at this,
  obtain ⟨pr, prX, prW⟩ := this,
  obtain ⟨X, rfl⟩ := multiset.exists_cons_of_mem prX, clear prX,
  simp only [multiset.map_cons] at Dp,
  have h₁ := Dp _ (le_refl _),
  have h₂ := Dp _ (multiset.le_cons_self _ _),
  rw [multiset.card_cons] at h₁,
  rw [←h₂] at h₁,
  by_cases hc : pr.small ≤ (X.map submodule_pair.small).sum,
  {
    have : (pr.small ::ₘ X.map submodule_pair.small).sum ≤ (X.map submodule_pair.small).sum,
    {
      refine sum_multiset_le _,
      intros G hG,
      rw [multiset.mem_cons] at hG,
      cases hG with hG hG,
      {
        obtain rfl := hG,
        exact hc,
      },
      {
        exact le_sum_multiset_of_mem hG,
      },
    },
    replace := submodule.finrank_mono this,
    simp only [←dim_finrank] at this,
    linarith,
  },
  {
    have : ¬(W₁ + W₂ ≤ (X.map submodule_pair.small).sum),
    {
      rw [←prW],
      intro h,
      exact hc (le_trans pr.le h),
    },
    rw [submodule.add_le_iff, not_and_distrib,
      submodule.not_le_iff, submodule.not_le_iff] at this,
    rcases this with hh | hh,
    {
      left,
      have : W₁ ::ₘ multiset.map submodule_pair.small X ⊑ₘ W₁ ::ₘ C,
      {
        apply cons_elem_le_cons_tail,
        simp only [multiset.map_cons, prW, multiset.cons_eq_cons] at hX,
        simp only [eq_self_iff_true, true_and, ne.def, not_true, false_and, or_false] at hX,
        refine ⟨X, rfl, hX⟩,
      },
      refine semicritical_mono' this _,
      rw [semicritical_cons_iff_not_le_of_perfect], rotate,
      {
        exact perfect_collection_of_le (multiset.le_cons_self _ _) Dp,
      },
      rw [submodule.not_le_iff],
      exact hh,
    },
    {
      right,
      have : W₂ ::ₘ multiset.map submodule_pair.small X ⊑ₘ W₂ ::ₘ C,
      {
        apply cons_elem_le_cons_tail,
        simp only [multiset.map_cons, prW, multiset.cons_eq_cons] at hX,
        simp only [eq_self_iff_true, true_and, ne.def, not_true, false_and, or_false] at hX,
        refine ⟨X, rfl, hX⟩,
      },
      refine semicritical_mono' this _,
      rw [semicritical_cons_iff_not_le_of_perfect], rotate,
      {
        exact perfect_collection_of_le (multiset.le_cons_self _ _) Dp,
      },
      rw [submodule.not_le_iff],
      exact hh,
    },
  },
end


-- this should become a helper for semicritical_additivity
lemma semicritical_additivity'
{C : multiset (submodule ℝ V × submodule ℝ V)}
{D : multiset (submodule ℝ V)}
(h : semicritical_spaces (D + C.map prod_sum)) :
∃ F G, C = F + G ∧ semicritical_spaces (D + F.map prod.fst + G.map prod.snd) :=
begin
  revert D,
  induction C using pauls_multiset_induction with C pr ih,
  {
    intros D h,
    refine ⟨0, 0, _, _⟩,
    {simp only [add_zero]},
    {
      simp only [multiset.map_zero, add_zero],
      exact semicritical_of_le (multiset.le_add_right _ _) h,
    },
  },
  {
    intros D h,
    rw [multiset.map_cons, multiset.add_cons] at h,
    simp only [prod_sum] at h,
    cases semicritical_additivity'' h with sc sc,
    {
      rw [←multiset.cons_add] at sc,
      obtain ⟨F', G', rfl, hFG'⟩ := ih sc,
      refine ⟨pr ::ₘ F', G', by rw [multiset.cons_add], _⟩,
      simpa only [multiset.map_cons, multiset.cons_add, multiset.add_cons] using hFG',
    },
    {
      rw [←multiset.cons_add] at sc,
      obtain ⟨F', G', rfl, hFG'⟩ := ih sc,
      refine ⟨F', pr ::ₘ G', by rw [multiset.add_cons], _⟩,
      simpa only [multiset.map_cons, multiset.cons_add, multiset.add_cons] using hFG',
    },
  },
end

lemma semicritical_additivity
{F G : multiset (submodule ℝ V × submodule ℝ V)}
(h : semicritical_spaces (F.map prod.snd + G.map prod_sum))
(hmax : ∀ H, H ≥ F → H ≤ F + G →
  semicritical_spaces (H.map prod.snd + (F + G - H).map prod_sum) →
  H = F) :
semicritical_spaces (F.map prod.snd + G.map prod.fst) :=
begin
  obtain ⟨F', G', rfl, hFG'⟩ := semicritical_additivity' h,
  rw [add_comm, ←add_assoc, ←multiset.map_add] at hFG',
  replace hmax := hmax (F + G') _ _ _, rotate,
  {
    simp only [ge_iff_le, le_add_iff_nonneg_right, zero_le],
  },
  {
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, zero_le],
  },
  {
    have : semicritical_spaces (multiset.map prod.snd (G' + F) + multiset.map prod_sum F'),
    {
      let X : multiset (submodule ℝ V × submodule ℝ V) :=
      (G' + F).map (λ pr, ⟨pr.snd, pr.snd⟩) + F',
      have Xfst : semicritical_spaces (X.map prod.fst),
      {
        simp only [multiset.map_add, multiset.map_map, function.comp_app] at hFG' ⊢,
        exact hFG',
      },
      have := semicritical_mono Xfst,
      simp only [multiset.map_add, multiset.map_map, function.comp_app, prod_sum, submodule.add_eq_sup, sup_idem] at this ⊢,
      exact this,
    },
    convert this using 2,
    {
      rw [add_comm],
    },
    {
      rw [tsub_add_eq_tsub_tsub, add_tsub_cancel_left, add_tsub_cancel_right],
    },
  },
  rw [add_right_eq_self] at hmax,
  obtain rfl := hmax,
  simpa [add_zero, zero_add] using hFG',
end

lemma semicritical_shrinking
{F G : multiset (submodule ℝ V × submodule ℝ V)}
{pr : submodule ℝ V × submodule ℝ V}
(hGF : G ≤ F)
(hsec : semicritical_spaces ((pr ::ₘ F).map prod_sum))
(hsuc : minimally_subcritical_spaces ((pr ::ₘ G).map prod_sum))
(hne : pr.snd ≠ ⊥) :
semicritical_spaces (pr.snd ::ₘ F.map prod_sum) :=
begin
  have Gcr : critical_spaces (G.map prod_sum),
  {
    rw [multiset.map_cons] at hsuc,
    exact critical_tail_of_minimally_subcritical_cons hsuc,
  },
  have sc : semicritical_spaces (pr.snd ::ₘ G.map prod_sum) :=
  semicritical_cons_of_supercritical_tail Gcr hne,
  let E := (pr.snd ::ₘ G.map prod_sum).sum,
  have hE₁ : E = (pr.snd ::ₘ G.map prod_sum).sum := rfl,
  have hE₂ : E = ((pr ::ₘ G).map prod_sum).sum,
  {
    rw [hE₁],
    apply finite_dimensional.eq_of_le_of_finrank_le,
    {
      simp only [multiset.map_cons, multiset.sum_cons, submodule.add_eq_sup, sup_le_iff, le_sup_right, and_true],
      refine le_trans _ le_sup_left,
      simp only [prod_sum, submodule.add_eq_sup, le_sup_right],
    },
    {
      rw [←dim_finrank],
      refine le_trans (dim_le_card_of_minimally_subcritical hsuc) _,
      refine le_trans _ (sc _ (le_refl _)),
      simp only [multiset.card_map, multiset.card_cons],
    },
  },
  have hdim₁ : dim E = (pr.snd ::ₘ G.map prod_sum).card,
  {
    rw [hE₁],
    apply le_antisymm,
    {
      have := dim_le_card_of_minimally_subcritical hsuc,
      simp only [multiset.card_cons, multiset.card_map] at this ⊢,
      refine le_trans _ this,
      rw [dim_finrank],
      apply submodule.finrank_mono,
      simp only [multiset.sum_cons, submodule.add_eq_sup, multiset.map_cons, sup_le_iff, le_sup_right, and_true],
      refine le_trans _ le_sup_left,
      simp only [prod_sum, submodule.add_eq_sup, le_sup_right],
    },
    {
      exact sc _ (le_refl _),
    },
  },
  have hdim₂ : dim E = ((pr ::ₘ G).map prod_sum).card,
  {
    rw [hdim₁],
    simp only [multiset.card_cons, multiset.map_cons],
  },
  obtain ⟨H, rfl⟩ := multiset.le_iff_exists_add.mp hGF, clear hGF,
  rw [multiset.map_add, ←multiset.cons_add],
  refine semicritical_spaces_factorization' _ _ ⟨hdim₁, _⟩ sc _,
  {
    intros W hW,
    rw [hE₁],
    apply le_sum_multiset_of_mem hW,
  },
  {
    rw [multiset.map_cons, multiset.map_add, ←multiset.cons_add, ←multiset.map_cons] at hsec,
    apply semicritical_spaces_factorization,
    {
      refine ⟨hdim₂, _⟩,
      intros W hW,
      rw [hE₂],
      apply le_sum_multiset_of_mem hW,
    },
    {
      exact hsec,
    },
  },
end

lemma semicritical_switching
(C : multiset (submodule ℝ V × submodule ℝ V))
(E : submodule ℝ V)
(nontriv : C.card > 0)
(C1sc : semicritical_spaces (C.map prod.fst))
(hE : dim E = C.card)
(hCE : multiset_all (λ x : submodule ℝ V × submodule ℝ V, x.fst ≤ E ∧ x.snd ≤ E) C)
(hne : ∀ x : submodule ℝ V × submodule ℝ V, x ∈ C → prod.snd x ≠ 0):
∃ A B : multiset (submodule ℝ V × submodule ℝ V), A ≤ B ∧ B ≤ C ∧
semicritical_spaces ((B.map prod.snd) + ((C - B).map prod.fst)) ∧
dim (A.map prod.snd).sum = A.card ∧
A.card > 0 :=
begin
  let p : multiset (submodule ℝ V × submodule ℝ V) → Prop :=
    λ D, semicritical_spaces (D.map prod.snd + (C - D).map prod_sum),
  have hp : p ⊥,
  {
    simp only [p, multiset.bot_eq_zero],
    rw [multiset.map_zero, zero_add, multiset.sub_zero],
    intros τ hτ,
    exact (semicritical_mono C1sc) τ hτ,
  },
  rcases ex_maximal_multiset (bot_le : ⊥ ≤ C) hp with ⟨F, hFC, pF, Fmax⟩,
  rw [multiset.le_iff_exists_add] at hFC,
  rcases hFC with ⟨F', rfl⟩,
  let mF : multiset (submodule ℝ V × submodule ℝ V) :=
    F.map (λ x, ⟨x.snd, x.snd⟩),
  let q : multiset (submodule ℝ V × submodule ℝ V) → Prop :=
    λ D, subcritical_spaces (D.map prod_sum),
  have hq : q (mF + F'),
  {
    refine ⟨(mF + F').map prod_sum, _, le_refl _, _⟩,
    {
      simpa only [←multiset.card_pos, multiset.card_add, multiset.card_map] using nontriv,
    },
    {
      have : ((mF + F').map prod_sum).sum ≤ E,
      {
        apply sum_multiset_le _,
        intros W hW,
        simp only [multiset.mem_map, multiset.mem_add] at hW,
        rcases hW with ⟨W, (⟨a, ha, rfl⟩ | hW), rfl⟩,
        {
          simp only [prod_sum, submodule.add_eq_sup, sup_idem],
          have := hCE a (multiset.subset_of_le (multiset.le_add_right _ _) ha),
          exact this.2,
        },
        {
          simp only [prod_sum, submodule.add_eq_sup, sup_le_iff],
          exact hCE W (multiset.subset_of_le (multiset.le_add_left _ _) hW),
        },
      },
      rw [dim_finrank] at hE ⊢,
      refine le_trans (submodule.finrank_mono this) _,
      simp only [mF, multiset.card_map, multiset.card_add, hE],
    },
  },
  rcases ex_minimal_multiset (le_refl (mF + F')) hq with ⟨G, hGC, qG, Gmin⟩,
  rcases multiset_split_le hGC with ⟨mG₁, G₂, hmG₁, hG₂, rfl⟩,
  rcases multiset_exists_of_le_map hmG₁ with ⟨G₁, hG₁, hG₁e⟩,
  rw [multiset.le_iff_exists_add] at hG₂,
  -- rcases hG₁ with ⟨G₁', rfl⟩,
  rcases hG₂ with ⟨G₂', rfl⟩,
  -- let mG₁' : multiset (submodule ℝ V × submodule ℝ V) :=
  --   G₁'.map (λ x, ⟨x.snd, x.snd⟩),
  have G₂0 : G₂ = 0,
  {
    by_contra hc,
    rcases multiset.exists_mem_of_ne_zero hc with ⟨pr, hpr⟩,
    rcases multiset.exists_cons_of_mem hpr with ⟨rG₂, rfl⟩,
    have := semicritical_shrinking
      (_ : mG₁ + rG₂ ≤ mF + (rG₂ + G₂'))
      _
      _
      (_ : pr.snd ≠ ⊥),
    {
      simp only [mF] at this,
      rw [multiset.map_add, multiset.map_map,
        map_lambda] at this,
      simp only [function.comp_app, prod_sum,
        submodule.add_eq_sup, sup_idem,
        ←multiset.cons_add] at this,
      rw [←multiset.map_cons] at this,
      simp only [←submodule.add_eq_sup] at this,
      replace Fmax := Fmax (pr ::ₘ F) (multiset.le_cons_self _ _),
      simp only [p,multiset.cons_add, multiset.add_cons] at Fmax,
      replace Fmax := Fmax (multiset.cons_le_cons _ (multiset.le_add_right _ _)),
      simp only [cons_erase_cons, add_tsub_cancel_left] at Fmax,
      replace Fmax := Fmax this,
      replace Fmax := congr_arg multiset.card Fmax,
      simp only [multiset.card_cons] at Fmax,
      linarith,
    },
    {
      refine add_le_add _ _,
      {
        exact hmG₁,
      },
      {
        exact multiset.le_add_right _ _,
      },
    },
    {
      simp only [p] at pF,
      simp only [add_tsub_cancel_left] at pF,
      rw [←multiset.add_cons, ←multiset.cons_add],
      rw [multiset.map_add],
      simp only [mF, multiset.map_map],
      rw [map_lambda],
      simp only [function.comp_app, prod_sum,
        submodule.add_eq_sup, sup_idem],
      simp only [←submodule.add_eq_sup],
      exact pF,
    },
    {
      simp only [q, multiset.add_cons] at qG Gmin,
      refine ⟨qG, _⟩,
      intros D hD,
      rcases multiset_exists_of_le_map hD.1 with ⟨D', hD', rfl⟩,
      replace Gmin := Gmin D' hD' hD.2,
      rw [Gmin],
    },
    {
      apply hne _,
      simp only [multiset.add_cons, multiset.cons_add],
      exact multiset.mem_cons_self _ _,
    },
  },
  cases G₂0,
  refine ⟨G₁, F, hG₁, multiset.le_add_right _ _, _, _, _⟩,
  {
    simp only [multiset.quot_mk_to_coe'', multiset.coe_nil_eq_zero, zero_add, add_tsub_cancel_left], -- somehow use maximality of F
    refine semicritical_additivity _ _,
    {
      simp only [p] at pF,
      simp only [add_tsub_cancel_left, multiset.quot_mk_to_coe'', multiset.coe_nil_eq_zero, zero_add] at pF,
      exact pF,
    },
    {
      intros H h1 h2 h3,
      simp only [p, multiset.quot_mk_to_coe'', multiset.coe_nil_eq_zero, zero_add] at Fmax,
      symmetry,
      exact Fmax H h1 h2 h3,
    },
  },
  {
    apply le_antisymm,
    {
      have : minimally_subcritical_spaces (G₁.map prod.snd),
      {
        refine ⟨_, _⟩,
        {
          simp only [q, add_zero, multiset.quot_mk_to_coe'', multiset.coe_nil_eq_zero] at qG,
          simp only [←hG₁e, multiset.map_map] at qG,
          rw [map_lambda] at qG,
          simp only [function.comp_app, prod_sum, submodule.add_eq_sup, sup_idem] at qG,
          exact qG,
        },
        {
          simp only [multiset.quot_mk_to_coe'', multiset.coe_nil_eq_zero, add_zero] at Gmin,
          rintro D ⟨hD₁, hD₂⟩,
          rcases multiset_exists_of_le_map hD₁ with ⟨D, hD, rfl⟩,
          let mD : multiset( submodule ℝ V × submodule ℝ V) := D.map (λ pr, ⟨pr.snd, pr.snd⟩),
          simp only [←hG₁e] at Gmin,
          have := Gmin mD (multiset.map_mono _ hD) _,
          {
            replace this := congr_arg (multiset.map prod.snd) this,
            simp only [multiset.map_map, function.comp_app] at this,
            symmetry,
            exact this,
          },
          {
            simp only [q, multiset.quot_mk_to_coe'', multiset.coe_nil_eq_zero, add_zero],
            simp only [multiset.map_map, function.comp_app, prod_sum, submodule.add_eq_sup, sup_idem],
            exact hD₂,
          },
        },
      },
      rcases this.1 with ⟨Gsuc, h1, h2, h3⟩,
      have : Gsuc = G₁.map prod.snd,
      {
        refine this.2 Gsuc ⟨h2, Gsuc, h1, le_refl _, h3⟩,
      },
      rw [this, multiset.card_map] at h3,
      exact h3,
    },
    {
      simp only [p, add_tsub_cancel_left] at pF,
      simp only [add_tsub_cancel_left] at pF,
      have := semicritical_of_le (multiset.le_add_right _ _) pF,
      replace := semicritical_of_le (multiset.map_mono _ hG₁) this,
      simpa only [multiset.card_map] using this (G₁.map prod.snd) (le_refl _),
    },
  },
  {
    simp only [q] at qG,
    have := subcritical_collection_nonempty qG,
    simpa only [←hG₁e, multiset.map_add, multiset.card_add,
      multiset.card_map] using this,
  },
end