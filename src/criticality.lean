import convex linalg multiset data.fintype.basic linear_algebra.dimension
  data.multiset.fintype
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

def subcritical_spaces (C : multiset (submodule ℝ V)) :=
  ∃ τ, τ ≠ 0 ∧ τ ≤ C ∧ dim τ.sum ≤ τ.card

def minimally_subcritical_spaces (C : multiset (submodule ℝ V)) :=
  subcritical_spaces C ∧
  ∀ D : multiset (submodule ℝ V), D ≤ C ∧ subcritical_spaces D → D = C

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

noncomputable def span_singleton (x : V) : submodule ℝ V := submodule.span ℝ {x}

def multiset.linear_independent
(C : multiset V) : Prop :=
semicritical_spaces (C.map span_singleton)

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

lemma semicritical_iff_linear_independent
{C : multiset (submodule ℝ V)} :
semicritical_spaces C ↔ ∃ CC : multiset (pointed_submodule V),
CC.map pointed_submodule.to_space = C ∧
(CC.map pointed_submodule.to_vector).linear_independent :=
begin
  split,
  {
    unfreezingI {
      generalize hn : C.card = n,
      replace hn : C.card ≤ n := le_of_eq hn,
      induction n with n ih generalizing V,
      {
        rw [nat.le_zero_iff, multiset.card_eq_zero] at hn,
        rcases hn with rfl,
        simp only [multiset.map_eq_zero, subtype.val_eq_coe, exists_eq_left],
        rintro -,
        simp only [multiset.linear_independent, semicritical_spaces, multiset.map_zero, nonpos_iff_eq_zero, ge_iff_le, forall_eq,
        multiset.card_zero, zero_le'],
      },
      {
        intro Csc,
        by_cases h : ∃ D, D < C ∧ 0 < D ∧ dim D.sum ≤ D.card,
        admit {
          obtain ⟨D, DC, D0, hD⟩ := h,
          have cD : D.card ≤ n,
          {
            apply nat.le_of_lt_succ,
            exact lt_of_lt_of_le (multiset.card_lt_of_lt DC) hn,
          },
          obtain ⟨fD, hfD⟩ := ih cD (semicritical_of_le (le_of_lt DC) Csc),
          replace hD : dim D.sum = D.card := le_antisymm hD (Csc D (le_of_lt DC)),
          obtain ⟨E, hE⟩ := multiset.le_iff_exists_add.mp (le_of_lt DC),
          obtain rfl := hE,
          let E' := E.map (project_subspace D.sumᗮ),
          have hE'C : E'.card ≤ n,
          {
            apply nat.le_of_lt_succ,
            refine lt_of_lt_of_le _ hn,
            rw [multiset.card_map, multiset.card_add, lt_add_iff_pos_left],
            exact multiset.card_lt_of_lt D0,
          },
          obtain ⟨fE, hfE⟩ := ih hE'C _,
          {
            obtain ⟨G, hG₁, hG₂⟩ := multiset.lift_pointed hfE.1,
            refine ⟨fD + G, _, _⟩,
            {
              simp only [multiset.map_add, hfD.1, hG₁],
            },
            {
              simp only [multiset.linear_independent] at hfD hfE ⊢,
              simp only [multiset.map_add],
              apply semicritical_spaces_factorization',
              {
                split,
                {
                  simp only [multiset.card_map],
                  convert multiset.card_map pointed_submodule.to_space fD,
                  rw [hfD.1],
                  exact hD,
                },
                {
                  intros W hW,
                  simp only [multiset.mem_map, span_singleton] at hW,
                  obtain ⟨-, ⟨x, hx, rfl⟩, rfl⟩ := hW,
                  simp only [submodule.span_le, set.singleton_subset_iff],
                  have : x.to_space ∈ D := hfD.1 ▸ multiset.mem_map_of_mem _ hx,
                  exact le_sum_multiset_of_mem this x.mem,
                },
              },
              {exact hfD.2},
              {
                convert hfE.2 using 1,
                simp only [multiset.map_map, ←hG₂],
                congr' 1,
                funext x,
                simp only [function.comp_app, span_singleton, submodule.map_span],
                congr' 1,
                simp only [pointed_submodule.proj, pointed_submodule.to_vector, subtype.val_eq_coe, set.image_singleton],
              },
            },
          },
          {
            simp only [E', project_subspace],
            apply semicritical_spaces_factorization _ _ _ Csc,
            refine ⟨hD, _⟩,
            intros W hW,
            exact le_sum_multiset_of_mem hW,
          },
        },
        {
          push_neg at h,
          cases multiset.empty_or_exists_mem C with hh hh,
          {
            obtain rfl := hh,
            refine ⟨0, multiset.map_zero _, _⟩,
            {
              simp only [multiset.map_zero _, multiset.linear_independent],
              intros G hG,
              rw [multiset.le_zero] at hG,
              simp only [hG, multiset.card_zero, ge_iff_le, zero_le'],
            },
          },
          {
            -- this has to be changed.
            -- idea: induction over the number of entries with
            -- dimension greater than one
            obtain ⟨W, hW⟩ := hh,
            obtain ⟨T, rfl⟩ := multiset.exists_cons_of_mem hW,
            have := ne_bot_of_semicritical_spaces_of_mem Csc hW,
            rw [submodule.ne_bot_iff] at this,
            obtain ⟨x, xW, xnz⟩ := this,
            simp only [multiset.card_cons, nat.succ_le_succ_iff] at hn,
            obtain ⟨CC, hCC⟩ := ih hn _, rotate,
            {
              admit,
            },
            refine ⟨⟨W, ⟨x, xW⟩⟩ ::ₘ CC, _⟩,
            split,
            {
              admit,
            },
            {
              simp only [multiset.map_cons, multiset.linear_independent],
            },
          },
        },
      },
    },
  }
end

#exit

-- this should become a helper for semicritical_additivity
lemma semicritical_additivity'
{C : multiset (submodule ℝ V × submodule ℝ V)}
(h : semicritical_spaces (C.map prod_sum)) :
∃ F G, C = F + G ∧ semicritical_spaces (F.map prod.fst + G.map prod.snd) :=
begin
  induction C using pauls_multiset_induction,
  {
    refine ⟨0, 0, _, _⟩,
    {simp only [add_zero]},
    {
      simp only [multiset.map_zero, add_zero],
      tauto,
    },
  },
  {
    admit,
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
  revert F,
  induction G using pauls_multiset_induction,
  {
    simp only [multiset.map_zero, add_zero, ge_iff_le],
    intros F h hmax,
    exact h,
  },
  {
    intros F h hmax,
    have : F.map prod.snd + G_C'.map prod_sum ≤ F.map prod.snd + (G_a ::ₘ G_C').map prod_sum,
    {
      simp only [multiset.map_cons, multiset.add_cons],
      exact multiset.le_cons_self _ _,
    },
    have ih := G_ᾰ (semicritical_of_le this h) begin
      intros H leH Hle sc,
      refine hmax H leH _ _,
      {
        rw [multiset.add_cons],
        exact le_trans Hle (multiset.le_cons_self _ _),
      },
      {
        admit,
      }
    end,
    intros D hD,
    rcases multiset_split_le hD with ⟨D₁, D₂, hD₁, hD₂, rfl⟩,
    rcases multiset_exists_of_le_map hD₁ with ⟨pD₁, hpD₁, rfl⟩,
    rcases multiset_exists_of_le_map hD₂ with ⟨pD₂, hpD₂, rfl⟩,
    by_cases hD' : G_a ∈ pD₂,
    {
      rcases multiset.exists_cons_of_mem hD' with ⟨pD₂, rfl⟩,
      simp only [multiset.card_add, multiset.card_map, multiset.card_cons],
      rw [multiset.map_cons, multiset.add_cons, multiset.sum_cons],
      rw [multiset.cons_le_cons_iff] at hpD₂,
      by_contra hc,
      replace hc := lt_of_not_ge hc,
      simp only [nat.lt_succ_iff, nat.add_succ, add_zero] at hc,
      have : G_a.fst + (pD₁.map prod.snd + pD₂.map prod.fst).sum = (pD₁.map prod.snd + pD₂.map prod.fst).sum,
      {
        symmetry,
        refine finite_dimensional.eq_of_le_of_finrank_le _ _,
        {
          simp only [submodule.add_eq_sup, sup_le_iff],
          exact le_sup_right,
        },
        {
          rw [dim_finrank] at hc,
          refine le_trans hc _,
          rw [←multiset.card_add],
          admit,
        },
      },
      admit,
    },
    admit,
  },
end

lemma semicritical_shrinking
{F G : multiset (submodule ℝ V × submodule ℝ V)}
{pr : submodule ℝ V × submodule ℝ V}
(hGF : G ≤ F)
(hsec : semicritical_spaces ((pr ::ₘ F).map prod_sum))
(hsuc : minimally_subcritical_spaces ((pr ::ₘ G).map prod_sum))
(hne : pr.snd ≠ ⊥) :
semicritical_spaces (pr.snd ::ₘ F.map prod_sum) :=
sorry

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