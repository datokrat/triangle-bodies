import convex convex_body linalg measure touching_cone brunn_minkowski
  microid criticality pruning locally_linear arithmetic
  touching_cone_polytope
  analysis.convex.basic
  data.multiset.basic
  measure_theory.measure.measure_space
  topology.basic
  analysis.inner_product_space.pi_L2

open_locale pointwise
open_locale ennreal -- for ∞ notation
open_locale topological_space -- for 𝓝 notation

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

section definitions

variables (V : Type)
[inner_product_space ℝ V] [finite_dimensional ℝ V]

end definitions

section preparation_lemmas

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

noncomputable def TS_microid_measure {k : ℕ} (u : metric.sphere (0 : V) 1) (μ : microid_measure V k) :
submodule ℝ V :=
TS (microid_of_measure μ).val u.val
end preparation_lemmas


section default_reduction

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def microid_pair (k : ℕ)
(u : metric.sphere (0 : V) 1) :=
(Σ μ : microid_measure V k,
{P : microid_generator_space V k // is_default_polytope μ u P})

def pair_to_default_body {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : convex_body V :=
convex_body_of_polytope (polytope_of_microid_generator pair.2.1)

def pair_to_measure {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair: microid_pair k u) : microid_measure V k := pair.1

noncomputable def pair_to_microid {k : ℕ}
{u : metric.sphere (0 : V) 1} :
microid_pair k u → convex_body V :=
microid_of_measure ∘ pair_to_measure

noncomputable def pair_to_default_measure {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : microid_measure V k :=
dirac_microid_measure pair.2.1

noncomputable def pair_to_TS {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V :=
TS (pair_to_microid pair).val u

noncomputable def reduce_pair {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : microid_pair k u :=
begin
  refine ⟨pair_to_default_measure pair, pair.2.1, _⟩,
  rcases pair.2.2 with ⟨h1, h2, h3⟩,
  refine ⟨h1, h2, _⟩,
  {
    simp only [pair_to_default_measure, microid_of_dirac_eq],
    simp only [body_of_poly_of_gen_eq],
    refine ⟨h3.1, _⟩,
    intros C hC,
    exact id,
  },
end

lemma reduced_microid_eq_default_body {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
(pair_to_microid (reduce_pair pair)) = pair_to_default_body pair :=
begin
  simp only [pair_to_microid, pair_to_TS, pair_to_measure, reduce_pair,
  pair_to_default_measure, microid_of_dirac_eq, pair_to_default_body,
  body_of_poly_of_gen_eq,
  function.comp_app, function.comp_app],
end

lemma nface_eq_self_of_vspan_mem_uperp {A : set V} {u : V}
(h : vector_span ℝ A ≤ vector_orth u) : normal_face A u = A :=
begin
  apply subset_antisymm,
  {
    apply normal_face_subset,
  },
  {
    intros a ha,
    simp only [mem_normal_face],
    refine ⟨ha, _⟩,
    intros b hb,
    have hab : a - b ∈ vector_orth u,
    {
      apply h,
      apply submodule.subset_span,
      exact ⟨a, b, ha, hb, rfl⟩,
    },
    simp only [vector_orth] at hab,
    replace hab := inner_left_of_mem_orthogonal_singleton _ hab,
    apply le_of_eq,
    symmetry,
    simpa only [inner_sub_left, sub_eq_zero] using hab,
  },
end

lemma span_reduced_microid_eq_TS (k : ℕ)
(u : metric.sphere (0 : V) 1) :
span_of_convex_body ∘ pair_to_microid ∘ (reduce_pair : microid_pair k u → microid_pair k u) =
pair_to_TS ∘ (reduce_pair : microid_pair k u → microid_pair k u) :=
begin
  funext pair,
  simp only [function.comp_app],
  simp only [reduced_microid_eq_default_body, pair_to_default_body, pair_to_TS],
  simp only [convex_body_of_polytope],
  have is_poly := (polytope_of_microid_generator pair.2.1).property,
  rw [TS_poly_eq_vspan_face is_poly],
  rcases pair.2.2 with ⟨h0, h1, h2, h3⟩,
  rw [←subtype.val_eq_coe, nface_eq_self_of_vspan_mem_uperp h1],
  simp only [span_of_convex_body],
end

lemma subset_diff {A : set V} (h : (0 : V) ∈ A) : A ⊆ diff A :=
begin
  intros v vA,
  refine ⟨v, 0, vA, h, _⟩,
  simp only [vsub_eq_sub, sub_zero],
end

lemma vspan_eq_span_of_mem_zero {A : set V} (h : (0 : V) ∈ A) :
vector_span ℝ A = submodule.span ℝ A :=
begin
  apply le_antisymm,
  {
    simp only [vector_span, submodule.span_le],
    rintro x ⟨a, b, ha, hb, rfl⟩,
    simp only [vsub_eq_sub, set_like.mem_coe],
    refine submodule.sub_mem _ _ _,
    all_goals {
      apply submodule.subset_span,
      assumption,
    },
  },
  {
    simp only [vector_span],
    apply submodule.span_mono,
    exact subset_diff h,
  },
end

lemma reduced_microid_subset_TS {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
(pair_to_microid (reduce_pair pair)).val ⊆ pair_to_TS (reduce_pair pair) :=
begin
  refine subset_trans submodule.subset_span
    (subset_of_eq (congr_arg coe _)),
  revert pair,
  have := function.funext_iff.mp (span_reduced_microid_eq_TS k u),
  convert this,
  ext,
  refine forall_congr _,
  simp only [function.comp_app, span_of_convex_body],
  intro pair,
  rw [reduced_microid_eq_default_body, pair_to_default_body,
    convex_body_of_polytope, subtype.val_eq_coe, subtype.coe_mk],
  rw [vspan_eq_span_of_mem_zero (pair.2.2.1)],
end

noncomputable def pair_to_default_space {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V :=
TS (pair_to_default_body pair).val u.val

lemma TS_reduce_eq_default_space {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
pair_to_TS (reduce_pair pair) = pair_to_default_space pair :=
begin
  simp only [pair_to_TS, pair_to_default_space, reduced_microid_eq_default_body],
  refl,
end

lemma reduced_default_body_eq {k : ℕ}{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
pair_to_default_body (reduce_pair pair) = pair_to_default_body pair :=
begin
  simp only [pair_to_default_body, reduce_pair],
end

lemma default_space_eq_TS_of_reduced {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
pair_to_default_space (reduce_pair pair) = pair_to_TS (reduce_pair pair) :=
begin
  simp only [pair_to_default_space, TS_reduce_eq_default_space, reduced_default_body_eq],
end

noncomputable def pair_to_space_pair {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V × submodule ℝ V :=
⟨pair_to_TS pair, pair_to_default_space pair⟩

lemma pair_to_space_pair_def {k : ℕ}
{u : metric.sphere (0 : V) 1} :
@pair_to_space_pair V _ _ k u = λ pair, ⟨pair_to_TS pair, pair_to_default_space pair⟩ :=
rfl

noncomputable def paircol_span {k : ℕ}
{u : metric.sphere (0 : V) 1}
(D : multiset (microid_pair k u)) : submodule ℝ V :=
(D.map pair_to_default_space).sum

lemma nonempty_prune_triple {k : ℕ} : nonempty (prune_triple V k) :=
begin
  refine ⟨⟨⟨0, _⟩, 0, 0⟩⟩,
  simp only [mem_closed_ball_zero_iff, norm_zero, zero_le_one],
end

lemma cuspiness_lipschitz {k : ℕ}
(tr : prune_triple V k)
(u v : V) :
|cuspiness' u tr - cuspiness' v tr| ≤ dist u v :=
begin
  simp only [cuspiness', ←sub_div, ←inner_sub_right, abs_div],
  simp only [←is_R_or_C.abs_to_real],
  refine le_trans (div_le_div_of_le_right
    (abs_inner_le_norm (prune_direction tr) (u - v)) _) _,
  {
    apply is_R_or_C.abs_nonneg,
  },
  {
    simp only [is_R_or_C.abs_to_real,
      abs_eq_self.mpr (norm_nonneg _)],
    apply div_le_of_nonneg_of_le_mul,
    {
      apply norm_nonneg,
    },
    {
      apply dist_nonneg,
    },
    {
      conv {to_lhs, rw [mul_comm]},
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      simp only [←dist_eq_norm, subtype.dist_eq],
    },
  },
end

lemma support_locally_linear_of_cuspy {k : ℕ}
{G : microid_generator_space V k}
{u : metric.sphere (0 : V ) 1}
{ε : ℝ}
(εpos : ε > 0)
(h : ∀ tr : prune_triple V k,
valid_prune_triple tr u → (prune_triple_generator tr) = G → cuspiness u tr ≥ ε) :
supp_locally_linear (metric.ball u.val ε) (body_of_microid_generator G) :=
begin
  rw [normal_face_singleton_iff_locally_linear metric.is_open_ball],
  rcases generator_face_nonempty G u with ⟨m, hm⟩,
  refine ⟨G.val m, _⟩,
  intros v hv,
  simp only [body_of_microid_generator, convex_body.normal_face],
  simp only [normal_face_spanned_by_verts],
  convert convex_hull_singleton (G.val m),
  have lem : ∀ l : fin k.succ, G.val l ≠ G.val m →
    ⟪G.val m - G.val l, v⟫_ℝ > 0,
  {
    intros l hh,
    let tr : prune_triple V k := ⟨G, m, l⟩,
    have valid : valid_prune_triple tr u,
    {
      simp only [valid_prune_triple,
      prune_cusp, prune_cusp_index,
      prune_secondary, prune_secondary_index,
      prune_gen_fn, tr],
      split,
      {
        simp only [generator_face, finset.mem_coe, finset.mem_filter] at hm,
        exact hm.2,
      },
      {tauto},
    },
    have := h tr valid rfl,
    change cuspiness' u.val tr ≥ ε at this,
    replace : cuspiness' v tr > 0,
    {
      refine lt_of_lt_of_le _ (ge_sub_abs (cuspiness' v tr) (cuspiness' u.val tr)),
      refine lt_of_lt_of_le _ (sub_le_sub this (cuspiness_lipschitz _ _ _)),
      simpa only [metric.mem_ball, sub_pos] using hv,
    },
    {
      simp only [cuspiness', prune_direction,
        prune_cusp, prune_secondary,
        prune_cusp_index, prune_secondary_index,
        prune_gen_fn, tr] at this,
      exact dividend_pos this (norm_nonneg _),
    },
  },
  apply subset_antisymm,
  {
    intros x hx,
    simp only [set.mem_singleton_iff],
    simp only [generator_face, finset.mem_coe, finset.mem_filter] at hm,
    simp only [mem_normal_face] at hx,
    rcases hx.1 with ⟨l, hl, rfl⟩,
    by_contra hh,
    suffices c : ⟪G.val m - G.val l, v⟫_ℝ > 0,
    {
      simp only [inner_sub_left, gt_iff_lt, sub_pos] at c,
      replace hx := hx.2 (G.val m) (set.mem_range_self _),
      linarith,
    },
    {
      exact lem l hh,
    },
  },
  {
    simp only [set.singleton_subset_iff, mem_normal_face],
    refine ⟨set.mem_range_self _, _⟩,
    intros y hy,
    rcases hy with ⟨l, rfl⟩,
    by_cases hh : G.val l = G.val m,
    {
      simp only [hh],
      apply le_refl,
    },
    {
      apply le_of_lt,
      rw [←sub_pos, ←inner_sub_left],
      exact lem l hh,
    },
  },
end

/- lemma lemma_vspan_subset_span {A : set V} :
(vector_span ℝ A : set V) ⊆ submodule.span ℝ A :=
begin
  simp only [vector_span],
end -/

lemma zero_normal_face_eq (A : set V) :
normal_face A 0 = A :=
begin
  ext,
  simp only [normal_face, set.mem_set_of],
  split,
  {
    intro h,
    exact h.1,
  },
  {
    intro h,
    refine ⟨h, _⟩,
    simp only [inner_zero_right],
    intros y hy,
    apply le_refl,
  }
end

lemma orthogonal_projection_eq_zero_iff (E : submodule ℝ V) :
Eᗮ = 0 ↔ E = ⊤ :=
begin
  exact submodule.orthogonal_eq_bot_iff,
end

/- lemma normal_face_by_supp (K : convex_body V) (u : V) :
(normal_face K.val u) = { x : V | x ∈ K.val ∧ ⟪x, u⟫_ℝ = K.supp u } := sorry
 -/

lemma TS_zero_of_cuspy_generators {k : ℕ}
{μ : microid_measure V k}
{u : metric.sphere (0 : V) 1}
{ε : ℝ}
(εpos : ε > 0)
(h : ∀ (tr : prune_triple V k),
valid_prune_triple tr u → prune_triple_generator tr ∈ msupport μ → cuspiness u tr ≥ ε) :
TS_microid_measure u μ = 0 :=
begin
  suffices hε : metric.ball u.val ε ⊆ pre_touching_cone (microid_of_measure μ).val u,
  {
    have span_top : vector_span ℝ (pre_touching_cone (microid_of_measure μ).val u) = ⊤,
    {
      refine vector_span_top_of_ball_subset εpos hε,
    },
    have : pre_touching_cone (microid_of_measure μ).val u =
      touching_cone (microid_of_measure μ).val u,
    {
      refine touching_cone_unique_face _ _ _ _ _,
      {
        conv {
          congr, skip,
          rw [←zero_normal_face_eq (pre_touching_cone (microid_of_measure μ).val u)],
        },
        exact normal_face_is_face (pre_touching_cone_convex _ _) 0,
      },
      rw [relint_eq_int (vector_span_top_of_ball_subset εpos hε), mem_interior],
      exact ⟨metric.ball u.val ε, hε, metric.is_open_ball, metric.mem_ball_self εpos⟩,
    },
    simp only [TS_microid_measure, TS, orthogonal_projection_eq_zero_iff],
    rw [this] at hε,
    refine span_top_of_ball_subset εpos hε,
  },
  intros v hv,
  simp only [pre_touching_cone, outer_normal_cone, set.mem_set_of],
  suffices ll : supp_locally_linear (metric.ball u.val ε)
    (microid_of_measure μ),
  {
    rcases ll with ⟨x, ll⟩,
    rw [normal_face_singleton_iff_locally_linear_with (metric.is_open_ball)] at ll,
    simp only [convex_body.normal_face] at ll,
    rw [ll v hv, ll ↑u (metric.mem_ball_self εpos)],
  },
  {
    apply microid_supp_locally_linear_of_generators εpos,
    intros G hG,
    apply support_locally_linear_of_cuspy εpos,
    intros tr valid htrG,
    refine h tr valid _,
    rw [htrG],
    exact hG,
  },
end

lemma cuspiness_nonneg {k : ℕ}
{tr : prune_triple V k}
{u : metric.sphere (0 : V) 1}
(h : valid_prune_triple tr u) : cuspiness u tr ≥ 0 :=
begin
  simp only [valid_prune_triple] at h,
  simp only [cuspiness, prune_direction,
    prune_cusp, prune_cusp_index,
    prune_secondary, prune_secondary_index,
    prune_gen_fn] at h ⊢,
  apply div_nonneg,
  {
    simp only [inner_sub_left, sub_nonneg],
    tauto,
  },
  {apply norm_nonneg},
end

lemma exists_prune_triple_seq {k : ℕ}
{μ : microid_measure V k}
{u : metric.sphere (0 : V) 1}
(h : TS_microid_measure u μ ≠ 0) :
∃ t : ℕ → prune_triple V k,
(∀ n : ℕ, valid_prune_triple (t n) u) ∧
(∀ n : ℕ, prune_triple_generator (t n) ∈ msupport μ) ∧
filter.tendsto ((cuspiness u) ∘ t) filter.at_top (𝓝 (0 : ℝ)) :=
begin
  suffices hex : ∀ ε : ℝ,
  ∃ tr : prune_triple V k, ε > 0 →
  valid_prune_triple tr u ∧
  prune_triple_generator tr ∈ msupport μ ∧ cuspiness u tr < ε,
  {
    choose tℝ htℝ using hex,
    rcases exists_seq_strict_anti_tendsto (0 : ℝ)
      with ⟨ε, -, εpos, εtt⟩,
    let t := tℝ ∘ ε,
    refine ⟨t, _, _, _⟩,
    {
      intro n,
      exact (htℝ (ε n) (εpos n)).1,
    },
    {
      intro n,
      exact (htℝ (ε n) (εpos n)).2.1,
    },
    {
      have εtt' := tendsto_nhds_within_of_tendsto_nhds_of_eventually_within
        _ εtt (filter.eventually_of_forall εpos),
      have : filter.tendsto (cuspiness u ∘ tℝ) (𝓝[preorder.lt 0] 0) (𝓝 0),
      {
        simp only [filter.tendsto_iff_eventually],
        intros p ep,
        simp only [filter.has_basis.eventually_iff metric.nhds_basis_ball] at ep,
        simp only [filter.has_basis.eventually_iff metric.nhds_within_basis_ball,
          function.comp_app],
        rcases ep with ⟨i, ipos, hi⟩,
        refine ⟨i, ipos, _⟩,
        rintro x ⟨hx, xpos⟩,
        apply hi,
        simp only [real.ball_eq_Ioo] at hx ⊢,
        split,
        {
          simp only [zero_sub],
          refine lt_of_lt_of_le (neg_neg_of_pos ipos) _,
          apply cuspiness_nonneg,
          exact (htℝ x xpos).1,
        },
        {
          exact lt_trans (htℝ x xpos).2.2 hx.2,
        },
      },
      have := filter.tendsto.comp this εtt',
      rw [function.comp.assoc] at this,
      exact this,
    },
  },
  intros ε,
  by_cases εpos : ε > 0, rotate,
  {
    rcases nonempty_prune_triple with ⟨tr⟩,
    refine ⟨tr, _⟩,
    {
      intro h,
      contradiction,
    },
  },
  {
    by_contra hass,
    push_neg at hass,
    apply h,
    apply TS_zero_of_cuspy_generators εpos,
    intros tr valid htr,
    exact (hass tr).2 valid htr,
  },
end

lemma exists_pair {k : ℕ}
{μ : microid_measure V k}
{u : metric.sphere (0 : V) 1}
(h : TS_microid_measure u μ ≠ 0) :
∃ p : microid_pair k u,
pair_to_measure p = μ :=
begin
  rcases exists_prune_triple_seq h with ⟨t, valid, genμ, tt⟩,
  rcases pruning_lemma valid tt with ⟨G, hzm, hnz, hup, hcl⟩,
  refine ⟨⟨μ, G, _⟩, _⟩,
  {
    refine ⟨hzm, hup, _, _⟩,
    {
      rw [TS_poly_eq_vspan_face (polytope_of_microid_generator G).property u],
      rw [←subtype.val_eq_coe, nface_eq_self_of_vspan_mem_uperp hup],
      exact hnz,
    },
    {
      simp only [in_combinatorial_closure] at hcl,
      intros C hC hsupp,
      rw [body_of_poly_of_gen_eq] at hsupp,
      have := hcl C hC hsupp,
      rw [msupport_microid_eq_closure μ hC],
      refine set.mem_of_subset_of_mem _ this,
      apply closure_mono,
      intros v hv,
      simp only [set.mem_Union] at hv ⊢,
      rcases hv with ⟨K, ⟨nK, -, rfl⟩, vsupp⟩,
      refine ⟨prune_triple_generator (t nK), genμ nK, _⟩,
      simp only [function.comp_app] at vsupp,
      exact vsupp,
    },
  },
  {
    simp only [pair_to_measure],
  },
end

lemma nonzero_of_mem_of_semicritical
{Es : multiset (submodule ℝ V)}
(h : semicritical_spaces Es) :
∀ E : submodule ℝ V, E ∈ Es → E ≠ ⊥ :=
begin
  intros E hE,
  let S : multiset (submodule ℝ V) := {E},
  suffices hd : dim S.sum ≥ S.card,
  {
    by_contra,
    simp only [h, S] at hd,
    rw [multiset.sum_singleton E, multiset.card_singleton] at hd,
    rw [h] at hd,
    change finite_dimensional.finrank ℝ (⊥ : submodule ℝ V) ≥ 1 at hd,
    simp only [finrank_bot, gt_iff_lt, not_lt_zero'] at hd,
    linarith,
  },
  refine h S _,
  simp only [S, multiset.singleton_le],
  exact hE,
end

lemma exists_pair_multiset {k : ℕ}
(μs : multiset (microid_measure V k))
(u : metric.sphere (0 : V) 1)
(hTS : semicritical_spaces (μs.map (TS_microid_measure u))) :
∃ C : multiset (microid_pair k u),
C.map pair_to_measure = μs :=
begin
  induction μs using pauls_multiset_induction,
  {
    refine ⟨0, _⟩,
    simp only [multiset.map_zero],
  },
  {
    have hTS': semicritical_spaces (μs_C'.map (TS_microid_measure u)),
    {
      simp only [multiset.map_cons] at hTS,
      refine semicritical_of_le (multiset.le_cons_self _ _) hTS,
    },
    rcases μs_ᾰ hTS' with ⟨C', hC'⟩,
    have μs_a_nonzero : TS_microid_measure u μs_a ≠ ⊥,
    {
      refine nonzero_of_mem_of_semicritical hTS _ _,
      simp only [multiset.map_cons],
      exact multiset.mem_cons_self _ _,
    },
    rcases exists_pair μs_a_nonzero with ⟨E, hE⟩,
    refine ⟨E ::ₘ C', _⟩,
    simp only [hC', hE, multiset.map_cons],
  },
end

theorem matryoshka_reduction {k : ℕ}
{u : metric.sphere (0 : V) 1}
{D C : multiset (microid_pair k u)}
(hdim : dim V = (D + C).card + 1) :
u ∈ msupport (bm.area ((D.map pair_to_default_body) + C.map pair_to_microid)) →
u ∈ msupport (bm.area ((D + C).map pair_to_microid))
:=
begin
  revert C,
  induction D using pauls_multiset_induction,
  {
    intros C hdim hu,
    simpa only [multiset.map_zero, zero_add] using hu,
  },
  {
    intros C hdim hu,
    let C' := (reduce_pair D_a) ::ₘ C,
    have hdim' : dim V = (D_C' + C').card + 1,
    {
      simp only [C', multiset.card_add, multiset.card_cons] at hdim ⊢,
      rw [hdim],
      ring,
    },
    have goal' := D_ᾰ hdim',
    simp only [multiset.map_add, multiset.map_cons] at goal',
    rw [multiset.add_cons, ←multiset.cons_add] at goal',
    rw [reduced_microid_eq_default_body] at goal',
    simp only [multiset.map_add, multiset.map_cons] at hu,
    replace hu := goal' hu,
    clear D_ᾰ goal',
    simp only [multiset.cons_add, multiset.map_cons],
    rw [multiset.add_cons, ←multiset.map_add] at hu,
    have defp := D_a.2.2,
    refine defp.2.2.2 _ _ hu,
    simp only [multiset.card_map, multiset.card_add],
    simp only [multiset.card_add, multiset.card_cons] at hdim,
    rw [hdim],
    ring,
  },
end

end default_reduction

variables {V : Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma TS_microid_proj_eq_proj_TS_microid {k : ℕ}
(μ : microid_measure V k)
(E : submodule ℝ V)
(u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) :
TS_microid_measure (uncoe_sph E u uE) (project_microid_measure E μ) =
(TS_microid_measure u μ).map (proj E) :=
begin
  simp only [TS_microid_measure, uncoe_sph],
  rw [TS_orthogonal_projection _ uE, microid_proj_eq_proj_microid],
  simp only [proj_body, subtype.val_eq_coe],
  refl,
end

lemma TS_default_body_eq_TS_default_measure (k : ℕ)
(u : metric.sphere (0 : V) 1) (x : microid_pair k u) :
TS (pair_to_default_body x).val u.val = TS_microid_measure u (pair_to_default_measure x) :=
begin
  simp only [TS_microid_measure, pair_to_default_measure, pair_to_default_body,
    microid_of_dirac_eq, body_of_poly_of_gen_eq],
end

section blabb

lemma u_mem_sum_TS_orth
{k : ℕ}
{u : metric.sphere (0 : V) 1}
{E : submodule ℝ V}
(A : multiset (microid_pair k u))
(h : E = (A.map pair_to_TS).sum) :
u.val ∈ Eᗮ :=
begin
  revert E,
  induction A using pauls_multiset_induction,
  {
    intros E h,
    simp only [multiset.map_zero, multiset.sum_zero, submodule.zero_eq_bot] at h,
    simp only [h, submodule.bot_orthogonal_eq_top],
  },
  {
    intros E h,
    simp only [multiset.map_cons, multiset.sum_cons, submodule.add_eq_sup] at h,
    simp only [h],
    intros x hx,
    simp only [submodule.mem_sup] at hx,
    rcases hx with ⟨y, hy, z, hz, rfl⟩,
    simp only [inner_add_left],
    convert add_zero (0 : ℝ),
    {
      apply inner_left_of_mem_orthogonal_singleton,
      simp only [pair_to_TS] at hy,
      exact TS_le_uperp _ _ hy,
    },
    {
      exact A_ᾰ rfl z hz,
    },
  },
end

lemma semicritical_subprojection
{k : ℕ}
{u : metric.sphere (0 : V) 1}
(A B : multiset (microid_pair k u))
(E : submodule ℝ V)
(SP : multiset (microid_measure Eᗮ k))
(hAE : E = (A.map pair_to_TS).sum)
(hA2 : dim E = A.card)
(hB : semicritical_spaces ((A + B).map pair_to_TS))
(hSP : SP = B.map (project_microid_measure Eᗮ ∘ pair_to_measure)):
semicritical_spaces
(SP.map (TS_microid_measure (uncoe_sph Eᗮ u (u_mem_sum_TS_orth A hAE)))) :=
begin
  simp only [hSP],
  rw [multiset.map_map, map_lambda],
  simp only [function.comp_app, TS_microid_measure,
    microid_proj_eq_proj_microid, proj_body, uncoe_sph],
  simp only [←TS_orthogonal_projection],
  let C := A.map pair_to_TS,
  let D := B.map pair_to_TS,
  suffices hD : semicritical_spaces (D.map (λ W, W.map (proj Eᗮ))),
  {
    simpa only [D, multiset.map_map, map_lambda, function.comp_app] using hD,
  },
  simp only [multiset.map_add] at hB,
  change semicritical_spaces (C + D) at hB,
  refine semicritical_spaces_factorization _ _ _ hB,
  refine ⟨_, _⟩,
  {
    simpa only [C, multiset.card_map] using hA2,
  },
  {
    intros F hF,
    simp only [hAE],
    apply le_sum_multiset_of_mem,
    exact hF,
  },
end

end blabb

--set_option pp.implicit true
theorem matryoshka_principle {k : ℕ}
(n₀ : ℕ)
(n : ℕ)
(hn : n ≤ n₀)
(μs : multiset (microid_measure V k))
(u : metric.sphere (0 : V) 1)
--(hdim1 : n ≥ 1)
(hdim2 : dim V = n + 1)
(hdim3 : μs.card = n)
(hTS : semicritical_spaces (μs.map (TS_microid_measure u))) :
u ∈ msupport (bm.area (μs.map microid_of_measure)) :=
begin
  unfreezingI {
    induction n₀ with n₀ ih generalizing n μs V,
    {
      have : μs = 0,
      {
        rw [←multiset.card_eq_zero, hdim3],
        simpa only [le_zero_iff] using hn,
      },
      rw [this],
      simp only [multiset.empty_eq_zero, multiset.map_zero, bm.area_empty],
    },
    {
      by_cases hn' : n = 0,
      {
        have : μs = 0,
        {
          rw [←multiset.card_eq_zero, hdim3, hn'],
        },
        rw [this],
        simp only [multiset.map_zero, bm.area_empty],
      },
      rcases exists_pair_multiset μs u hTS with
        ⟨C, rfl⟩,
      let D := C.map pair_to_space_pair,
      let uperp := vector_orth u.val,
      have :=
      begin
        clear ih,
        refine semicritical_switching D uperp _ _ _ _ _,
        {
          simp only [D, multiset.card_map] at hdim3 ⊢,
          rw [hdim3],
          exact nat.pos_of_ne_zero hn',
        },
        {
          simpa only [multiset.map_map] using hTS,
        },
        {
          have dim_uperp : dim uperp = n,
          {
            suffices h : dim uperp + 1 = dim V,
            {
              rw [hdim2] at h,
              exact nat.add_right_cancel h,
            },
            {
              have : dim (submodule.span ℝ ({u} : set V)) = 1,
              {
                apply finrank_span_singleton,
                have := metric.mem_sphere.mp u.prop,
                have z_ne_o: 1 ≠ (0 : ℝ) := zero_ne_one.symm,
                rw [←this] at z_ne_o,
                apply dist_ne_zero.mp z_ne_o,
              },
              rw [←this],
              rw [nat.add_comm],
              refine dim_add_dim_orthogonal _,
            },
          },
          symmetry,
          simpa only [dim_uperp, multiset.card_map] using hdim3,
        },
        {
          clear hn hdim2 hdim3 hTS,
          intros x xD,
          rcases multiset.mem_map.mp xD with ⟨c, ⟨cC, rfl⟩⟩,
          simp only [pair_to_space_pair],
          split,
          {apply TS_le_uperp},
          {
            simp only [pair_to_default_space, pair_to_default_body, submodule.span_le],
            apply TS_le_uperp,
/-          simp only [polytope_to_convex_body],
            have is_default_poly := c.snd.2,
            exact is_default_poly.1, --simp only [is_default_polytope] at is_default_poly, -/
          },
        },
        {
          intros x xD,
          rcases multiset.mem_map.mp xD with ⟨c, ⟨cC, rfl⟩⟩,
          simp only [pair_to_space_pair, pair_to_default_space,
            pair_to_default_body, convex_body_of_polytope],
          have is_default_poly := c.snd.2,
          exact is_default_poly.2.2.1,
        },
      end,
      rcases this with ⟨A, B, h⟩,
      rcases h with ⟨hAB, hBD, h1, h2, h3⟩,
      rcases multiset_exists_of_le_map hBD with ⟨B', ⟨hB'C, rfl⟩⟩,
      rcases multiset_exists_of_le_map hAB with ⟨A', ⟨hA'B', rfl⟩⟩,
      /- let F := (B' - A').map pair_to_default_measure + (C - B').map pair_to_measure,
      let G := A'.map pair_to_default_measure,
      let E : submodule ℝ V := (A'.map pair_to_default_space).sum,
      have uE : u.val ∈ Eᗮ,
      {
        suffices h : E ≤ uperp,
        {
          simp only [submodule.mem_orthogonal],
          rintro x xE,
          apply inner_left_of_mem_orthogonal_singleton,
          exact h xE,
        },
        {
          refine sum_multiset_le _,
          rintro W hW,
          simp only [pair_to_default_space, multiset.mem_map] at hW,
          rcases hW with ⟨a, hA, rfl⟩,
          apply TS_le_uperp,
        },
      }, -/
      /- let pF := F.map (project_microid_measure Eᗮ),
      let n' := pF.card,
      have hn' : n' ≤ n₀,
      {
        simp only [n', pF, F, multiset.card_map, multiset.card_add
          --, multiset.card_add, multiset.card_sub, hA'B', hB'C
        ],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
        simp only [add_tsub_cancel_left],
        simp only [multiset.card_map, multiset.card_add] at hdim3,
        calc t.card + tt.card = n - A'.card : _
      ...  ≤ n - 1 : _
      ...  ≤ n₀ : _,
        {
          rw [←hdim3],
          admit,
        },
        {
          apply nat.sub_le_sub_left n,
          apply nat.succ_le_of_lt,
          simpa only [multiset.card_map] using h3,
        },
        {
          norm_num,
          assumption,
        },
      },
      have EA' : dim E = A'.card,
      {
        apply le_antisymm,
        {admit},
        {
          simp only [multiset.map_map, pair_to_space_pair] at h1,
          rw [←multiset.card_map pair_to_default_space],
          --simp only [pair_to_default_space] at E,
          refine h1 _ _,
          refine le_trans _ (multiset.le_add_right _ _),
          simp only [function.comp_app],
          exact multiset.map_le_map hA'B',
        }
      },
      have hdim2' : dim Eᗮ = n' + 1,
      {
        apply le_antisymm,
        {
          suffices dimE : dim E ≥ n - n',
          {
            simp only [ge_iff_le, tsub_le_iff_right, eq_tsub_of_add_eq hdim2.symm] at dimE,
            rw [←dim_add_dim_orthogonal E, nat.add_assoc] at dimE,
            norm_num at dimE,
            exact dimE,
          },
          {
            rw [EA'],
            norm_num,
            simp only [hdim3.symm, multiset.card_map],
            simp only [pF, F, n', multiset.card_map, multiset.card_add],

            rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
            rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
            simp only [add_tsub_cancel_left, multiset.card_add],
            simp only [add_assoc],
          },
        },
        {
          suffices dimE : dim E ≤ n - n',
          {
            simp only [ge_iff_le, tsub_le_iff_right, eq_tsub_of_add_eq hdim2.symm] at dimE,
            rw [←dim_add_dim_orthogonal E, tsub_tsub] at dimE,
            admit,
          },
          {
            rw [multiset.map_map, pair_to_space_pair_def, multiset.card_map] at h2,
            rw [h2],
            rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
            rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
            simp only [add_tsub_cancel_left,
                       multiset.card_map, n', pF, F,
                       multiset.card_add,
                       hdim3.symm],
            generalizes [A'.card = A'c, t.card = tc, tt.card = ttc],
            rw [nat.add_assoc],
            simp only [add_tsub_cancel_right],
          },
        },
      },
      have hdim3' : pF.card = n' := rfl,
      let u' := uncoe_sph Eᗮ u uE, -/
      let A := A'.map reduce_pair,
      let B := (B' - A').map reduce_pair + (C - B'),
      let E := (A.map pair_to_TS).sum,
      let SP := B.map (project_microid_measure Eᗮ ∘ pair_to_measure),
      have sc_AB : semicritical_spaces ((A + B).map pair_to_TS),
      {
        have hA : A.map pair_to_TS = A'.map pair_to_default_space,
        {simp only [multiset.map_map, function.comp_app, TS_reduce_eq_default_space]},
        have hB : B.map pair_to_TS = (B' - A').map pair_to_default_space + (C - B').map pair_to_TS,
        {
          simp only [B, multiset.map_map, multiset.map_add, function.comp_app,
            TS_reduce_eq_default_space],
        },
        have hAB : (A + B).map pair_to_TS = B'.map pair_to_default_space + (C - B').map pair_to_TS,
        {
          rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
          rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
          simp only [A, B, add_tsub_cancel_left, multiset.map_map, multiset.map_add,
            function.comp_app, TS_reduce_eq_default_space, add_assoc],
        },
        rw [hAB],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
        simp only [add_tsub_cancel_left] at hAB ⊢,
        simp only [D, pair_to_space_pair_def] at h1,
        simpa only [multiset.map_add, multiset.map_map, add_tsub_cancel_left,
          function.comp_app] using h1,
      },
      have dimE : dim E = A.card,
      {
        rw [multiset.card_map] at h2 ⊢,
        rw [←h2],
        suffices h : E = ((A'.map pair_to_space_pair).map prod.snd).sum,
        {rw [h]},
        {
          simp only [multiset.map_map, E, pair_to_space_pair_def,
            function.comp_app, TS_reduce_eq_default_space],
        },
      },
      have sc_sp := semicritical_subprojection A B E SP rfl dimE sc_AB rfl,
      have cardSP : A.card + SP.card = n,
      {
        simp only [multiset.card_map, map_add],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
        simp only [add_tsub_cancel_left],
        simpa only [multiset.card_map, multiset.card_add, add_assoc] using hdim3,
      },
      have dimEp : dim Eᗮ = SP.card + 1,
      {
        have rn := dim_add_dim_orthogonal E,
        rw [hdim2, ←cardSP, dimE, add_assoc] at rn,
        zify at rn ⊢,
        exact add_left_cancel rn,
      },
      have cardSPle : SP.card ≤ n₀,
      {
        have cardAgt : A.card > 0 := by simpa only [multiset.card_map] using h3,
        rw [←cardSP] at hn,
        apply nat.le_of_lt_succ,
        refine nat.lt_of_lt_of_le _ hn,
        simpa only [lt_add_iff_pos_left] using cardAgt,
      },
      /- have Fsc : semicritical_spaces (pF.map (TS_microid_measure u')),
      {
        simp only [multiset.map_map, function.comp_app],
        simp only [u', TS_microid_proj_eq_proj_TS_microid _ Eᗮ u uE],
        let A := A'.map pair_to_default_space,
        let Z := (B' - A').map pair_to_default_space + (C - B').map pair_to_TS,
        have := semicritical_spaces_factorization
          A Z ⟨(_ : dim E = A.card), _⟩ _,
        {
          have : Z.map (λ W, W.map (proj Eᗮ)) = F.map (λ μ, (TS_microid_measure u μ).map (proj Eᗮ)),
          {
            simp only [Z, pair_to_default_space, pair_to_TS, multiset.map_add, multiset.map_map],
            rw [TS_default_body_eq_TS_default_measure k u],
          }
        }
      }, -/
      have finp := ih SP.card cardSPle SP _ dimEp rfl sc_sp,
      clear ih hTS hn hAB hBD h2 h3 h1 sc_sp,

      have hE : E ≤ ⊤ := le_top,
      let Am := A.map pair_to_microid,
      let Bm := B.map pair_to_microid,
      have vc : bm.is_vol_coll Am E,
      {
        split,
        {simpa only [multiset.card_map, Am] using dimE},
        {
          simp only [Am, multiset.map_map],
          intros K hK,
          rcases multiset.mem_map.mp hK with ⟨x, hx, rfl⟩,
          simp only [E],
          have : convex_body_subset (pair_to_TS (reduce_pair x)) ((pair_to_microid ∘ reduce_pair) x) :=
          begin
            apply reduced_microid_subset_TS,
          end,
          refine subset_trans this _,
          apply set_like.coe_subset_coe.mpr,
          refine le_sum_multiset_of_mem _,
          apply multiset.mem_map.mpr,
          refine ⟨reduce_pair x, _, rfl⟩,
          apply multiset.mem_map.mpr,
          exact ⟨x, hx, rfl⟩,
        },
      },
      have ac : bm.is_area_coll (Am + Bm),
      {
        change finite_dimensional.finrank ℝ V = (Am + Bm).card + 1,
        change dim V = (Am + Bm).card + 1,
        rw [hdim2],
        simp only [multiset.card_add, multiset.card_map, add_left_inj],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
        rw [add_tsub_cancel_left],
        rw [add_tsub_cancel_left],
        rw [←add_assoc],
        symmetry,
        simp only [multiset.card_map, multiset.card_add] at hdim3,
        assumption,
      },
      have sc : semicritical_spaces (Am.map span_of_convex_body),
      {
        simp only [multiset.map_map, Am, A],
        rw [span_reduced_microid_eq_TS, ←multiset.map_map],
        have : A.map pair_to_TS ≤ (A + B).map pair_to_TS,
        {simp only [multiset.map_add, le_add_iff_nonneg_right, zero_le]},
        exact semicritical_of_le this sc_AB,
      },
      have heq := bm.factorize_area vc ac sc,
      have tmp : multiset.map microid_of_measure SP = proj_coll Eᗮ Bm,
      {
        simp only [SP, Bm, proj_coll, multiset.map_map, pair_to_microid],
        simp only [function.comp_app],
        simp only [proj_microid_of_measure Eᗮ], -- rw does not work because of lambda!
      },
      have finp' := set.mem_image_of_mem (coe_sph Eᗮ) finp,
      rw [tmp, ←heq, coe_uncoe_sph] at finp',

      have : Am + Bm = B'.map pair_to_default_body + (C - B').map pair_to_microid,
      {
        simp only [Am, Bm, A, B, multiset.map_add, multiset.map_map],
        rw [←add_assoc],
        congr,
        rw [←multiset.map_add],
        simp only [function.comp_app, reduced_microid_eq_default_body],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        simp only [add_tsub_cancel_left],
      },
      rw [this] at finp',
      have : dim V = C.card + 1,
      {
        symmetry,
        simpa only [multiset.card_map, hdim2, add_left_inj] using hdim3,
      },
      rcases multiset.le_iff_exists_add.mp hB'C with ⟨D, rfl⟩,
      rw [add_tsub_cancel_left] at finp',
      have := matryoshka_reduction this finp',
      simpa only [multiset.map_map, pair_to_microid] using this,
    },
  },
end