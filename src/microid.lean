import convex convex_body multiset brunn_minkowski
  finset polytope touching_cone
  linear_algebra.affine_space.affine_subspace
  topology.continuous_function.bounded
  measure_theory.measure.measure_space
  analysis.convex.basic
  data.multiset.basic
  topology.basic

open_locale pointwise

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

open_locale pointwise

section types

variables (V : Type)
[inner_product_space ℝ V] [finite_dimensional ℝ V]

abbreviation unbounded_microid_generator (k : ℕ) := fin k.succ → V
abbreviation microid_generator_space (k : ℕ) := metric.closed_ball (0 : fin k.succ → V) 1

noncomputable instance borel_measurable_space_microid_generator_space (k : ℕ) :=
borel
(microid_generator_space V k)

instance borel_space_microid_generator_space (k : ℕ) :
borel_space (microid_generator_space V k) :=
⟨rfl⟩

instance proper_space_microid_generator_space (k : ℕ) :
compact_space (microid_generator_space V k) :=
{
  compact_univ :=
  begin
    apply compact_iff_compact_in_subtype.mpr,
    simp only [set.image_univ, subtype.range_coe_subtype],
    exact proper_space.is_compact_closed_ball 0 1,
  end
}

def function_of_generator {k : ℕ}
(G : microid_generator_space V k) : fin k.succ → V := G.val

abbreviation microid_measure (k : ℕ) :=
measure_theory.finite_measure (microid_generator_space V k)

end types


axiom microid_of_measure {V : Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]
{k : ℕ} (μ : microid_measure V k) :
convex_body V

section bla

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma finite_generator_range {k : ℕ} (G : microid_generator_space V k) :
(set.range G.val).finite :=
begin
  rw [set_range_eq_finset_range G.val],
  apply finset.finite_to_set,
end

def polytope_of_microid_generator {k : ℕ} (G : microid_generator_space V k) :
polytope V :=
begin
  refine ⟨convex_hull ℝ (set.range G.val), _⟩,
  simp only [is_polytope],
  refine ⟨set.range G.val, _, _, rfl⟩,
  {
    simp only [←set.image_univ],
    refine set.finite.of_finset (finset.image G.val finset.univ) _,
    simp only [←finset.mem_coe, finset.coe_image, finset.coe_univ],
    tauto,
  },
  {
    exact ⟨G.val 0, set.mem_range_self 0⟩,
  },
end

def body_of_microid_generator {k : ℕ} (G : microid_generator_space V k) :
convex_body V :=
begin
  refine ⟨convex_hull ℝ (set.range G.val), _, _, _⟩,
  {
    apply convex_convex_hull,
  },
  {
    refine metric.compact_iff_closed_bounded.mpr ⟨_, _⟩,
    {
      apply set.finite.is_closed_convex_hull,
      apply finite_generator_range,
    },
    {
      apply bounded_convex_hull.mpr,
      refine (metric.bounded_iff_is_bounded _).mpr (set.finite.is_bounded _),
      apply finite_generator_range,
    },
  },
  {
    refine ⟨G.val 0, _⟩,
    refine (subset_convex_hull ℝ _) _,
    refine ⟨0, rfl⟩,
  },
end

lemma body_of_poly_of_gen_eq {k : ℕ}
{G : microid_generator_space V k} :
convex_body_of_polytope (polytope_of_microid_generator G) =
body_of_microid_generator G :=
begin
  simp only [convex_body_of_polytope, polytope_of_microid_generator,
  body_of_microid_generator],
  refl,
end

noncomputable def support_eval {k : ℕ} (u : V) :
microid_generator_space V k → ℝ :=
λ G, (body_of_microid_generator G).supp u

lemma supp_microid_eq_integral {k : ℕ} (μ : microid_measure V k) :
(microid_of_measure μ).supp = (λ u, ∫ G, (body_of_microid_generator G).supp u ∂μ.val) := sorry

/- lemma supp_microid_eq_integral' {k : ℕ} (μ : microid_measure V k) :
(microid_of_measure μ).supp = (λ u, ∫ G in msupport μ, (body_of_microid_generator G).supp u ∂μ.val) := sorry -/

lemma msupport_microid_eq_closure {k : ℕ}
(μ : microid_measure V k)
{C : multiset (convex_body V)}
(hC : dim V = C.card + 2) :
msupport (bm.area (microid_of_measure μ ::ₘ C)) =
closure (⋃ L ∈ msupport μ, msupport (bm.area (body_of_microid_generator L ::ₘ C))) := sorry

-- only used for c > 0
def cuspy_cone (x : V) (u : V) (c : ℝ) :=
{ y : V | ⟪x - y, u⟫_ℝ ≥ c * ∥ y - x ∥ }

def is_cuspy (A : set V) (u : V) (c : ℝ) :=
∃ x ∈ A, A ⊆ cuspy_cone x u c

/- lemma cuspy_iff_TS_zero (K : convex_body V) (u : V) :
TS K.val = 0 ↔ ∃ c > 0, is_cuspy K.val u c := sorry

lemma cuspy_generators_of_cuspy {k : ℕ} {μ : microid_measure V k.succ} {u : V} {c > 0}
(h : is_cuspy (microid_of_measure μ).val u c) :
∀ G ∈ msupport μ, is_cuspy (polytope_of_microid_generator G).val u c := sorry -/

def is_default_polytope {k : ℕ} (μ : microid_measure V k) (u : metric.sphere (0 : V) 1)
(P : microid_generator_space V k) :=
0 ∈ (polytope_of_microid_generator P).val ∧
vector_span ℝ (polytope_of_microid_generator P).val ≤ vector_orth u.val ∧
TS (polytope_of_microid_generator P).val u ≠ 0 ∧
(∀ C : multiset (convex_body V),
dim V = C.card + 2 →
u ∈ msupport (bm.area ((convex_body_of_polytope (polytope_of_microid_generator P)) ::ₘ C)) →
u ∈ msupport (bm.area (microid_of_measure μ ::ₘ C)))

/- lemma finset_sum_pi_eq {α β: Type} {s : finset α}
(f : α → β → V) :
s.sum f = λ b : β, s.sum (λ a : α, f a b) :=
begin
  funext,
  exact finset.sum_apply _ _ _,
end -/

lemma finset_sum_fn_add {α : Type} {s : finset α} (f : α → V) (g : α → V):
s.sum f + s.sum g = s.sum (f + g) :=
begin
  simp only [finset.sum, multiset.sum_map_add.symm],
  refl,
end

lemma finset_sum_fn_sub {α : Type} {s : finset α} (f : α → V) (g : α → V):
s.sum f - s.sum g = s.sum (f - g) :=
begin
  simp only [finset.sum, multiset.sum_map_sub.symm],
  refl,
end

/- lemma real_convex_combination_le {α : Type} {s : finset α}
{w : α → ℝ} {f : α → ℝ} {g : α → ℝ}
(hw₀ : ∀ x : α, x ∈ s → w x ≥ 0)
(hle : f ≤ g) :
s.sum (λ x, w x * f x) ≤ s.sum (λ x, w x * g x) :=
begin
  admit,
end -/

lemma dist_convex_combination_le {k : ℕ}
(G H : microid_generator_space V k)
{s : finset (fin k.succ)}
{w : fin k.succ → ℝ}
(hw₀ : ∀ x : fin k.succ, x ∈ s → w x ≥ 0)
(hw₁ : s.sum w = 1)
: dist (s.affine_combination G.val w) (s.affine_combination H.val w) ≤
dist G H :=
begin
  simp only [dist_eq_norm, finset.affine_combination, finset.weighted_vsub_of_point_apply, vsub_eq_sub, vadd_eq_add,
  affine_map.coe_mk, add_sub_add_right_eq_sub],
  simp only [finset_sum_fn_sub _ _, pi.sub_def, (smul_sub _ _ _).symm],
  refine le_trans (norm_sum_le _ _) _,
  simp only [norm_smul, real.norm_eq_abs],
  simp only [sub_sub_sub_cancel_right],
  simp only [(pi.sub_apply G.val H.val _).symm],
  have : ∀ x : fin k.succ, x ∈ s → |w x| * ∥(G.val - H.val) x∥ ≤ w x * ∥G.val - H.val∥,
  {
    intros x hx,
    simp only [abs_of_nonneg (hw₀ x hx)],
    refine mul_le_mul_of_nonneg_left _ _,
    {exact norm_le_pi_norm (G.val - H.val) x},
    {exact hw₀ x hx},
  },
  refine le_trans (finset.sum_le_sum this) _,
  rw [←finset.sum_mul],
  simp only [hw₁, one_mul],
  change ∥G.val - H.val∥ ≤ dist G.val H.val,
  simp only [dist_eq_norm],
end

lemma body_of_gen_lipschitz {k : ℕ} :
lipschitz_with 1 (body_of_microid_generator : microid_generator_space V k → convex_body V) :=
begin
  rintro x y,
  simp only [ennreal.coe_one, one_mul],
  simp only [edist_dist, body_of_microid_generator, dist_body_eq_Hausdorff_edist],
  -- apply ennreal.of_real_le_of_real,
  have : dist x y = dist x.val y.val := rfl,
  apply emetric.Hausdorff_edist_le_of_mem_edist,
  {
    intros v hv,
    simp only [convex_hull_range_eq_exists_affine_combination _,
      set.mem_set_of] at hv ⊢,
    rcases hv with ⟨s, w, hw₀, hw₁, rfl⟩,
    refine ⟨s.affine_combination y.val w, _, _⟩,
    {
      exact ⟨s, w, hw₀, hw₁, rfl⟩,
    },
    {
      rw [edist_dist],
      apply ennreal.of_real_le_of_real,
      refine dist_convex_combination_le _ _ hw₀ hw₁,
    },
  },
  {
    intros v hv,
    simp only [convex_hull_range_eq_exists_affine_combination _,
      set.mem_set_of] at hv ⊢,
    rcases hv with ⟨s, w, hw₀, hw₁, rfl⟩,
    refine ⟨s.affine_combination x.val w, _, _⟩,
    {
      exact ⟨s, w, hw₀, hw₁, rfl⟩,
    },
    {
      rw [edist_dist],
      apply ennreal.of_real_le_of_real,
      rw [dist_comm],
      refine dist_convex_combination_le _ _ hw₀ hw₁,
    },
  },
end

lemma body_of_gen_continuous_at {k : ℕ} (G : microid_generator_space V k) :
continuous_at (body_of_microid_generator : microid_generator_space V k → convex_body V) G :=
begin
  apply continuous_at_of_locally_lipschitz zero_lt_one 1,
  rintro H -,
  have := body_of_gen_lipschitz H G,
  simpa only [edist_dist, ennreal.coe_one, one_mul,
    ennreal.of_real_le_of_real_iff dist_nonneg] using this,
end

-- uses pruning lemma
/- lemma exists_default_polytope_of_TS_nonzero {k : ℕ} {μ : microid_measure V k}
(h : TS (microid_of_measure μ).val ≠ 0) (u : metric.sphere (0 : V) 1) :
∃ P : microid_generator_space V k, is_default_polytope μ u P := sorry
 -/

noncomputable def project_generator {k : ℕ} (E : submodule ℝ V)
(G : microid_generator_space V k) :
microid_generator_space E k :=
begin
  refine ⟨(proj E) ∘ G.val, _⟩,
  simp only [subtype.val_eq_coe, mem_closed_ball_zero_iff],
  simp only [pi_norm_le_iff zero_le_one, function.comp_app],
  intro l,
  simp only [proj],
  simp only [continuous_linear_map.to_linear_map_eq_coe,
    continuous_linear_map.coe_coe, submodule.coe_norm],
  refine le_trans (continuous_linear_map.le_op_norm (orthogonal_projection E) _) _,
  refine le_trans (mul_le_mul (orthogonal_projection_norm_le E) (norm_le_pi_norm _ _) (norm_nonneg _) zero_le_one) _,
  simpa only [one_mul, mem_closed_ball_iff_norm, sub_zero] using G.property,
end

lemma microid_eval_continuous {k : ℕ} {i : fin k.succ} :
continuous (λ G : microid_generator_space V k, G.val i) :=
begin
  apply lipschitz_with.continuous, rotate, exact 1,
  intros G H,
  simp only [subtype.val_eq_coe, edist_eq_coe_nnnorm_sub],
  rw [subtype.edist_eq, edist_eq_coe_nnnorm_sub],
  simp only [ennreal.coe_one, one_mul, ennreal.coe_le_coe,
    ←pi.sub_apply],
  apply nnnorm_le_pi_nnnorm,
end

lemma project_generator_continuous {k : ℕ} {E : submodule ℝ V} :
continuous
(project_generator E : microid_generator_space V k →
microid_generator_space E k) :=
begin
  have : project_generator E = λ G, project_generator E G := rfl,
  rw [this],
  simp only [project_generator],
  refine continuous_subtype_mk _ _,
  refine continuous_pi (λ i, (map_continuous _).comp _),
  exact microid_eval_continuous,
end

lemma project_generator_measurable {k : ℕ} {E : submodule ℝ V} :
measurable
(project_generator E : microid_generator_space V k →
microid_generator_space E k) :=
begin
  exact project_generator_continuous.measurable,
end

-- MOVETO ???
lemma subset_cthickening_of_Hausdorff_edist_le
{A B : set V} {r : ℝ}
(h : emetric.Hausdorff_edist A B ≤ ennreal.of_real r) :
A ⊆ metric.cthickening r B :=
begin
  intros a ha,
  simp only [metric.mem_cthickening_iff],
  refine le_trans _ h,
  apply emetric.inf_edist_le_Hausdorff_edist_of_mem,
  exact ha,
end

lemma subset_cthickening_Hausdorff_dist
{A B : set V}
(h : emetric.Hausdorff_edist A B ≠ ⊤) :
A ⊆ metric.cthickening (metric.Hausdorff_dist A B) B :=
begin
  apply subset_cthickening_of_Hausdorff_edist_le,
  simp only [metric.Hausdorff_dist,
    ennreal.of_real_to_real h],
  exact le_refl _,
end

lemma body_supp_eval_continuous {u : V} :
continuous (λ K : convex_body V, K.supp u) :=
begin
  apply lipschitz_with.continuous, rotate, exact ∥u∥₊,
  intros K L,
  simp only [edist_body_eq_Hausdorff_edist, ennreal.coe_one, one_mul],
  simp only [edist_dist, dist_eq_norm, real.norm_eq_abs],
  rw [Hausdorff_edist_dist edist_body_ne_top],
  rw [←nnnorm_norm, real.ennnorm_eq_of_real (norm_nonneg _),
    ←ennreal.of_real_mul (norm_nonneg _)],
  apply ennreal.of_real_le_of_real,
  rcases K.supp_exists_mem_face u
    with ⟨k, kf, hk⟩,
  rcases L.supp_exists_mem_face u
    with ⟨l, lf, hl⟩,
  rw [←hk, ←hl],
  rw [abs_sub_le_iff], split,
  {
    have : metric.inf_dist k L.val ≤ metric.Hausdorff_dist K.val L.val,
    {
      apply metric.inf_dist_le_Hausdorff_dist_of_mem,
      {
        exact normal_face_subset kf,
      },
      {
        exact edist_body_ne_top,
      },
    },
    refine le_trans _ (mul_le_mul_of_nonneg_left this (norm_nonneg _)),
    rcases is_closed.exists_inf_dist_eq_dist
      L.is_closed
      L.nonempty
      k
      with ⟨l', l'L, hl'⟩,
    rw [hl'],
    rw [mem_normal_face] at lf,
    refine le_trans (sub_le_sub_left (lf.2 _ l'L) _) _,
    rw [←inner_sub_left],
    refine le_trans (real_inner_le_norm _ _) _,
    nth_rewrite 0 [mul_comm],
    rw [dist_eq_norm],
  },
  { -- it might have been nicer to use the wlog tactic
    have : metric.inf_dist l K.val ≤ metric.Hausdorff_dist K.val L.val,
    {
      rw [metric.Hausdorff_dist_comm],
      apply metric.inf_dist_le_Hausdorff_dist_of_mem,
      {
        exact normal_face_subset lf,
      },
      {
        exact edist_body_ne_top,
      },
    },
    refine le_trans _ (mul_le_mul_of_nonneg_left this (norm_nonneg _)),
    rcases is_closed.exists_inf_dist_eq_dist
      K.is_closed
      K.nonempty
      l
      with ⟨k', k'K, hk'⟩,
    rw [hk'],
    rw [mem_normal_face] at kf,
    refine le_trans (sub_le_sub_left (kf.2 _ k'K) _) _,
    rw [←inner_sub_left],
    refine le_trans (real_inner_le_norm _ _) _,
    nth_rewrite 0 [mul_comm],
    rw [dist_eq_norm],
  },
  apply_instance,
end

lemma supp_eval_continuous {k : ℕ} {u : V} :
continuous (support_eval u : microid_generator_space V k → ℝ) :=
begin
  convert continuous.comp
    body_supp_eval_continuous
    body_of_gen_lipschitz.continuous,
end

lemma supp_eval_strongly_measurable {k : ℕ} {u : V} :
measure_theory.strongly_measurable (support_eval u : microid_generator_space V k → ℝ) :=
begin
  exact supp_eval_continuous.strongly_measurable,
end

noncomputable def project_microid_measure {k : ℕ} (E : submodule ℝ V) (μ : microid_measure V k) :
microid_measure E k := finite_measure_map (project_generator E) μ

lemma microid_generator.proj_body {k : ℕ} (E : submodule ℝ V)
(G : microid_generator_space V k) :
proj_body E (body_of_microid_generator G) =
body_of_microid_generator (project_generator E G) :=
begin
  simp only [proj_body, project_generator, body_of_microid_generator],
  simp only [←(proj E).coe_to_affine_map, affine_map.image_convex_hull,
    set.range_comp],
end

lemma proj_microid_of_measure {k : ℕ}
(E : submodule ℝ V)
(μ : microid_measure V k) :
proj_body E (microid_of_measure μ) = microid_of_measure (project_microid_measure E μ) :=
begin
  apply convex_body.supp_injective,
  funext,
  simp only [convex_body.proj_supp, supp_microid_eq_integral],
  simp only [project_microid_measure, finite_measure_map, measure_theory.finite_measure.val_eq_to_measure],
  rw [measure_theory.integral_map],
  {
    simp only [←microid_generator.proj_body, convex_body.proj_supp],
  },
  {
    exact project_generator_measurable.ae_measurable,
  },
  {
    exact supp_eval_strongly_measurable.ae_strongly_measurable,
  },
end

lemma microid_proj_eq_proj_microid {k : ℕ}
(μ : microid_measure V k)
(E : submodule ℝ V) :
microid_of_measure (project_microid_measure E μ) = proj_body E (microid_of_measure μ) :=
begin
  symmetry,
  apply proj_microid_of_measure,
end

noncomputable def dirac_microid_measure {k : ℕ}
(P : microid_generator_space V k) : microid_measure V k :=
begin
  refine ⟨measure_theory.measure.dirac P, ⟨_⟩⟩, -- trivial
  simp only [measure_theory.is_probability_measure.measure_univ, ennreal.one_lt_top],
end

lemma microid_of_dirac_eq {k : ℕ}
(P : microid_generator_space V k) :
microid_of_measure (dirac_microid_measure P) = body_of_microid_generator P :=
begin
  apply convex_body.supp_injective,
  funext,
  simp only [supp_microid_eq_integral, dirac_microid_measure],
  simp only [measure_theory.integral_dirac],
end


end bla
