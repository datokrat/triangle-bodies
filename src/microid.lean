import convex convex_body multiset brunn_minkowski finset
  linear_algebra.affine_space.affine_subspace
  topology.continuous_function.bounded
  measure_theory.measure.measure_space
  analysis.convex.basic
  data.multiset.basic
  measure_theory.measure.measure_space
  topology.basic
  analysis.inner_product_space.pi_L2

open_locale pointwise

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

open_locale pointwise

section types

variables (V : Type)
[inner_product_space ℝ V] [finite_dimensional ℝ V]

def polytope :=
{ P : set V // is_polytope P }

def convex_body_of_polytope (P : polytope V) : convex_body V :=
sorry

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

section bla

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma finite_generator_range {k : ℕ} (G : microid_generator_space V k) :
(set.range G.val).finite :=
begin
  rw [set_range_eq_finset_range G.val],
  apply finset.finite_to_set,
end

-- bad edge case: k = 0
def polytope_of_microid_generator {k : ℕ} (G : microid_generator_space V k) :
polytope V :=
begin
  refine ⟨convex_hull ℝ (set.range G.val), sorry⟩,
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

def microid_of_measure {k : ℕ} (μ : microid_measure V k) :
convex_body V := sorry


-- only used for c > 0
def cuspy_cone (x : V) (u : V) (c : ℝ) :=
{ y : V | ⟪x - y, u⟫_ℝ ≥ c * ∥ y - x ∥ }

def is_cuspy (A : set V) (u : V) (c : ℝ) :=
∃ x ∈ A, A ⊆ cuspy_cone x u c

lemma cuspy_iff_TS_zero (K : convex_body V) (u : V) :
TS K.val = 0 ↔ ∃ c > 0, is_cuspy K.val u c := sorry

lemma cuspy_generators_of_cuspy {k : ℕ} {μ : microid_measure V k.succ} {u : V} {c > 0}
(h : is_cuspy (microid_of_measure μ).val u c) :
∀ G ∈ msupport μ, is_cuspy (polytope_of_microid_generator G).val u c := sorry

def polytope_to_convex_body
(P : polytope V) : convex_body V :=
⟨P.val, sorry⟩

def is_default_polytope {k : ℕ} (μ : microid_measure V k.succ) (u : metric.sphere (0 : V) 1)
(P : microid_generator_space V k.succ) :=
vector_span ℝ (polytope_of_microid_generator P).val ≤ vector_orth u.val ∧
TS (polytope_of_microid_generator P).val u ≠ 0 ∧
(∀ C : multiset (convex_body V),
C.card = dim V - 2 →
u ∈ msupport (bm.area ((polytope_to_convex_body (polytope_of_microid_generator P)) ::ₘ C)) →
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

lemma real_convex_combination_le {α : Type} {s : finset α}
{w : α → ℝ} {f : α → ℝ} {g : α → ℝ}
(hw₀ : ∀ x : α, x ∈ s → w x ≥ 0)
(hle : f ≤ g) :
s.sum (λ x, w x * f x) ≤ s.sum (λ x, w x * g x) :=
begin
  admit,
end

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
lemma exists_default_polytope_of_TS_nonzero {k : ℕ} {μ : microid_measure V k.succ}
(h : TS (microid_of_measure μ).val ≠ 0) (u : metric.sphere (0 : V) 1) :
∃ P : microid_generator_space V k.succ, is_default_polytope μ u P := sorry

end bla