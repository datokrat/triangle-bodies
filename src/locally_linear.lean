import convex_body microid

open_locale topological_space

variables {V : Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]

def supp_locally_linear_with (U : set V) (K : convex_body V)
(x : V) :=
∀ v ∈ U, K.supp v = ⟪x, v⟫_ℝ

def supp_locally_linear (U : set V)
(K : convex_body V) :=
∃ x : V, supp_locally_linear_with U K x

def finsupp_sum {α : Type} (f : α →₀ ℝ) : ℝ :=
f.support.sum f.to_fun

noncomputable def finsupp_weighted_sum {α : Type} (w : α →₀ ℝ) (f : α → V) : V :=
w.support.sum (λ a, w a • f a)

structure supp_locally_linear'' (u : V) (ε : ℝ) (K : convex_body V) : Prop :=
/- (map_add : ∀ x y z, x ∈ U → y ∈ U → z ∈ U → x + y - z ∈ U → K.supp (x + y - z) = K.supp x + K.supp y - K.supp z)
(map_smul : ∀ (c : ℝ) x, x ∈ U → c • x ∈ U → K.supp (c • x) = c • K.supp x) -/
--(map_ll : ∀ (c : ℝ) x y z, x ∈ U → y ∈ U → z ∈ U → x + c • (y - z) ∈ U → K.supp (x + c • (y - z)) = K.supp x + c • (K.supp y - K.supp z))
(map_smul : ∀ (c δ : ℝ) x, δ • x + u ∈ metric.ball u ε → δ • (c • x) + u ∈ metric.ball u ε → K.supp (δ • (c • x) + u) - K.supp u = c * (K.supp (δ • x + u) - K.supp u))
(map_add : ∀ (δ : ℝ) x y, δ • x + u ∈ metric.ball u ε → δ • y + u ∈ metric.ball u ε → δ • (x + y) + u ∈ metric.ball u ε → K.supp (δ • (x + y) + u) - K.supp u = (K.supp (δ • x + u) - K.supp u) + (K.supp (δ • y + u) - K.supp u))
(map_hom : ∀ (δ : ℝ), δ • u ∈ metric.ball u ε → K.supp (δ • u) = δ • K.supp u)

structure supp_locally_linear' {ι : Type} (basis : basis ι ℝ V) (u : V) (ε : ℝ) (K : convex_body V) : Prop :=
--(ι : Type)
--(basis : basis ι ℝ V)
--(basis_mem : ∀ k : ι, basis k ∈ metric.ball u ε)
(linear : ∀ v : V, v ∈ metric.ball u ε →
K.supp v = (basis.repr v).sum (λ i ci, ci * K.supp (basis i)))

noncomputable def transform_into_ball (u : V) (ε : ℝ)
(v : V) : V :=
(ε / (2 * ∥v∥)) • v + u

lemma transform_into_ball_mem_ball (u : V) {ε : ℝ} (εpos : ε > 0)
(v : V) : transform_into_ball u ε v ∈ metric.ball u ε :=
begin
  simp only [transform_into_ball, metric.mem_ball, dist_eq_norm],
  simp only [add_sub_cancel, norm_smul, norm_div, norm_mul],
  simp only [real.norm_eq_abs, abs_eq_self.mpr (le_of_lt εpos)],
  simp only [abs_two, abs_norm_eq_norm],
  ring_nf,
  simp only [mul_inv],
  conv {
    to_rhs,
    rw [←one_mul ε],
  },
  rw [mul_lt_mul_right εpos, mul_comm, mul_assoc],
  by_cases h : ∥v∥ = 0,
  {
    simp only [h],
    simp only [mul_zero, zero_lt_one],
  },
  {
    rw [inv_mul_cancel h],
    ring_nf,
    exact half_lt_self (zero_lt_one),
  },
end

noncomputable def ll_extension (u : V) (ε : ℝ)
(f : V → ℝ) : V → ℝ :=
λ v, ((2 * ∥v∥) / ε) * (f (transform_into_ball u ε v) - f u)

lemma supp_locally_linear_iff {ι : Type} {b : basis ι ℝ V}
{u : V} {ε : ℝ} (εpos : ε > 0)
(hb : ∀ k : ι, b k ∈ metric.ball u ε)
(K : convex_body V) :
supp_locally_linear (metric.ball u ε) K ↔
supp_locally_linear' b u ε K :=
begin
  split,
  {
    rintro ⟨x, h⟩,
    refine ⟨_⟩,
    {
      intros v hv,
      rw [h v hv],
      simp only [h (b _) (hb _)],
      --simp only [←real_inner_smul_right],
      simp only [←smul_eq_mul],
      simp only [←finsupp.inner_sum],
      rw [←finsupp.total_apply],
      rw [basis.total_repr],
    },
  },
  {
    rintro ⟨hlin⟩,
    let f' : (ι →₀ ℝ) → ℝ := λ f, f.sum (λ i ci, ci * K.supp (b i)),
    let f := f' ∘ b.repr,
    have flin : is_linear_map ℝ f,
    {
      refine ⟨_, _⟩,
      {
        intros x y,
        simp only [f, f', function.comp_app],
        rw [map_add, finsupp.sum_add_index'],
        {
          simp only [zero_mul, eq_self_iff_true, implies_true_iff],
        },
        {
          simp only [add_mul, eq_self_iff_true, forall_forall_const, implies_true_iff],
        },
      },
      {
        intros d x,
        simp only [f, f', function.comp_app],
        rw [map_smul, finsupp.sum_smul_index', finsupp.smul_sum],
        {simp only [smul_mul_assoc]},
        {
          intro i,
          simp only [zero_mul],
        },
      },
    },
    have feq: ∀ v : V, v ∈ metric.ball u ε → f v = K.supp v,
    {
      intros v hv,
      symmetry,
      apply hlin,
      exact hv,
    },
    obtain ⟨hadd, hsmul⟩ := flin,
    let x := of_dual' ⟨_, hadd, hsmul⟩,
    refine ⟨x, _⟩,
    intros v hv,
    rw [←feq v hv],
    simp only [x, of_dual'],
    rw [inner_product_space.to_dual_symm_apply],
    refl,
  }
end

/-lemma inner_transform_into_ball (u : V) {ε : ℝ} (εpos : ε > 0)
(v w : V) :
(2 * ∥w∥ / ε) * (⟪v, (transform_into_ball u ε w)⟫_ℝ - ⟪v, u⟫_ℝ) =
⟪v, w⟫_ℝ := sorry

lemma ll_extension_eq_inner  {u : V} {ε : ℝ} (εpos : ε > 0)
{K : convex_body V} {x : V}
(h : supp_locally_linear_with (metric.ball u ε) K x) :
ll_extension u εpos K.supp = (λ v, ⟪x, v⟫_ℝ) :=
begin
  funext v,
  simp only [ll_extension],
  rw [h _ (transform_into_ball_mem_ball u εpos _)],
  rw [h u (metric.mem_ball_self εpos)],
  rw [inner_transform_into_ball u εpos],
end -/

/- lemma supp_locally_linear_iff_ll_extension_linear {u : V} {ε : ℝ} (εpos : ε > 0)
(K : convex_body V) :
supp_locally_linear (metric.ball u ε) K ↔ is_linear_map ℝ (ll_extension u εpos K.supp) :=
begin
  split,
  {
    rintro ⟨x, hx⟩,
    refine ⟨_, _⟩,
    all_goals {
      intros x y,
      simp only [ll_extension],
      repeat {rw [hx _ (transform_into_ball_mem_ball u εpos _)]},
      repeat {rw [hx u (metric.mem_ball_self εpos)]},
      repeat {rw [inner_transform_into_ball u εpos]},
      simp only [inner_add_right, inner_smul_right, smul_eq_mul],
    },
  },
  {
    rintro ⟨hadd, hsmul⟩,
    let f : V →ₗ[ℝ] ℝ := ⟨_, hadd, hsmul⟩,
    let x := of_dual' f,
  },
end -/

lemma supp_integrable {k : ℕ} (u : V)
{μ : measure_theory.finite_measure (microid_generator_space V k)} :
measure_theory.integrable (λ G, (body_of_microid_generator G).supp u) μ.val :=
begin
  let M := support_eval u '' (set.univ : set (microid_generator_space V k)),
  have gcp : is_compact (set.univ : set (microid_generator_space V k)) := compact_space.compact_univ,
  have Mcp : is_compact M := gcp.image supp_eval_continuous,
  have Mbdd := Mcp.bounded,
  rw [bounded_iff_forall_norm_le] at Mbdd,
  obtain ⟨C, hC⟩ := Mbdd,
  refine ⟨_, _⟩,
  {
    exact supp_eval_strongly_measurable.ae_strongly_measurable,
  },
  {
    apply measure_theory.has_finite_integral_of_bounded,
    rotate,
    {exact C},
    {
      apply filter.eventually_of_forall,
      intro G,
      apply hC,
      exact set.mem_image_of_mem _ (set.mem_univ _),
    },
  },
end

lemma exists_basis_in_ball {ε : ℝ} (u : V) (εpos : ε > 0) :
∃ (ι : Type) (b : basis ι ℝ V), ∀ k : ι, b k ∈ metric.ball u ε :=
begin
  have := linear_independent_empty ℝ V,
  let s := this.extend (set.empty_subset (metric.ball u ε)),
  have sli := this.linear_independent_extend (set.empty_subset (metric.ball u ε)),
  have sball : s ⊆ metric.ball u ε := this.extend_subset _,
  let b : basis s ℝ V := basis.mk _ _, rotate,
  {
    intro x, exact x,
  },
  {
    exact sli,
  },
  {
    rw [←ball_spans_submodule ⊤ u submodule.mem_top εpos],
    rw [submodule.span_le],
    simp only [subtype.range_coe_subtype, set.set_of_mem_eq],
    simp only [submodule.top_coe, set.inter_univ],
    exact this.subset_span_extend _,
  },
  refine ⟨_, b, _⟩,
  intro k,
  rw [basis.mk_apply],
  exact sball k.property,
end

lemma microid_supp_locally_linear_of_generators {k : ℕ} {ε : ℝ} {u : V}
(εpos : ε > 0)
(μ : microid_measure V k)
(h : ∀ G ∈ msupport μ,
supp_locally_linear (metric.ball u ε) (body_of_microid_generator G)) :
supp_locally_linear (metric.ball u ε) (microid_of_measure μ) :=
begin
  obtain ⟨ι, b, hb⟩ := exists_basis_in_ball u εpos,
  simp only [supp_locally_linear_iff εpos hb] at h ⊢,
  refine ⟨_⟩,
  {
    intros v hv,
    simp only [supp_microid_eq_integral],
    simp only [finsupp.sum],
    simp only [←measure_theory.integral_mul_left],
    rw [←measure_theory.integral_finset_sum],
    refine integral_eq_of_eq_on_msupport _ _ _,
    any_goals {apply measure_theory.integrable_finset_sum},
    any_goals {intros G hG},
    any_goals {apply measure_theory.integrable.const_mul},
    any_goals {apply supp_integrable},
    {
      obtain ⟨hlin'⟩ := h G hG,
      exact hlin' v hv,
    },
  },
end

lemma normal_face_singleton_iff_locally_linear_with
{U : set V} (oU : is_open U)
{K : convex_body V}
{x : V} :
supp_locally_linear_with U K x ↔  
∀ u ∈ U, (K.normal_face u).val = {x} :=
begin
  rw [metric.is_open_iff] at oU,
  split,
  {
    intros h u hu,
    obtain ⟨ε, εpos, εball⟩ := oU u hu,
    have ss : (K.normal_face u).val ⊆ {x},
    {
      intros z hz,
      simp only [set.mem_singleton_iff],
      rw [←sub_eq_zero, ←real_inner_self_nonpos],
      rw [inner_sub_right, sub_nonpos],
      simp only [convex_body.normal_face, K.normal_face_supp u, set.mem_set_of] at hz,
      suffices hs : ∃ δ : ℝ, δ > 0 ∧ ⟪u + δ • (z - x), z⟫_ℝ ≤ ⟪u + δ • (z - x), x⟫_ℝ,
      {
        rcases hs with ⟨δ, δpos, hs⟩,
        simp only [inner_add_left, real_inner_smul_left] at hs,
        rw [real_inner_comm z u, real_inner_comm x u] at hs,
        simp only [hz, h u hu] at hs,
        simpa only [add_le_add_iff_left, mul_le_mul_left δpos] using hs,
      },
      by_cases hc : z - x = 0,
      {
        refine ⟨1, zero_lt_one, _⟩,
        rw [hc, smul_zero, add_zero],
        rw [real_inner_comm x u, real_inner_comm z u, ←h u hu],
        rw [hz.2],
      },
      {
        refine ⟨ε / (2 * ∥z - x∥), _, _⟩,
        {
          refine div_pos εpos _,
          simp only [zero_lt_mul_left, zero_lt_bit0, zero_lt_one, norm_pos_iff, ne.def, hc, not_false_iff],
        },
        {
          have : u + (ε / (2 * ∥z - x∥)) • (z - x) ∈ U,
          {
            apply εball,
            simp only [metric.mem_ball, dist_self_add_left],
            simp only [norm_smul, norm_div, norm_mul],
            simp only [real.norm_eq_abs, abs_eq_self.mpr (le_of_lt εpos)],
            simp only [abs_two, abs_norm_eq_norm],
            ring_nf,
            simp only [mul_inv],
            conv {
              to_rhs,
              rw [←one_mul ε],
            },
            rw [mul_lt_mul_right εpos, mul_comm, mul_assoc],
            change z - x ≠ 0 at hc,
            rw [←norm_ne_zero_iff] at hc,
            rw [inv_mul_cancel hc],
            ring_nf,
            exact half_lt_self (zero_lt_one),
          },
          have heq := h _ this,
          rw [real_inner_comm] at heq,
          rw [←heq],
          refine le_trans _ (K.inner_le_supp hz.1),
          exact le_of_eq (real_inner_comm _ _),
        },
      },
    },
    apply subset_antisymm,
    {
      exact ss,
    },
    {
      obtain ⟨y, hy⟩ := K.normal_face_nonempty u,
      have := ss hy,
      rw [set.mem_singleton_iff] at this,
      rw [set.singleton_subset_iff, ←this],
      exact hy,
    },
  },
  {
    intros h u hu,
    replace h := h u hu,
    have := set.mem_singleton x,
    simp only [←h, convex_body.normal_face, K.normal_face_supp] at this,
    exact this.2.symm,
  },
end

lemma normal_face_singleton_iff_locally_linear
{U : set V} (oU : is_open U)
{K : convex_body V} :
supp_locally_linear U K ↔  
∃ x : V, ∀ u ∈ U, (K.normal_face u).val = {x} :=
begin
  apply exists_congr,
  intro x,
  exact normal_face_singleton_iff_locally_linear_with oU,
end