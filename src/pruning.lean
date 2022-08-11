import convex convex_body multiset brunn_minkowski microid
  init.data.fin.ops

open_locale pointwise
open_locale topological_space
open_locale nat

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

section defs

variables (V : Type) [inner_product_space ℝ V] [finite_dimensional ℝ V]

def prune_triple (k : ℕ) :=
microid_generator_space V k × fin k.succ × fin k.succ

end defs

section blob

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def prune_triple_generator {k : ℕ}
(t : prune_triple V k) : microid_generator_space V k := t.1

def prune_gen_fn {k : ℕ}
(t : prune_triple V k) : fin k.succ → V := t.1.val

def prune_cusp_index {k : ℕ}
(t : prune_triple V k) : fin k.succ := t.2.1

def prune_cusp {k : ℕ}
(t : prune_triple V k) : V :=
prune_gen_fn t (prune_cusp_index t)

def prune_secondary_index {k : ℕ}
(t : prune_triple V k) : fin k.succ := t.2.2

def prune_secondary {k : ℕ}
(t : prune_triple V k) : V :=
prune_gen_fn t (prune_secondary_index t)

def valid_prune_triple {k : ℕ}
(t : prune_triple V k) (u : metric.sphere (0 : V) 1) : Prop :=
∀ i : fin k, ⟪prune_gen_fn t i, u⟫_ℝ ≤ ⟪prune_cusp t, u⟫_ℝ ∧
prune_cusp t ≠ prune_secondary t

noncomputable def prune_direction {k : ℕ}
(t : prune_triple V k) : V :=
prune_cusp t - prune_secondary t

noncomputable def cuspiness {k : ℕ}
(u : metric.sphere (0 : V) 1) (t : prune_triple V k) : ℝ :=
⟪prune_direction t, u⟫_ℝ / ∥prune_direction t∥


def in_combinatorial_closure
(u : metric.sphere (0 : V) 1)
(S : set (convex_body V))
(K : convex_body V) :=
∀ Ps : multiset (convex_body V), dim V = Ps.card + 1 →
u ∈ msupport (bm.area (K ::ₘ Ps)) →
u ∈ closure (⋃ L ∈ S, msupport (bm.area (L ::ₘ Ps)))

def lfe --locally face equivalent
(U : set (metric.sphere (0 : V) 1))
(P Q : polytope V) :=
∀ u : metric.sphere (0 : V) 1,
u ∈ U → vector_span ℝ (normal_face P.val u) = vector_span ℝ (normal_face Q.val u)

def chop_generator {k : ℕ} {c : ℕ}
(φ : fin c.succ → fin k.succ)
(G : microid_generator_space V k) :
microid_generator_space V c :=
begin
  refine ⟨G.val ∘ φ, _⟩,
  simp only [subtype.val_eq_coe, mem_ball_zero_iff],
  admit,
end

lemma chop_def {k : ℕ} {c : ℕ}
{φ : fin c.succ → fin k.succ} :
(chop_generator φ : microid_generator_space V k → microid_generator_space V c)
= (λ G, chop_generator φ G) := rfl

noncomputable def diam_generator {k : ℕ}
(G : microid_generator_space V k) : ℝ :=
metric.diam (G.val '' set.univ)

lemma generator_range_bounded {k : ℕ}
(G : microid_generator_space V k) :
metric.bounded (set.range G.val) :=
begin
  let C := finset.sup finset.univ (has_nnnorm.nnnorm ∘ G.val),
  refine ⟨C + C, _⟩,
  intros x hx y hy,
  rcases set.mem_range.mp hx with ⟨x, rfl⟩,
  rcases set.mem_range.mp hy with ⟨y, rfl⟩,
  have nx : ∥ G.val x ∥₊ ≤ C := finset.le_sup (finset.mem_univ x),
  have ny : ∥ G.val y ∥₊ ≤ C := finset.le_sup (finset.mem_univ y),
  refine le_trans _ (add_le_add nx ny),
  apply dist_le_norm_add_norm,
end

lemma h_diam_continuous {k : ℕ} {ε : ℝ}
(x y : microid_generator_space V k) (h : dist x y < ε / 4) :
diam_generator x < ε + diam_generator y :=
begin
  have hh : ε / 2 < ε := sorry,
  have hδ' : 0 ≤ ε / 2 := sorry,
  refine lt_of_le_of_lt _ (add_lt_add_right hh (diam_generator y)),
  simp only [diam_generator],
  apply metric.diam_le_of_forall_dist_le,
  {
    rw [←@add_zero ℝ _ 0],
    exact add_le_add hδ' metric.diam_nonneg,
  },
  {
    intros u hu v hv,
    rcases (set.mem_image _ _ _).mp hu with ⟨pu, hpu, rfl⟩,
    rcases (set.mem_image _ _ _).mp hv with ⟨pv, hpv, rfl⟩,
    simp only [dist_eq_norm],
    have : x.val pu - x.val pv = ((x.val-y.val) pu - (x.val-y.val) pv)
      + (y.val pu - y.val pv),
    {
      simp only [pi.sub_apply],
      abel,
    },
    rw [this],
    refine le_trans (norm_add_le _ _) _,
    refine add_le_add _ _,
    {
      refine le_trans (norm_sub_le _ _) _,
      refine le_trans (add_le_add (norm_le_pi_norm _ _) (norm_le_pi_norm _ _)) _,
      -- have : ∀ x : ℝ, x + x = 2 * x := sorry,
      -- have two_gt: 2 > 0 := by positivity,
      -- rw [this],
      rw [←dist_eq_norm],
      have := metric.mem_ball.mp h,
      -- rw [dist_comm] at this,
      change dist x y + dist x y ≤ ε / 2,
      refine le_of_lt (lt_of_lt_of_le (add_lt_add this this) _),
      admit,
    },
    {
      rw[←dist_eq_norm],
      refine metric.dist_le_diam_of_mem _ _ _,
      {
        simp only [set.image_univ],
        apply generator_range_bounded,
      },
      all_goals {
        refine (set.mem_image _ _ _).mp _,
        simp only [set.image_univ, set.mem_range_self],
      },
    },
  },
end

lemma diam_continuous (k : ℕ) :
continuous (diam_generator : microid_generator_space V k → ℝ) :=
begin
  simp only [continuous_def],
  simp only [metric.is_open_iff],
  intros U hU x hxU,
  replace hxU := set.mem_preimage.mp hxU,
  rcases hU _ hxU with ⟨ε, hε, hx⟩,
  let δ := ε / 2,
  have hδ : δ > 0 := half_pos hε,
  have hδ' : δ ≥ 0 := le_of_lt hδ,
  let γ := ε / 4,
  have hγ : γ > 0 := sorry,
  have hγ' : γ ≥ 0 := le_of_lt hγ,
  have hh : δ < ε := sorry,
  refine ⟨γ, hγ, _⟩,
  intros y hy,
  simp only [set.mem_preimage],
  apply hx,
  simp only [metric.mem_ball, real.dist_eq],
  refine abs_lt.mpr ⟨_, _⟩,
  {
    simp only [neg_lt_sub_iff_lt_add],
    replace hy := metric.mem_ball.mp hy,
    rw [dist_comm] at hy,
    refine h_diam_continuous _ _ hy,
  },
  {
    simp only [sub_lt_iff_lt_add],
    replace hy := metric.mem_ball.mp hy,
    refine h_diam_continuous _ _ hy,
  },
end

lemma const_of_diam_zero {k : ℕ}
{G : microid_generator_space V k}
(h : diam_generator G = 0) (m n : fin k.succ) :
G.val m = G.val n :=
begin
  simp only [diam_generator, subtype.val_eq_coe, set.image_univ] at h,
  simp only [subtype.val_eq_coe],
  apply dist_le_zero.mp,
  {
    rw [←h],
    refine metric.dist_le_diam_of_mem _ _ _,
    {apply generator_range_bounded},
    {simp only [subtype.val_eq_coe, set.mem_range_self]},
    {simp only [subtype.val_eq_coe, set.mem_range_self]},
  },
end

noncomputable def norm_generator {k : ℕ}
(G : microid_generator_space V k) : microid_generator_space V k :=
begin
  let f := G.val - function.const _ (G.val 0),
  refine ⟨λ m, (1 / diam_generator G) • (G.val m - G.val 0) , _⟩,
  simp only [set.image_univ, one_div, mem_closed_ball_zero_iff],
  simp only [pi.norm_def, nnnorm_smul],
  have : ∀ b : fin k.succ, ∥G.val b - G.val 0∥ ≤ diam_generator G,
  {
    intro b,
    rw [←dist_eq_norm],
    refine metric.dist_le_diam_of_mem _ _ _,
    {rw [set.image_univ], apply generator_range_bounded},
    all_goals {
      rw [set.image_univ],
      simp only [subtype.val_eq_coe, set.mem_range_self],
    },
  },
  admit,
end

lemma norm_generator_positive_factor₁ {k : ℕ}
(G : microid_generator_space V k) (h : diam_generator G = 0) :
(norm_generator G).val = (1 : ℝ /- some painful seconds -/) • (G.val - function.const _ (G.val 0)) :=
begin
  funext,
  simp only [norm_generator, one_div, pi.sub_apply,
    function.const_apply, one_smul],
  have : G.val m - G.val 0 = 0,
  {
    rw [const_of_diam_zero h _ 0],
    simp only [sub_self],
  },
  simp only [this, smul_zero],
end

lemma norm_generator_positive_factor₂ {k : ℕ}
(G : microid_generator_space V k) (h : diam_generator G ≠ 0) :
(diam_generator G)⁻¹ > 0 ∧ (norm_generator G).val = (diam_generator G)⁻¹ • (G.val - function.const _ (G.val 0)) :=
begin
  replace h : diam_generator G > 0,
  {
    simp only [diam_generator] at h,
    exact ne.lt_of_le' h metric.diam_nonneg,
  },
  refine ⟨_, _⟩,
  {
    exact inv_pos_of_pos h,
  },
  {
    funext,
    simp only [norm_generator, one_div, pi.smul_apply, pi.sub_apply],
  },
end

lemma norm_generator_positive_factor {k : ℕ}
(G : microid_generator_space V k) :
∃ c : ℝ, c > 0 ∧ (norm_generator G).val = c • (G.val - function.const _ (G.val 0)) :=
begin
  by_cases h : diam_generator G = 0,
  {
    refine ⟨1, zero_lt_one, _⟩,
    exact norm_generator_positive_factor₁ G h,
  },
  {
    refine ⟨(diam_generator G)⁻¹, _⟩,
    exact norm_generator_positive_factor₂ G h,
  }
end

lemma dist_times_norm {k : ℕ}
(G : microid_generator_space V k) :
∃ v : V, G.val = (diam_generator G • (norm_generator G).val) + function.const _ v :=
begin
    simp only [norm_generator, one_div, set.image_univ],
    simp only [pi.smul_def, smul_smul],
    by_cases h : diam_generator G = 0,
    {
      rw [h],
      simp only [inv_zero, mul_zero, zero_smul],
      refine ⟨G.val 0, _⟩,
      funext,
      simp only [pi.add_apply, function.const_apply, zero_add],
      refine const_of_diam_zero h _ _,
    },
    {
      rw [mul_inv_cancel h],
      simp only [one_smul],
      refine ⟨G.val 0, _⟩,
      funext,
      simp only [pi.add_apply, sub_add_cancel],
    },
end

noncomputable def prunenorm_generator {k : ℕ} {c : ℕ}
(φ : fin c.succ → fin k.succ)
(G : microid_generator_space V k) : microid_generator_space V c :=
norm_generator (chop_generator φ G)

lemma prunenorm_def {k : ℕ} {c : ℕ}
(φ : fin c.succ → fin k.succ) :
(prunenorm_generator φ : microid_generator_space V k → microid_generator_space V c) =
norm_generator ∘ chop_generator φ := rfl

lemma prunenorm_prunenorm {c₁ c₂ c₃: ℕ}
(φ₁ : fin c₁.succ → fin c₂.succ) (φ₂ : fin c₂.succ → fin c₃.succ)
(G : microid_generator_space V c₃) :
prunenorm_generator φ₁ (prunenorm_generator φ₂ G) =
prunenorm_generator (φ₂ ∘ φ₁) G :=
sorry

lemma diam_norm_generator_eq {k : ℕ}
(G : microid_generator_space V k) :
diam_generator G ≠ 0 → diam_generator (norm_generator G) = 1 :=
begin
  intro h,
  rcases norm_generator_positive_factor₂ G h with ⟨hgt, heq⟩,
end

lemma set_image_smul' {α : Type} {t : set α} {a : ℝ} (f : α → V) :
(a • f) '' t = a • (f '' t) :=
begin
  have : a • f = (λ x, a • x) ∘ f,
  {
    funext,
    simp only [pi.smul_apply],
  },
  rw [this],
  rw [set.image_comp _ f t],
  ext, split,
  all_goals {
    intro hx,
    rcases (set.mem_image _ _ _).mp hx with ⟨px, hpx, rfl⟩,
    refine (set.mem_image _ _ _).mpr ⟨px, hpx, rfl⟩,
  },
end

lemma polytope_of_norm_generator_smul {k : ℕ}
(G : microid_generator_space V k) :
∃ c : ℝ, c > 0 ∧
(polytope_of_microid_generator (norm_generator G)).val =
c • ((polytope_of_microid_generator G).val + {-(G.val 0)}) :=
begin
  rcases norm_generator_positive_factor G with ⟨c, hc₁, hc₂⟩,
  refine ⟨c, hc₁, _⟩,
  simp only [polytope_of_microid_generator, hc₂],
  rw [←set.image_univ],
  rw [set_image_smul', convex_hull_smul],
  congr,
  rw [←@convex_hull_singleton ℝ V _ _ _ (-(G.val 0))],
  rw [←convex_hull_add],
  congr,
  ext, split,
  {
    intro hx,
    rcases (set.mem_image _ _ _).mp hx with ⟨px, hpx, rfl⟩,
    refine ⟨G.val px, -G.val 0, _, _, _⟩,
    {
      simp only [set.mem_range_self],
    },
    {
      simp only [set.mem_singleton],
    },
    {
      simp only [pi.sub_apply, function.const_apply],
      abel,
    },
  },
  {
    rintro ⟨a, b, ha, hb, rfl⟩,
    rcases (set.mem_range).mp ha with ⟨pa, hpa, rfl⟩,
    refine (set.mem_image _ _ _).mpr ⟨pa, _, _⟩,
    {
      simp only [set.mem_univ],
    },
    {
      simp only [set.eq_of_mem_singleton hb, pi.sub_apply,
      function.const_apply],
      abel,
    },
  },
end

lemma h_normal_face_homothety (A : set V) (u : V) (c : ℝ) (v : V)
(h : c > 0) : normal_face (c • (A + {v})) u ⊆ c • (normal_face A u + {v}) :=
begin
  simp only [normal_face],
  intro x,
  {
    intros hx,
    replace hx := set.mem_set_of.mp hx,
    rcases set.mem_smul_set.mp hx.1 with ⟨y, hy, rfl⟩,
    refine set.mem_smul_set.mpr (set.smul_mem_smul_set _),
    apply set.mem_set_of.mpr,
    refine ⟨y - v, v, _, _⟩,
    {
      apply set.mem_set_of.mpr,
      rcases hy with ⟨a, vv, ha, hvv, rfl⟩,
      rcases set.eq_of_mem_singleton hvv,
      split,
      {
        simp only [ha, add_sub_cancel],
      },
      {
        intros y hy,
        replace hx := hx.2,
        have := hx (c • (y + v)) _,
        {
          simp only [inner_smul_left, inner_add_left,
            is_R_or_C.conj_to_real, (smul_eq_mul ℝ).symm] at this,
          replace := (smul_le_smul_iff_of_pos h).mp this,
          simpa only [add_sub_cancel, add_le_add_iff_right] using this,
        },
        {
          refine set.smul_mem_smul_set ⟨y, v, hy, _, rfl⟩,
          exact set.mem_singleton _,
        },
      },
    },
    {
      refine ⟨set.mem_singleton _, by simp only [sub_add_cancel]⟩,
    },
  },
end

lemma normal_face_homothety {A : set V} {u : V} {c : ℝ} (v : V)
(h : c > 0) : normal_face (c • (A + {v})) u = c • (normal_face A u + {v}) :=
begin
  apply subset_antisymm,
  {
    apply h_normal_face_homothety A u c v h,
  },
  {
    let B := c • (A + {v}),
    refine (set.set_smul_subset_iff₀ (ne_of_gt h)).mpr _,
    suffices hh : normal_face A u ⊆ c⁻¹ • (normal_face (c • (A + {v})) u + {-c • v}),
    {
      rintro x ⟨n, vv, hn, hvv, rfl⟩,
      cases set.eq_of_mem_singleton hvv,
      rcases set.mem_smul_set.mp (hh hn) with ⟨a, ha, rfl⟩,
      refine set.mem_smul_set.mpr ⟨a - (-c) • v, _, _⟩,
      {
        rcases ha with ⟨b, d, hb, hd, rfl⟩,
        cases set.eq_of_mem_singleton hd,
        convert hb,
        simp only [add_sub_cancel],
      },
      {
        simp only [neg_smul, sub_neg_eq_add, smul_add, add_right_inj,
          inv_smul_smul₀ (ne_of_gt h)],
      },
    },
    convert h_normal_face_homothety B u c⁻¹ (-c • v) (inv_pos_of_pos h),
    ext, split,
    {
      intro hx,
      refine (set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt (inv_pos_of_pos h)) _ _).mpr _,
      simp only [B, inv_inv, set.add_singleton, neg_smul, set.image_add_right,
        set.mem_preimage, neg_neg],
      refine set.mem_smul_set.mpr _,
      refine ⟨x + v, _, _⟩,
      {
        refine (set.mem_preimage).mpr _,
        convert hx,
        simp only [add_neg_cancel_right],
      },
      {
        rw [smul_add],
      },
    },
    {
      intro hx,
      rcases set.mem_smul_set.mp hx with ⟨y, ⟨b, w, hb, hw, rfl⟩, rfl⟩,
      rcases set.eq_of_mem_singleton hw,
      simp only [B] at hb,
      rcases set.mem_smul_set.mp hb with ⟨d, ⟨e, q, he, hq, rfl⟩, rfl⟩,
      rcases set.eq_of_mem_singleton hq,
      simp only [neg_smul, sub_neg_eq_add, smul_add,
        sub_neg_eq_add],
      simp only [smul_neg, (smul_assoc _ _ _).symm,
        (inv_mul_eq_one₀ (ne_of_gt h)).mpr rfl, smul_eq_mul, one_smul,
        add_neg_cancel_right],
      assumption,
    },
  },
end

lemma h_vector_span_homothety (A : set V) {c : ℝ} (v : V)
(h : c > 0) :
vector_span ℝ A ≥ vector_span ℝ (c • (A + {v})) :=
begin
  refine submodule.span_le.mpr _,
  simp only [vector_span],
  rintro x ⟨a₁, a₂, ha₁, ha₂, rfl⟩,
  rcases set.mem_smul_set.mp ha₁ with ⟨d₁, ⟨e₁, v₁, he₁, hv₁, rfl⟩, rfl⟩,
  rcases set.mem_smul_set.mp ha₂ with ⟨d₂, ⟨e₂, v₂, he₂, hv₂, rfl⟩, rfl⟩,
  rcases set.eq_of_mem_singleton hv₁,
  rcases set.eq_of_mem_singleton hv₂,
  simp only [vsub_eq_sub],
  rw [←smul_sub],
  change c • (e₁ + v - (e₂ + v)) ∈ /- need change to remove ↑ here -/ (submodule.span ℝ (A -ᵥ A)),
  refine submodule.smul_mem _ c _,
  rw [add_sub_add_right_eq_sub],
  apply submodule.subset_span,
  refine ⟨e₁, e₂, he₁, he₂, rfl⟩,
end

lemma vector_span_homothety {A : set V} {c : ℝ} (v : V)
(h : c > 0) :
vector_span ℝ (c • (A + {v})) = vector_span ℝ A :=
begin
  apply le_antisymm,
  {
    exact h_vector_span_homothety A v h,
  },
  {
    -- might become a separate lemma!
    have : A = c⁻¹ • ((c • (A + {v})) + {-c • v}),
    {
      simp only [smul_add, neg_smul, set.smul_set_singleton, smul_neg],
      simp only [inv_smul_smul₀ (ne_of_gt h)],
      rw [add_assoc],
      -- Worked with squeeze_simp, but doesn't work now: simp only [set.singleton_add_singleton, set.singleton_add_singleton, add_right_neg, set.add_singleton, add_zero, set.image_id', eq_self_iff_true],
      simp only [set.singleton_add_singleton, add_right_neg, add_zero],
      simp only [set.add_singleton, add_zero, set.image_id'],
    },
    convert h_vector_span_homothety (c • (A + {v})) (-c • v) (inv_pos_of_pos h),
  },
end

lemma gen_lfe_norm {k : ℕ}
(G : microid_generator_space V k) :
lfe ⊤ (polytope_of_microid_generator G) (polytope_of_microid_generator (norm_generator G)) :=
begin
  unfold lfe,
  rintro u -,
  rcases polytope_of_norm_generator_smul G with ⟨c, hc₁, hc₂⟩,
  simp only [hc₂],
  rw [normal_face_homothety _ hc₁],
  rw [vector_span_homothety _ hc₁],
  apply_instance, -- why????
end

lemma lim_norm_gen {k : ℕ}
{t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k }
(htt : filter.tendsto t filter.at_top (𝓝 tl))
(hd : ∀ n : ℕ, diam_generator (t n) = 1) :
diam_generator tl = 1 :=
begin
  simp only [diam_generator],
  have tt₁ : filter.tendsto (λ n : ℕ, diam_generator (t n)) filter.at_top (𝓝 (diam_generator tl)),
  {
    convert (filter.tendsto.comp (continuous.continuous_at (diam_continuous k)) htt),
  },
  have tt₂ : filter.tendsto (λ n : ℕ, diam_generator (t n)) filter.at_top (𝓝 1),
  {
    simp only [hd],
    exact tendsto_const_nhds,
  },
  exact tendsto_nhds_unique tt₁ tt₂,
end

lemma prunenorm_id_eq_norm {k : ℕ} :
(prunenorm_generator id : microid_generator_space V k → microid_generator_space V k) =
norm_generator :=
begin
  funext,
  simp only [prunenorm_generator, chop_generator, subtype.val_eq_coe,
  function.comp.right_id, subtype.coe_eta],
end

noncomputable def generator_face {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) : finset (fin k.succ) :=
(finset.fin_range k.succ).filter (λ m, ∀ n : fin k.succ, ⟪G.val m, u⟫_ℝ ≥ ⟪G.val n, u⟫_ℝ)

lemma diam_generator_nonneg {k : ℕ}
(G : microid_generator_space V k) : diam_generator G ≥ 0 :=
begin
  simp only [diam_generator],
  exact metric.diam_nonneg,
end

lemma ex_finset_argmax {α : Type} (f : α → ℝ) {s : finset α} (hs : s.nonempty) :
∃ a ∈ s, ∀ b ∈ s, f a ≥ f b :=
begin
  have hsval : s.val ≠ 0,
  {
    intro h,
    rcases hs with ⟨x, hx⟩,
    simpa only [finset.mem_def, h] using hx,
  },
  rcases ex_multiset_argmax f hsval with ⟨a, ha, hp⟩,
  exact ⟨a, ha, hp⟩,
end

lemma generator_face_nonempty {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) :
(generator_face G u).nonempty :=
begin
  rcases ex_finset_argmax (λ x : fin k.succ, ⟪G.val x, u⟫_ℝ) ⟨0, finset.mem_univ 0⟩ with ⟨m, -, hp⟩,
  refine ⟨m, _⟩,
  simp only [generator_face],
  apply finset.mem_filter.mpr, split,
  {apply finset.mem_univ},
  {
    intro b,
    simp only at hp,
    exact hp b (finset.mem_univ _),
  },
end

lemma generator_face_equiv_fin {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) :
∃ c : ℕ, (generator_face G u).card = c.succ ∧ nonempty (generator_face G u ≃ fin c.succ) :=
begin
  rcases nat.exists_eq_succ_of_ne_zero
    (ne_of_gt (finset.nonempty.card_pos (generator_face_nonempty G u)))
    with ⟨c, hc⟩,
  refine ⟨c, hc, _⟩,
  {
    let eqv := finset.equiv_fin (generator_face G u),
    rw [hc] at eqv,
    exact ⟨eqv⟩,
  },
end

lemma norm_face_eq {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) :
generator_face (norm_generator G) u = generator_face G u :=
begin
  ext,
  simp only [generator_face, norm_generator, one_div, ge_iff_le, finset.mem_filter, finset.mem_fin_range,
    true_and],
  simp only [smul_sub, inner_sub_left, sub_le_sub_iff_right],
  by_cases hzero : diam_generator G = 0,
  {
    simp only [hzero, inv_zero, zero_smul, le_refl, forall_const, true_iff],
    intro n,
    rw [const_of_diam_zero hzero],
  },
  split,
  {
    intros h n,
    replace h := h n,
    simp only [inner_smul_left, is_R_or_C.conj_to_real] at h,
    replace h := mul_le_mul_of_nonneg_left h (diam_generator_nonneg G),
    rw [←mul_assoc] at h,
    rw [←mul_assoc] at h,
    simpa only [mul_inv_cancel hzero, one_mul] using h,
  },
  {
    intros h n,
    replace h := h n,
    simp only [inner_smul_left, is_R_or_C.conj_to_real],
    refine mul_le_mul_of_nonneg_left h _,
    exact inv_nonneg_of_nonneg (diam_generator_nonneg G),
  },
end

lemma chop_preserves_face_verts {k : ℕ}
{G : microid_generator_space V k} {c : ℕ} {φ : fin c.succ → fin k.succ}
{u : metric.sphere (0 : V) 1}
{m : fin c.succ} (h : φ m ∈ generator_face G u) :
m ∈ generator_face (chop_generator φ G) u :=
begin
  simp only [generator_face, chop_generator, subtype.val_eq_coe,
  function.comp_app, ge_iff_le, finset.mem_filter,
  finset.mem_fin_range, true_and] at h ⊢,
  intro n,
  exact h (φ n),
end

lemma prunenorm_preserves_face_verts {k : ℕ}
{G : microid_generator_space V k} {c : ℕ} {S : fin c.succ → fin k.succ}
{u : metric.sphere (0 : V) 1}
{m : fin c.succ} (h : S m ∈ generator_face G u) :
m ∈ generator_face (prunenorm_generator S G) u :=
begin
  simp only [prunenorm_generator, norm_face_eq],
  exact chop_preserves_face_verts h,
end

/- lemma pruning {k : ℕ}
{t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k}
(u : metric.sphere (0 : V) 1)
(ht : filter.tendsto t filter.at_top (𝓝 tl))
{c : ℕ}
{φ : fin c → fin k}
(h : generator_face tl u ⊆ finset.image φ finset.univ)
:
∃ (U ∈ 𝓝 u),
∀ᶠ n : ℕ in filter.at_top,
lfe U
(polytope_of_microid_generator (t n))
(polytope_of_microid_generator (chop_generator φ (t n))) :=
sorry -/

/-

-> locally face equivalent (lfe) polytopes (on a nbh U)
  -> on U, the faces vector_span the same spaces
-> pruning:
  -> let Ps be a convergent sequence of k-topes
  -> let Ps' be the sequence consisting of convex hulls of
     vertices converging to the u-face
  -> then Ps' is uniformly lfe to Ps on a common nbh U
-> if P ≃ P' on U, then their mixed area measures agree on U
-> if Ps ≃ Ps' on a common nbh U and Ps' converges to P',
   then P' is in the combinatorial closure of Ps
-> in the non-cuspy case with Ps, there is a subsequence Ps'
   that is lfe to a sequence Ps'' converging to a nontrivial k-tope
   P in uᗮ

-/

def genseq_convergent {k : ℕ}
(t : ℕ → microid_generator_space V k) :=
(∃ tl : microid_generator_space V k, filter.tendsto t filter.at_top (𝓝 tl))
-- ∧ (∃ m : fin k, ∀ n : ℕ, m ∈ generator_face (t n) u)

lemma exists_convergent_subseq {k : ℕ}
(t : ℕ → microid_generator_space V k) :
∃ ϕ : ℕ → ℕ, strict_mono ϕ ∧ genseq_convergent (t ∘ ϕ) :=
begin
  rcases tendsto_subseq_of_bounded metric.bounded_of_compact_space
  (λ n : ℕ, set.mem_univ (t n)) with ⟨tl, -, ϕ, mono, tt⟩,
  refine ⟨ϕ, mono, _⟩,
  exact ⟨tl, tt⟩,
end

noncomputable def angle {k : ℕ} -- x / 0 = 0
(l m : fin k.succ) (u : metric.sphere (0 : V) 1) (G : microid_generator_space V k): ℝ :=
⟪G.val m - G.val l, u⟫_ℝ / ∥ G.val m - G.val l ∥

lemma angle_def {k : ℕ}
(l m : fin k.succ) (u : metric.sphere (0 : V) 1):
angle l m u = λ G : microid_generator_space V k, angle l m u G := rfl

lemma angle_mul_norm_eq_inner_diff {k : ℕ}
(l m : fin k.succ) (u : metric.sphere (0 : V) 1) (G : microid_generator_space V k):
angle l m u G * ∥ G.val m - G.val l ∥ = ⟪G.val m - G.val l, u⟫_ℝ :=
begin
  simp only [angle],
  by_cases h : ∥ G.val m - G.val l ∥ = 0,
  {
    rw [h, mul_zero],
    replace h := norm_eq_zero.mp h,
    rw [h],
    rw [inner_zero_left],
  },
  {
    rw [div_mul_cancel _ h],
  }
end

def anglett {k : ℕ}
(l m : fin k.succ) (u : metric.sphere (0 : V) 1) (t : ℕ → microid_generator_space V k) : Prop :=
filter.tendsto (angle l m u ∘ t) filter.at_top (𝓝 0)

lemma filter_tendsto_generator_apply {k : ℕ}
(l : fin k.succ) {t : ℕ → microid_generator_space V k} {tl : microid_generator_space V k}
(h : filter.tendsto t filter.at_top (𝓝 tl)) :
filter.tendsto (λ n, (t n).val l) filter.at_top (𝓝 (tl.val l)) :=
begin
  refine tendsto_pi_nhds.mp _ l,
  simp only [subtype.val_eq_coe], -- magically only works if this is the second line
  refine filter.tendsto.comp _ h,
  apply continuous_at_subtype_coe,
end

lemma face_of_anglett {k : ℕ}
{l m : fin k.succ} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k}
(htt : filter.tendsto t filter.at_top (𝓝 tl))
(hl : anglett l m u t)
(hm : m ∈ generator_face tl u) :
l ∈ generator_face tl u :=
begin
  simp only [generator_face, finset.mem_filter] at hm ⊢,
  simp only [anglett] at hl,
  replace hm := hm.2,
  split,
  {simp only [finset.mem_fin_range]},
  {
    intro n,
    have : filter.tendsto (λ n : ℕ, ⟪(t n).val m - (t n).val l, u⟫_ℝ) filter.at_top
      (𝓝 (0 * ∥ tl.val m - tl.val l ∥)),
    {
      simp only [←angle_mul_norm_eq_inner_diff],
      apply filter.tendsto.mul hl,
      apply filter.tendsto.norm,
      apply filter.tendsto.sub,
      all_goals {exact filter_tendsto_generator_apply _ htt},
    },
    rw [zero_mul] at this,
    -- simp only [inner_sub_left] at this,
    have tt2 : filter.tendsto (λn : ℕ, ⟪(t n).val m - (t n).val l, u⟫_ℝ) filter.at_top
      (𝓝 (⟪tl.val m, u⟫_ℝ - ⟪tl.val l, u⟫_ℝ)),
    {
      simp only [inner_sub_left],
      apply filter.tendsto.sub,
      all_goals {
        apply filter.tendsto.inner,
        {exact filter_tendsto_generator_apply _ htt},
        {apply tendsto_const_nhds},
      },
    },
    have := tendsto_nhds_unique this tt2,
    rw [←eq_of_sub_eq_zero this.symm],
    exact hm n,
  },
end

lemma tendsto_subseq_of_tendsto {α : Type} [topological_space α]
(f : ℕ → α) {a : α} {φ : ℕ → ℕ} (hm : strict_mono φ)
(htt : filter.tendsto f filter.at_top (𝓝 a)) :
filter.tendsto (f ∘ φ) filter.at_top (𝓝 a) :=
begin
  -- intros x hx,
  -- rw [←filter.map_map],
  have : filter.tendsto φ filter.at_top filter.at_top,
  {
    apply monotone.tendsto_at_top_at_top,
    {
      intros a b h,
      cases h with b hb,
      {apply le_refl},
      {
        apply le_of_lt,
        exact hm (nat.lt_succ_of_le hb),
      },
    },
    {
      intro b,
      induction b,
      {
        simp only [zero_le', exists_const],
      },
      {
        rcases b_ih with ⟨c, hc⟩,
        have := hm (nat.lt_succ_self c),
        refine ⟨c.succ, nat.succ_le_of_lt _⟩,
        exact lt_of_le_of_lt hc this,
      },
    },
  },
  refine filter.tendsto.comp htt this,
end

lemma anglett_subsequence {k: ℕ}
{l m : fin k.succ} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k}
{ϕ : ℕ → ℕ} (hmon : strict_mono ϕ) (ha : anglett l m u t) : anglett l m u (t ∘ ϕ) :=
begin
  simp only [anglett] at ha ⊢,
  rw [←function.comp.assoc],
  apply tendsto_subseq_of_tendsto,
  all_goals {assumption},
end

lemma angle_norm {k : ℕ}
{l m : fin k.succ} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k}
:
angle l m u ∘ (norm_generator ∘ t) = angle l m u ∘ t :=
begin
  funext,
  simp only [angle, set.image_univ, one_div, function.comp_app],
  rcases dist_times_norm (t x) with ⟨v, hv⟩,
  rw [hv],
  simp only [←smul_sub, subtype.val_eq_coe, pi.add_apply, pi.smul_apply,
    add_sub_add_right_eq_sub],
  simp only [inner_smul_left, norm_smul, is_R_or_C.conj_to_real,
    real.norm_eq_abs],
  by_cases h : diam_generator (t x) = 0,
  {
    simp only [h, zero_mul, abs_zero, div_zero, div_eq_zero_iff, norm_eq_zero],
    apply or.inr,
    simp only [norm_generator, h, div_zero, zero_smul, subtype.coe_mk, sub_self],
  },
  {
    simp only [diam_generator] at h ⊢,
    rw [abs_eq_self.mpr (metric.diam_nonneg)],
    rw [mul_div_mul_left _ _ h],
  }
end

lemma anglett_norm_iff {k: ℕ}
{l m : fin k.succ} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k} :
anglett l m u t ↔ anglett l m u (norm_generator ∘ t) :=
begin
  simp only [anglett],
  rw [←function.comp.assoc],
  simp only [angle_norm],
end

lemma angle_chop {k₁ k₂ : ℕ}
{l m : fin k₁.succ} {u : metric.sphere (0 : V) 1}
(φ : fin k₁.succ → fin k₂.succ) :
angle (φ l) (φ m) u = angle l m u ∘ chop_generator φ :=
begin
  funext,
  simp only [angle, chop_generator, function.comp_app], -- Wow!
end

lemma anglett_chop {k₁ k₂ : ℕ}
{l m : fin k₁.succ} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k₂}
(φ : fin k₁.succ → fin k₂.succ) (h : anglett (φ l) (φ m) u t) :
anglett l m u (chop_generator φ ∘ t) :=
begin
  simp only [anglett] at h ⊢,
  rw [←function.comp.assoc],
  simpa only [angle_chop] using h,
end

lemma anglett_prunenorm {k₁ k₂ : ℕ}
{l m : fin k₁.succ} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k₂}
(φ : fin k₁.succ → fin k₂.succ) (h : anglett (φ l) (φ m) u t) :
anglett l m u (prunenorm_generator φ ∘ t) :=
begin
  simp only [prunenorm_def],
  rw [function.comp.assoc],
  apply anglett_norm_iff.mp,
  apply anglett_chop,
  exact h,
end

lemma common_face_subset_face_lim {k : ℕ}
{t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k}
{m : fin k.succ}
{u : metric.sphere (0 : V) 1}
(htt : filter.tendsto t filter.at_top (𝓝 tl))
(hf : ∀ n : ℕ, m ∈ generator_face (t n) u) :
m ∈ generator_face tl u :=
begin
  simp only [generator_face, finset.mem_filter, subtype.val_eq_coe,
    finset.mem_fin_range, true_and, ge_iff_le] at hf ⊢,
  intro n,
  have tt: ∀ l : fin k.succ,
  filter.tendsto (λ p, ⟪(t p : fin k.succ → V) l, u⟫_ℝ) filter.at_top (𝓝 ⟪(tl : fin k.succ → V) l, u⟫_ℝ),
  {
    intro l,
    refine filter.tendsto.inner _ _,
    {exact filter_tendsto_generator_apply _ htt},
    {apply tendsto_const_nhds},
  },
  apply le_of_tendsto_of_tendsto (tt n) (tt m),
  simp only [filter.eventually_le, filter.eventually_at_top, ge_iff_le],
  existsi 0,
  rintro b -,
  exact hf b n,
end

lemma pre_pruning_lemma {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → microid_generator_space V k}
{m : fin k.succ}
(hm : ∀ n : ℕ, m ∈ generator_face (t n) u) :
∃ (c : ℕ) (φ : fin c.succ → fin k.succ) (ϕ : ℕ → ℕ) (tl : microid_generator_space V c),
strict_mono ϕ ∧
filter.tendsto (prunenorm_generator φ ∘ t ∘ ϕ) filter.at_top (𝓝 tl) ∧
(∀ (l : fin c.succ),
l ∈ generator_face tl u) ∧
∀ l : fin k.succ, anglett l m u t →
l ∈ finset.image φ finset.univ :=
begin
  let k₀ := k,
  have hk : k ≤ k₀ := le_refl k,
  clear_value k₀,
  induction k₀ with k₀ ih generalizing k,
  {
    rcases nat.eq_zero_of_le_zero hk with rfl,
    refine ⟨0, id, _⟩,
    let t₁ := norm_generator ∘ t,
    rcases exists_convergent_subseq t₁ with ⟨ϕ₂, mon1, ⟨tl₂, cv₂⟩⟩,
    refine ⟨ϕ₂, tl₂, mon1, _, _, _⟩,
    {
      rw [prunenorm_id_eq_norm],
      exact cv₂,
    },
    {
      intros l,
      rcases generator_face_nonempty tl₂ u with ⟨l', hl'⟩,
      rcases fin.subsingleton_iff_le_one.mpr (le_refl 1) with ⟨show_eq⟩,
      simpa only [show_eq l l'] using hl',
    },
    {
      intros l tt,
      simp only [finset.image_id, finset.mem_univ],
    },
  },
  {
    let t₁ := norm_generator ∘ t,
    rcases exists_convergent_subseq t₁ with ⟨ϕ₂, mon1, ⟨tl₂, cv₂⟩⟩,
    let t₂ := t₁ ∘ ϕ₂,
    by_cases generator_face tl₂ u = finset.univ,
    {
      clear ih,
      refine ⟨k, id, ϕ₂, tl₂, mon1, _, _, _⟩,
      {
        rw [prunenorm_id_eq_norm],
        exact cv₂,
      },
      {
        intros l,
        simp only [h, finset.mem_univ],
      },
      {
        intros l tt,
        simp only [finset.image_id, finset.mem_univ],
      },
    },
    {
      -- replace h := finset.ssubset_iff_subset_ne.mpr ⟨finset.subset_univ _, h⟩,
      -- rcases finset.exists_of_ssubset h with ⟨x, ⟨-, xnface⟩⟩,
      let S := generator_face tl₂ u,
      rcases generator_face_equiv_fin tl₂ u with ⟨c, hc, ⟨Sfin⟩⟩,
      let incl : fin c.succ → fin k.succ := coe ∘ Sfin.inv_fun,
      have Scard : c ≤ k₀,
      {
        apply nat.le_of_lt_succ,
        refine nat.lt_of_lt_of_le _ hk,
        apply nat.lt_of_succ_lt_succ,
        rw [←hc],
        simpa only [fintype.card_fin] using (finset.card_lt_iff_ne_univ _).mpr h,
      },
      let t' := prunenorm_generator incl ∘ t₂,
      have mS : m ∈ S,
      {
        simp only [S],
        refine common_face_subset_face_lim cv₂ _,
        intro n,
        simp only [function.comp_app, t₁, norm_face_eq],
        apply hm,
      },
      let m' := Sfin ⟨m, mS⟩,
      have hm' : ∀ n : ℕ, m' ∈ generator_face (t' n) u,
      {
        intro n,
        refine prunenorm_preserves_face_verts _,
        simp only [t', t₂, t₁, m', incl, function.comp_app, equiv.inv_fun_as_coe,
          equiv.symm_apply_apply, subtype.coe_mk, norm_face_eq],
        apply hm,
      },
      rcases @ih _ t' _ hm' Scard with ⟨c, φ, ϕ₃, tl₃, monih, h1, h2, h3⟩,
      clear ih,
      let t₃ := prunenorm_generator φ ∘ t' ∘ ϕ₃,
      have heq: prunenorm_generator (incl ∘ φ) ∘ t ∘ (ϕ₂ ∘ ϕ₃) = prunenorm_generator φ ∘ t' ∘ ϕ₃,
      {
        simp only [t', t₂, t₁],
        rw [←prunenorm_id_eq_norm],
        funext,
        simp only [function.comp_app, prunenorm_prunenorm, function.comp.left_id],
      },
      refine ⟨c, incl ∘ φ, ϕ₂ ∘ ϕ₃, tl₃, _, _, h2, _⟩,
      {
        exact strict_mono.comp mon1 monih,
      },
      {
        simpa only [heq] using h1,
      },
      {
        intros l tt,
        have at₂ : anglett l m u t₂,
        {
          simp only [t₂, t₁],
          apply anglett_subsequence,
          any_goals {apply anglett_norm_iff.mp},
          all_goals {assumption},
        },
        have lS : l ∈ S,
        {
          simp only [S] at mS ⊢,
          refine face_of_anglett cv₂ _ mS,
          simpa only [t₂, t₁] using at₂,
        },
        let l' := Sfin ⟨l, lS⟩,
        have at' : anglett l' m' u t',
        {
          simp only [t'],
          apply anglett_prunenorm,
          simp only [incl, equiv.inv_fun_as_coe, function.comp_app,
            equiv.symm_apply_apply, subtype.coe_mk],
          exact at₂,
        },
        simp only [m', t', t₂, t₁] at h3,
        rcases finset.mem_image.mp (h3 l' at') with ⟨a, -, hal'⟩,
        refine finset.mem_image.mpr ⟨a, finset.mem_univ a, _⟩,
        simp only [hal', incl, equiv.inv_fun_as_coe, function.comp_app,
          equiv.symm_apply_apply, subtype.coe_mk],
      },
    },
  },
end

lemma pruning_lemma {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → prune_triple V k}
(valid : ∀ n : ℕ, valid_prune_triple (t n) u)
(tt : filter.tendsto ((cuspiness u) ∘ t) filter.at_top (𝓝 (0 : ℝ))) :
∃ G : microid_generator_space V k,
vector_span ℝ (polytope_of_microid_generator G).val ≤ vector_orth u.val ∧
in_combinatorial_closure u
((body_of_microid_generator ∘ prune_triple_generator ∘ t) '' set.univ)
(body_of_microid_generator G) :=
begin
  admit,
end

end blob
