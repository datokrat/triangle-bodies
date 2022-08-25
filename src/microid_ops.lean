import convex convex_body multiset brunn_minkowski microid set_pi
  lfe init.data.fin.ops

open_locale pointwise
open_locale topological_space
open_locale nat

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

noncomputable def translate_gen {k : ℕ} (v : V) (G : unbounded_microid_generator V k) :
unbounded_microid_generator V k :=
λ l, G l + v

noncomputable def scale_gen {k : ℕ} (c : ℝ) (G : unbounded_microid_generator V k) :
unbounded_microid_generator V k :=
λ l, c • G l

noncomputable def scale_translate_gen {k : ℕ} (c : ℝ) (v : V) (G : unbounded_microid_generator V k) :
unbounded_microid_generator V k :=
scale_gen c (translate_gen v G)

def chop_generator' {k₁ k₂ : ℕ}
(φ : fin k₁.succ → fin k₂.succ)
(G : unbounded_microid_generator V k₂) :
unbounded_microid_generator V k₁ := G ∘ φ

def chop_generator {k : ℕ} {c : ℕ}
(φ : fin c.succ → fin k.succ)
(G : microid_generator_space V k) :
microid_generator_space V c :=
begin
  have Gprop := G.property,
  refine ⟨chop_generator' φ G, _⟩,
  simp only [chop_generator', subtype.val_eq_coe, mem_ball_zero_iff],
  simp only [metric.mem_closed_ball, dist_zero_right] at Gprop ⊢,
  rw [pi_norm_le_iff zero_le_one] at Gprop ⊢,
  intro b,
  apply Gprop,
end

lemma chop_def {k : ℕ} {c : ℕ}
{φ : fin c.succ → fin k.succ} :
(chop_generator φ : microid_generator_space V k → microid_generator_space V c)
= (λ G, chop_generator φ G) := rfl

/- lemma chop_smul {k₁ k₂ : ℕ}  {c : ℝ}
(φ : fin k₁.succ → fin k₂.succ)
(G : microid_generator_space V k₂) :
chop -/

noncomputable def diam_generator' {k : ℕ}
(G : unbounded_microid_generator V k) : ℝ :=
metric.diam (G '' set.univ)

lemma pi_range_bounded {α : Type} [fintype α]
(f : α → V) : metric.bounded (set.range f) :=
begin
  let C := finset.sup finset.univ (has_nnnorm.nnnorm ∘f),
  refine ⟨C + C, _⟩,
  intros x hx y hy,
  rcases set.mem_range.mp hx with ⟨x, rfl⟩,
  rcases set.mem_range.mp hy with ⟨y, rfl⟩,
  have nx : ∥ f x ∥₊ ≤ C := finset.le_sup (finset.mem_univ x),
  have ny : ∥ f y ∥₊ ≤ C := finset.le_sup (finset.mem_univ y),
  refine le_trans _ (add_le_add nx ny),
  apply dist_le_norm_add_norm,
end

lemma generator_range_bounded {k : ℕ}
(G : microid_generator_space V k) :
metric.bounded (set.range G.val) :=
begin
  apply pi_range_bounded,
end

lemma h_diam_continuous {k : ℕ} {ε : ℝ} (hε : ε > 0)
(x y : unbounded_microid_generator V k) (h : dist x y < ε / 4) :
diam_generator' x < ε + diam_generator' y :=
begin
  have hh : ε / 2 < ε := half_lt_self hε,
  have hδ' : 0 ≤ ε / 2 := div_nonneg (le_of_lt hε) (by simp only [zero_le_bit0, zero_le_one]),
  refine lt_of_le_of_lt _ (add_lt_add_right hh (diam_generator' y)),
  simp only [diam_generator'],
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
    have : x pu - x pv = ((x - y) pu - (x - y) pv) + (y pu - y pv),
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
      apply le_of_eq,
      ring,
    },
    {
      rw[←dist_eq_norm],
      refine metric.dist_le_diam_of_mem _ _ _,
      {
        simp only [set.image_univ],
        apply pi_range_bounded,
      },
      all_goals {
        refine (set.mem_image _ _ _).mp _,
        simp only [set.image_univ, set.mem_range_self],
      },
    },
  },
end

lemma diam_continuous (k : ℕ) :
continuous (diam_generator' : unbounded_microid_generator V k → ℝ) :=
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
  have hγ : γ > 0,
  {
    apply div_pos hε,
    simp only [zero_lt_bit0, zero_lt_one],
  },
  have hγ' : γ ≥ 0 := le_of_lt hγ,
  have hh : δ < ε := half_lt_self hε,
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
    refine h_diam_continuous hε _ _ hy,
  },
  {
    simp only [sub_lt_iff_lt_add],
    replace hy := metric.mem_ball.mp hy,
    refine h_diam_continuous hε _ _ hy,
  },
end

lemma const_of_diam_zero {k : ℕ}
{G : unbounded_microid_generator V k}
(h : diam_generator' G = 0) (m n : fin k.succ) :
G m = G n :=
begin
  simp only [diam_generator', set.image_univ] at h,
  apply dist_le_zero.mp,
  {
    rw [←h],
    refine metric.dist_le_diam_of_mem _ _ _,
    {apply pi_range_bounded},
    {simp only [set.mem_range_self]},
    {simp only [set.mem_range_self]},
  },
end

noncomputable def norm_generator' {k : ℕ}
(G : unbounded_microid_generator V k) : unbounded_microid_generator V k :=
scale_translate_gen (diam_generator' G)⁻¹ (-(G 0)) G

noncomputable def norm_generator {k : ℕ}
(G : microid_generator_space V k) : microid_generator_space V k :=
begin
  refine ⟨norm_generator' G.val, _⟩,
  simp only [norm_generator', set.image_univ, one_div, mem_closed_ball_zero_iff],
  simp only [pi.norm_def, nnnorm_smul],
  have : ∀ b : fin k.succ, ∥G.val b - G.val 0∥ ≤ diam_generator' G.val,
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
  rw [←real.coe_to_nnreal 1 zero_le_one],
  rw [nnreal.coe_le_coe],
  simp only [real.to_nnreal_one, finset.sup_le_iff, finset.mem_univ, forall_true_left],
  intro b,
  simp only [scale_translate_gen, scale_gen, translate_gen],
  rw [nnnorm_smul, nnnorm_inv, ←sub_eq_add_neg],
  have lem: ∀ r : nnreal, r⁻¹ * r ≤ 1,
  {
    intro r,
    by_cases hr : r = 0,
    {
      simp only [hr, mul_zero, zero_le'],
    },
    {
      rw [inv_mul_cancel hr],
    },
  },
  refine le_trans _ (lem ∥diam_generator' G.val∥₊),
  apply mul_le_mul_of_nonneg_left,
  {
    rw [←nnreal.coe_le_coe, coe_nnnorm, coe_nnnorm],
    rw [real.norm_eq_abs],
    refine le_trans (this b) _,
    apply le_abs_self,
  },
  {
    rw [←nnreal.coe_le_coe],
    simp only [nonneg.coe_zero, nonneg.coe_inv, coe_nnnorm,
      real.norm_eq_abs, inv_nonneg, abs_nonneg],
  },
end

lemma norm_generator_factor {k : ℕ}
(G : unbounded_microid_generator V k) :
norm_generator' G =
scale_translate_gen (diam_generator' G)⁻¹ (-(G 0)) G :=
begin
  funext,
  simp only [norm_generator', one_div, pi.smul_apply, pi.sub_apply],
end

lemma norm_generator_positive_factor₁ {k : ℕ}
(G : unbounded_microid_generator V k) (h : diam_generator' G = 0) :
norm_generator' G = scale_translate_gen 1 (-(G 0)) G :=
begin
  funext,
  simp only [norm_generator', scale_translate_gen, scale_gen, translate_gen,
    one_div, pi.sub_apply,
    function.const_apply, one_smul],
  rw [←sub_eq_add_neg],
  have : G l - G 0 = 0,
  {
    rw [const_of_diam_zero h _ 0],
    simp only [sub_self],
  },
  simp only [this, smul_zero],
end

lemma norm_generator_positive_factor₂ {k : ℕ}
(G : unbounded_microid_generator V k) (h : diam_generator' G ≠ 0) :
(diam_generator' G)⁻¹ > 0 ∧
norm_generator' G =
scale_translate_gen (diam_generator' G)⁻¹ (-(G 0)) G :=
begin
  replace h : diam_generator' G > 0,
  {
    simp only [diam_generator'] at h,
    exact ne.lt_of_le' h metric.diam_nonneg,
  },
  refine ⟨_, _⟩,
  {
    exact inv_pos_of_pos h,
  },
  {
    funext,
    simp only [norm_generator', one_div, pi.smul_apply, pi.sub_apply],
  },
end

lemma norm_generator_positive_factor {k : ℕ}
(G : unbounded_microid_generator V k) :
∃ c : ℝ, c > 0 ∧
norm_generator' G = scale_translate_gen c (-(G 0)) G :=
begin
  by_cases h : diam_generator' G = 0,
  {
    refine ⟨1, zero_lt_one, _⟩,
    exact norm_generator_positive_factor₁ G h,
  },
  {
    refine ⟨(diam_generator' G)⁻¹, _⟩,
    exact norm_generator_positive_factor₂ G h,
  }
end

lemma scale_translate_scale_translate {k : ℕ}
{c₁ c₂ : ℝ} {v₁ v₂ : V} {G : unbounded_microid_generator V k} (hc₂ : c₂ ≠ 0) :
scale_translate_gen c₁ v₁ (scale_translate_gen c₂ v₂ G) =
scale_translate_gen (c₁ * c₂) (c₂⁻¹ • v₁ + v₂) G :=
begin
  funext,
  simp only [scale_translate_gen, scale_gen, translate_gen],
  rw [←smul_eq_mul, smul_assoc],
  congr,
  simp only [smul_add, smul_inv_smul₀ hc₂],
  ac_refl,
end

lemma scale_translate_scale_translate' {k : ℕ}
{c₁ c₂ : ℝ} {v₁ v₂ : V} {G : unbounded_microid_generator V k} :
scale_translate_gen c₁ v₁ (scale_translate_gen c₂ v₂ G) =
translate_gen (c₁ • v₁ + (c₁ • c₂ • v₂)) (scale_gen (c₁ * c₂) G) :=
begin
  funext,
  simp only [scale_translate_gen, scale_gen, translate_gen],
  simp only [←smul_eq_mul, smul_assoc, smul_add],
  ac_refl,
end

lemma scale_translate_eq_translate_scale {k : ℕ}
{c : ℝ} {v : V} {G : unbounded_microid_generator V k} :
scale_gen c (translate_gen v G) = translate_gen (c • v) (scale_gen c G) :=
begin
  funext,
  simp only [scale_gen, translate_gen],
  simp only [←smul_eq_mul, smul_assoc, smul_add],
end

lemma scale_scale {k : ℕ}
{c₁ c₂ : ℝ} {G : unbounded_microid_generator V k} :
scale_gen c₁ (scale_gen c₂ G) = scale_gen (c₁ * c₂) G :=
begin
  funext,
  simp only [scale_gen],
  simp only [←smul_eq_mul, smul_assoc],
end

lemma translate_translate {k : ℕ}
{v₁ v₂ : V} {G : unbounded_microid_generator V k} :
translate_gen v₁ (translate_gen v₂ G) = translate_gen (v₁ + v₂) G :=
begin
  funext,
  simp only [translate_gen],
  ac_refl,
end

lemma translate_zero_scale_1 {k : ℕ}
(G : unbounded_microid_generator V k) :
G = translate_gen 0 (scale_gen 1 G) :=
begin
  funext,
  simp only [translate_gen, scale_gen],
  simp only [one_smul, add_zero],
end

lemma translate_zero {k : ℕ}
(G : unbounded_microid_generator V k) :
G = translate_gen 0 G :=
begin
  funext,
  simp only [translate_gen, add_zero],
end

lemma dist_times_norm {k : ℕ}
(G : unbounded_microid_generator V k) :
∃ v : V, G = translate_gen v (scale_gen (diam_generator' G) (norm_generator' G)) :=
begin
  simp only [norm_generator', scale_translate_gen],
  rw [scale_scale, scale_translate_eq_translate_scale],
  simp only [translate_translate], -- rw not working...
  by_cases h : diam_generator' G = 0,
  {
    refine ⟨_, _⟩, rotate,
    {
      simp only [translate_gen, scale_gen],
      simp only [h, zero_mul, zero_smul, add_zero, zero_add],
      funext,
      exact const_of_diam_zero h x 0,
    },
  },
  {
    refine ⟨_, _⟩, rotate,
    {
      convert translate_zero_scale_1 G,
      {refine neg_add_self _},
      {
        exact mul_inv_cancel h,
      },
    },
  },
end



lemma smul_set_bounded (c : ℝ) {A : set V} (hA : metric.bounded A) :
metric.bounded (c • A) :=
begin
  rcases hA with ⟨C, hC⟩,
  refine ⟨∥c∥ * C, _⟩,
  intros x hx y hy,
  rcases set.mem_smul_set.mp hx with ⟨px, hpx, rfl⟩,
  rcases set.mem_smul_set.mp hy with ⟨py, hpy, rfl⟩,
  rw [dist_smul],
  refine mul_le_mul_of_nonneg_left _ _,
  {exact hC px hpx py hpy},
  {apply norm_nonneg},
end

lemma set_bounded_of_smul {c : ℝ} (h : c > 0) {A : set V} (hA : metric.bounded (c • A)) :
metric.bounded A :=
begin
  convert smul_set_bounded c⁻¹ hA,
  rw [inv_smul_smul₀ (ne_of_gt h)],
end

lemma translate_set_bounded {A : set V} (hA : metric.bounded A) (v : V) :
metric.bounded (A + {v}) :=
begin
  rcases hA with ⟨C, hC⟩,
  refine ⟨C, _⟩,
  intros x hx y hy,
  rcases hx with ⟨xa, xv, hxa, hxv, rfl⟩,
  rcases hy with ⟨ya, yv, hya, hyv, rfl⟩,
  cases set.eq_of_mem_singleton hxv,
  cases set.eq_of_mem_singleton hyv,
  rw [dist_add_right],
  tauto,
end


lemma diam_smul {A : set V}  (hA : metric.bounded A) {c : ℝ} (h : c ≥ 0) :
metric.diam (c • A) = c * (metric.diam A) :=
begin
  revert A c,
  suffices hle : ∀ {A : set V} (hA : metric.bounded A) {c : ℝ}, c ≥ 0 → metric.diam (c • A) ≤ c * metric.diam A,
  {
    intros A c hA hc,
    apply le_antisymm,
    {exact hle hA hc},
    {
      by_cases h : c = 0,
      {
        rw [h, zero_mul],
        exact metric.diam_nonneg,
      },
      {
        replace hc := ne.lt_of_le (h ∘ eq.symm) hc,
        have := hle (smul_set_bounded c hA) (le_of_lt (inv_pos_of_pos hc)),
        rw [←mul_le_mul_left (inv_pos_of_pos hc), ←mul_assoc],
        rw [inv_mul_cancel (ne_of_gt hc), one_mul],
        convert this,
        rw [inv_smul_smul₀ (ne_of_gt hc)],
      }
    },
  },
  {
    intros A hA c hc,
    refine metric.diam_le_of_forall_dist_le _ _,
    {
      have : metric.diam A ≥ 0 := metric.diam_nonneg,
      positivity,
    },
    {
      intros x hx y hy,
      rcases set.mem_smul_set.mp hx with ⟨px, hpx, rfl⟩,
      rcases set.mem_smul_set.mp hy with ⟨py, hpy, rfl⟩,
      rw [dist_smul, real.norm_eq_abs, abs_of_nonneg hc],
      apply mul_le_mul_of_nonneg_left _ hc,
      exact metric.dist_le_diam_of_mem hA hpx hpy,
    },
  },
end

lemma diam_translate {A : set V} (hA : metric.bounded A) (v : V) :
metric.diam (A + {v}) = metric.diam A :=
begin
  revert A v,
  suffices h : ∀ {A : set V} (hA : metric.bounded A) (v : V), metric.diam (A + {v}) ≤ metric.diam A,
  {
    intros A v hA,
    apply le_antisymm,
    {
      exact h hA v,
    },
    {
      convert h (translate_set_bounded hA v) (-v),
      simp only [add_assoc, set.singleton_add_singleton, add_neg_self],
      simp only [set.add_singleton, add_zero, set.image_id'],
    },
  },
  {
    intros A hA v,
    refine metric.diam_le_of_forall_dist_le _ _,
    {exact metric.diam_nonneg},
    {
      intros x hx y hy,
      rcases hx with ⟨xa, xv, hxa, hxv, rfl⟩,
      rcases hy with ⟨ya, yv, hya, hyv, rfl⟩,
      cases set.eq_of_mem_singleton hxv,
      cases set.eq_of_mem_singleton hyv,
      rw [dist_add_right],
      exact metric.dist_le_diam_of_mem hA hxa hya,
    },
  },
end

lemma chop_scale_translate {k₁ k₂ : ℕ} {c : ℝ} (v : V)
(φ : fin k₁.succ → fin k₂.succ)
(G : unbounded_microid_generator V k₂) :
chop_generator' φ (scale_translate_gen c v G) = scale_translate_gen c v (chop_generator' φ G) :=
begin
  simp only [chop_generator', scale_translate_gen, scale_gen, translate_gen],
end

lemma chop_scale_translate' {k₁ k₂ : ℕ} {c : ℝ} (v : V)
(φ : fin k₁.succ → fin k₂.succ)
(G : unbounded_microid_generator V k₂) :
(scale_translate_gen c v G) ∘ φ = scale_translate_gen c v (G ∘ φ) :=
begin
  simp only [chop_generator', scale_translate_gen, scale_gen, translate_gen],
end

lemma diam_scale_translate {k : ℕ} {c : ℝ} (hc : c ≥ 0) (v : V)
(G : unbounded_microid_generator V k) :
diam_generator' (scale_translate_gen c v G) = c * diam_generator' G :=
begin
  simp only [scale_translate_gen, scale_gen, translate_gen],
  simp only [←pi.smul_def, diam_generator'],
  simp only [set_image_smul'],
  simp only [diam_generator', set.image_univ],
  rw [diam_smul (pi_range_bounded (λ i, G i + v)) hc, set.image_univ.symm],
  simp only [set_image_translate],
  rw [set.image_univ, diam_translate (pi_range_bounded G)],
end

lemma diam_chop_zero_of_diam_zero {k₁ k₂ : ℕ}
(φ : fin k₁.succ → fin k₂.succ)
(G : unbounded_microid_generator V k₂) :
diam_generator' G = 0 → diam_generator' (chop_generator' φ G) = 0 :=
begin
  simp only [diam_generator', chop_generator'],
  rw [set.image_comp],
  intro h,
  refine le_antisymm _ metric.diam_nonneg,
  refine le_trans (metric.diam_mono _ _) (le_of_eq h),
  {
    simp only [function.comp_app, set.image_univ, set.range_id'],
    apply set.range_comp_subset_range,
  },
  {
    rw [←set.image_comp, set.image_univ],
    apply pi_range_bounded,
  }
end

lemma scale_translate_zero {k : ℕ} {v : V} {G : unbounded_microid_generator V k} :
scale_translate_gen 0 v G = 0 :=
begin
  simp only [scale_translate_gen, scale_gen, translate_gen, zero_smul],
  refl,
end

lemma norm_chop_norm_eq_norm_chop {k₁ k₂ : ℕ}
(φ : fin k₁.succ → fin k₂.succ)
(G : unbounded_microid_generator V k₂) :
norm_generator' (chop_generator' φ (norm_generator' G)) = norm_generator' (chop_generator' φ G) :=
begin
  simp only [norm_generator_factor, chop_scale_translate, diam_scale_translate],
  by_cases h : diam_generator' G = 0,
  {
    simp only [h, inv_zero, zero_mul, diam_chop_zero_of_diam_zero _ _ h,
      scale_translate_zero],
    simp only [scale_translate_gen, translate_gen],
    simp only [pi.zero_apply, neg_zero, add_zero],
    simp only [scale_gen, smul_zero],
    refl,
  },
  {
    rw [scale_translate_scale_translate (inv_ne_zero h)],
    congr,
    {
      simp only [mul_inv, inv_inv],
      rw [diam_scale_translate _],
      rw [mul_comm, mul_inv, inv_inv],
      rw [←mul_assoc, inv_mul_cancel h, one_mul],
      apply inv_nonneg_of_nonneg,
      exact metric.diam_nonneg,
    },
    {
      rw [inv_inv],
      simp only [scale_translate_gen, scale_gen, translate_gen],
      simp only [chop_generator'],
      simp only [smul_neg, smul_inv_smul₀ h, neg_add, neg_neg, add_assoc,
        add_neg_self, add_zero],
    },
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

lemma norm_generator_idempotent {k : ℕ} (G : unbounded_microid_generator V k) :
norm_generator' (norm_generator' G) = norm_generator' G :=
begin
  simp only [norm_generator'],
  by_cases h : diam_generator' G = 0,
  {
    simp only [inv_zero, h],
    simp only [diam_generator'],
    simp only [set.image_univ],
    simp only [scale_translate_zero, pi.zero_apply, neg_zero],
    simp only [scale_translate_gen, scale_gen, translate_gen],
    simp only [pi.zero_apply, add_zero, smul_zero],
    refl,
  },
  {
    simp only [scale_translate_scale_translate (inv_ne_zero h)],
    congr,
    {
      have dnn: diam_generator' G ≥ 0 := metric.diam_nonneg,
      have idnn: (diam_generator' G)⁻¹ ≥ 0,
      {
        apply inv_nonneg_of_nonneg,
        exact metric.diam_nonneg,
      },
      rw [diam_scale_translate idnn, mul_inv, inv_inv],
      rw [←inv_inv (diam_generator' G)],
      generalize : (diam_generator' G)⁻¹ = x,
      rw [inv_inv],
      apply inv_mul_mul_self,
    },
    {
      rw [inv_inv, scale_translate_gen, scale_gen, translate_gen],
      simp only [add_right_neg, smul_zero, neg_zero, zero_add],
    },
  },
end

lemma diam_norm_generator {k : ℕ}
(G : unbounded_microid_generator V k) :
diam_generator' (norm_generator' G) = 1 ∨ diam_generator' G = 0 :=
begin
  simp only [norm_generator_factor],
  rw [diam_scale_translate _],
  {
    by_cases h : diam_generator' G = 0,
    {
      right,
      exact h,
    },
    {
      left,
      exact inv_mul_cancel h,
    },
  },
  {
    exact inv_nonneg_of_nonneg metric.diam_nonneg,
  },
end

lemma norm_generator_apply_zero {k : ℕ}
(G : unbounded_microid_generator V k) :
(norm_generator' G) 0 = 0 :=
begin
  simp only [norm_generator', scale_translate_gen, scale_gen, translate_gen],
  rw [←sub_eq_add_neg, sub_self, smul_zero],
end

/- lemma translate_scale_eq_norm_generator {k : ℕ}
{c : ℝ} (hc : c ≥ 0) (v : V) (G : unbounded_microid_generator V k) :
diam_generator' (scale_translate_gen c v G) = 1 ∧ (scale_translate_gen c v G 0 = 0) →
translate_gen v (scale_gen c G) = norm_generator' G :=
begin
  admit,
end -/

lemma translate_scale_eq_norm_generator' {k : ℕ} {c : ℝ} {v : V}
(G H : unbounded_microid_generator V k)
(h : H = translate_gen v (scale_gen c G)) (hc : c ≥ 0) :
(diam_generator' H = 1 ∨ diam_generator' G = 0) → H 0 = 0 → H = norm_generator' G :=
begin
  intros hd hz,
  cases hd,
  {
    simp only [h, norm_generator_factor, scale_translate_gen, scale_gen, translate_gen] at hz hd ⊢,
    replace hz := eq_neg_of_add_eq_zero_right hz,
    simp only [hz],
    funext,
    rw [←sub_eq_add_neg],
    rw [←sub_eq_add_neg],
    rw [←smul_sub],
    congr,
    apply eq_inv_of_mul_eq_one_left,
    rw [diam_generator', set.image_univ, ←diam_smul (pi_range_bounded _) hc],
    rw [←set.image_univ],
    rw [←set_image_smul', set.image_univ],
    rw [←diam_translate (pi_range_bounded _), ←set.image_univ],
    simp only [set_image_translate, diam_generator'] at hd,
    exact hd,
    all_goals {apply_instance},
  },
  {
    simp only [norm_generator', hd, h, scale_translate_gen, scale_gen, translate_gen] at hz ⊢,
    replace hz := eq_neg_of_add_eq_zero_right hz,
    simp only [hz],
    funext,
    rw [const_of_diam_zero hd l 0, ←sub_eq_add_neg, ←sub_eq_add_neg],
    simp only [sub_self, smul_zero],
  }
end

lemma diam_zero_of_diam_norm_zero {k : ℕ}
(G : unbounded_microid_generator V k) :
diam_generator' (norm_generator' G) = 0 → diam_generator' G = 0 :=
begin
  intro h,
  rcases diam_norm_generator G,
  {linarith},
  {assumption},
end

lemma diam_norm_one_of_diam_ne_zero {k : ℕ}
(G : unbounded_microid_generator V k) :
diam_generator' G ≠ 0 → diam_generator' (norm_generator' G) = 1 :=
begin
  intro h,
  rcases diam_norm_generator G,
  {assumption},
  {contradiction},
end

--set_option pp.all true
lemma prunenorm_prunenorm {c₁ c₂ c₃: ℕ}
(φ₁ : fin c₁.succ → fin c₂.succ) (φ₂ : fin c₂.succ → fin c₃.succ)
(G : microid_generator_space V c₃) :
prunenorm_generator φ₁ (prunenorm_generator φ₂ G) =
prunenorm_generator (φ₂ ∘ φ₁) G :=
begin
  simp only [prunenorm_generator, norm_generator, chop_generator],
  simp only [subtype.coe_mk, subtype.mk_eq_mk],
  simp only [norm_chop_norm_eq_norm_chop, chop_generator'],
  refine translate_scale_eq_norm_generator' _ _
    _ _ _ _, rotate, rotate,
  {
    conv {to_lhs, simp only [norm_generator']},
    have := chop_scale_translate,
    simp only [chop_generator'] at this,
    rw [this],
    rw [scale_translate_scale_translate'],
  },
  {
    simp only [diam_generator'],
    refine mul_nonneg _ _,
    all_goals {exact inv_nonneg_of_nonneg metric.diam_nonneg},
  },
  {
    by_cases h: diam_generator' (↑G ∘ φ₂ ∘ φ₁) = 0,
    {
      right,
      exact h,
    },
    {
      left,
      apply diam_norm_one_of_diam_ne_zero,
      simp only [norm_generator'],
      have : diam_generator' ((coe G : fin c₃.succ → V) ∘ φ₂) > 0,
      {
        simp only [diam_generator', set.image_univ],
        rw [diam_generator'] at h,
        replace h := ne.lt_of_le' h metric.diam_nonneg,
        rw [set.image_univ, ←function.comp.assoc] at h,
        refine lt_of_lt_of_le h _,
        refine metric.diam_mono _ (pi_range_bounded _),
        apply set.range_comp_subset_range,
      },
      rw [chop_scale_translate', diam_scale_translate],
      {
        apply mul_ne_zero,
        {exact ne_of_gt (inv_pos_of_pos this)},
        {rw [function.comp.assoc], exact h},
      },
      {exact le_of_lt (inv_pos_of_pos this)},
    },
  },
  {
    apply norm_generator_apply_zero,
  },
end

lemma sub_singleton_eq_add_singleton (A : set V) (v : V) :
A - {v} = A + {-v} :=
begin
  ext,
  simp only [set.mem_add, set.mem_sub, set.mem_singleton_iff],
  split,
  all_goals {
    intro h,
    rcases h with ⟨a, vv, ha, rfl, rfl⟩,
    refine ⟨a, _, ha, rfl, _⟩,
    rw [←sub_eq_add_neg],
  },
end

lemma diam_norm_generator_eq {k : ℕ}
(G : unbounded_microid_generator V k) :
diam_generator' G ≠ 0 → diam_generator' (norm_generator' G) = 1 :=
begin
  intro h,
  rcases norm_generator_positive_factor₂ G h with ⟨hgt, heq⟩,
  simp only [diam_generator', scale_translate_gen, scale_gen, translate_gen, heq],
  rw [←pi.smul_def, set_image_smul'],
  rw [diam_smul],
  {
    simp only [←sub_eq_add_neg],
    simp only [←pi.sub_def],
    rw [set_image_sub'],
    rw [sub_singleton_eq_add_singleton],
    rw [diam_translate],
    {
      convert inv_mul_cancel h,
    },
    {
      convert (pi_range_bounded G),
      exact set.image_univ,
    }
  },
  {
    rw [set.image_univ],
    refine pi_range_bounded _,
  },
  {
    apply inv_nonneg_of_nonneg,
    exact metric.diam_nonneg,
  },
end

lemma range_scale_translate {k : ℕ}
{c : ℝ} {v : V} {G : unbounded_microid_generator V k} :
(scale_translate_gen c v G) '' set.univ = c • ((G '' set.univ) + {v}) :=
begin
  simp only [scale_translate_gen, scale_gen, translate_gen],
  ext,
  simp only [set.mem_image, set.mem_smul, set.mem_add],
  split,
  {
    intro h,
    rcases h with ⟨l, -, rfl⟩,
    apply set.smul_mem_smul_set,
    refine ⟨G l, v, _, _, rfl⟩,
    {exact ⟨l, set.mem_univ _, rfl⟩},
    {apply set.mem_singleton},
  },
  {
    intro h,
    rcases h with ⟨y, ⟨py, vv, ⟨ppy, -, rfl⟩, hvv, rfl⟩, rfl⟩,
    cases set.eq_of_mem_singleton hvv,
    refine ⟨ppy, set.mem_univ _, rfl⟩,
  },
end

lemma polytope_of_norm_generator_smul {k : ℕ}
(G : microid_generator_space V k) :
∃ c : ℝ, c > 0 ∧
(polytope_of_microid_generator (norm_generator G)).val =
c • ((polytope_of_microid_generator G).val + {-(G.val 0)}) :=
begin
  rcases norm_generator_positive_factor G.val with ⟨c, hc₁, hc₂⟩,
  refine ⟨c, hc₁, _⟩,
  simp only [polytope_of_microid_generator, hc₂, norm_generator],
  rw [←set.image_univ],
  rw [range_scale_translate],
  rw [/- set_image_smul', -/ convex_hull_smul],
  congr,
  conv {to_rhs, rw [←@convex_hull_singleton ℝ V _ _ _ (-(G.val 0))]},
  rw [←convex_hull_add, set.image_univ],
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
  apply lfe_symm,
  rcases polytope_of_norm_generator_smul G with ⟨c, hc₁, hc₂⟩,
  refine ⟨c • (-G.val 0), c, hc₁, _⟩,
  simp only [bm.τ, convex_body_of_polytope, hc₂],
  --simp only [face_smul hc₁, face_translate],
  simp only [normal_face_homothety _ hc₁],
  simp only [smul_add],
  simp only [set.smul_set_Union₂],
  simp only [set.add_Union₂],
  simp only [set.smul_set_singleton],
  congr, funext, congr, funext,
  nth_rewrite 0 [add_comm],
end

lemma lim_norm_gen {k : ℕ}
{t : ℕ → unbounded_microid_generator V k}
{tl : unbounded_microid_generator V k }
(htt : filter.tendsto t filter.at_top (𝓝 tl))
(hd : ∀ n : ℕ, diam_generator' (t n) = 1) :
diam_generator' tl = 1 :=
begin
  simp only [diam_generator'],
  have tt₁ : filter.tendsto (λ n : ℕ, diam_generator' (t n)) filter.at_top (𝓝 (diam_generator' tl)),
  {
    have := @continuous.continuous_at (unbounded_microid_generator V k) ℝ _ _ _ _ (diam_continuous k),
    convert (filter.tendsto.comp this htt),
  },
  have tt₂ : filter.tendsto (λ n : ℕ, diam_generator' (t n)) filter.at_top (𝓝 1),
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
  simp only [chop_generator', function.comp.right_id, subtype.coe_eta],
end