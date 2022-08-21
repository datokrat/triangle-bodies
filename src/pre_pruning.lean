import convex convex_body multiset brunn_minkowski microid set_pi
  microid_ops sequence lfe
  --init.data.fin.ops

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
(∀ i : fin k.succ, ⟪prune_gen_fn t i, u⟫_ℝ ≤ ⟪prune_cusp t, u⟫_ℝ) ∧
prune_cusp t ≠ prune_secondary t

noncomputable def prune_direction {k : ℕ}
(t : prune_triple V k) : V :=
prune_cusp t - prune_secondary t

noncomputable def cuspiness {k : ℕ}
(u : metric.sphere (0 : V) 1) (t : prune_triple V k) : ℝ :=
⟪prune_direction t, u⟫_ℝ / ∥prune_direction t∥

noncomputable def cuspiness' {k : ℕ}
(u : V) (t : prune_triple V k) : ℝ :=
⟪prune_direction t, u⟫_ℝ / ∥prune_direction t∥

noncomputable def generator_face' {k : ℕ}
(G : unbounded_microid_generator V k) (u : metric.sphere (0 : V) 1) : finset (fin k.succ) :=
(finset.fin_range k.succ).filter (λ m, ∀ n : fin k.succ, ⟪G m, u⟫_ℝ ≥ ⟪G n, u⟫_ℝ)

noncomputable def generator_face {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) : finset (fin k.succ) :=
(finset.fin_range k.succ).filter (λ m, ∀ n : fin k.succ, ⟪G.val m, u⟫_ℝ ≥ ⟪G.val n, u⟫_ℝ)

lemma generator_face_generator_face' {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) :
generator_face G u = generator_face' G.val u := rfl

lemma diam_generator_nonneg {k : ℕ}
(G : unbounded_microid_generator V k) : diam_generator' G ≥ 0 :=
begin
  simp only [diam_generator'],
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

lemma generator_face_nonempty' {k : ℕ}
(G : unbounded_microid_generator V k) (u : metric.sphere (0 : V) 1) :
(generator_face' G u).nonempty :=
begin
  rcases ex_finset_argmax (λ x : fin k.succ, ⟪G x, u⟫_ℝ) ⟨0, finset.mem_univ 0⟩ with ⟨m, -, hp⟩,
  refine ⟨m, _⟩,
  simp only [generator_face'],
  apply finset.mem_filter.mpr, split,
  {apply finset.mem_univ},
  {
    intro b,
    simp only at hp,
    exact hp b (finset.mem_univ _),
  },
end

lemma generator_face_nonempty {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) :
(generator_face G u).nonempty :=
begin
  exact generator_face_nonempty' G.val u,
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
    true_and, norm_generator', scale_translate_gen, scale_gen, translate_gen],
  simp only [(sub_eq_add_neg _ _).symm, smul_sub,
    inner_sub_left, sub_le_sub_iff_right],
  by_cases hzero : diam_generator' G.val = 0,
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
    replace h := mul_le_mul_of_nonneg_left h (diam_generator_nonneg G.val),
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

lemma diam_norm_zero_of_diam_zero {k : ℕ}
{G : unbounded_microid_generator V k} (h : diam_generator' G = 0) :
diam_generator' (norm_generator' G) = 0 :=
begin
  rw [norm_generator_factor G, diam_scale_translate],
  {
    rw [h, mul_zero],
  },
  {
    rw [h, inv_zero],
    exact le_refl 0,
  },
end

lemma angle_norm {k : ℕ}
{l m : fin k.succ} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k}
:
angle l m u ∘ (norm_generator ∘ t) = angle l m u ∘ t :=
begin
  funext,
  simp only [angle, set.image_univ, one_div, function.comp_app],
  rcases dist_times_norm (t x).val with ⟨v, hv⟩,
  rw [hv],
  simp only [translate_gen, scale_gen],
  simp only [inner_sub_left, inner_add_left, add_sub_add_right_eq_sub],
  simp only [inner_sub_left.symm],
  rw [←smul_sub],
  simp only [inner_smul_left, norm_smul, is_R_or_C.conj_to_real,
    real.norm_eq_abs],
  by_cases h : diam_generator' (t x).val = 0,
  {
    simp only [h, zero_mul, abs_zero, div_zero, div_eq_zero_iff, norm_eq_zero],
    apply or.inr,
    simp only [norm_generator, h, div_zero, zero_smul, subtype.coe_mk, sub_self],
    have dnzero := diam_norm_zero_of_diam_zero h,
    have := const_of_diam_zero dnzero,
    rw [this m l, sub_self],
  },
  {
    simp only [diam_generator'] at h ⊢,
    rw [abs_eq_self.mpr (metric.diam_nonneg)],
    rw [mul_div_mul_left _ _ h],
    refl,
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
  simp only [angle, chop_generator, chop_generator',
    function.comp_app, subtype.val_eq_coe],
  -- Wow!
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

def is_facial_gap {k : ℕ}
(G : unbounded_microid_generator V k)
(u : metric.sphere (0 : V) 1)
(ε : ℝ) :=
ε > 0 ∧
∀ l m : fin k.succ,
l ∉ generator_face' G u →
m ∈ generator_face' G u →
⟪G m - G l, u⟫_ℝ > ε

lemma exists_facial_gap {k : ℕ}
(G : unbounded_microid_generator V k)
(u : metric.sphere (0 : V) 1) :
∃ ε : ℝ, is_facial_gap G u ε :=
begin
  by_cases h : (generator_face' G u)ᶜ = ∅,
  {
    refine ⟨1, zero_lt_one, _⟩,
    intros l m hl,
    rw [←finset.mem_compl, h] at hl,
    cases hl,
  },
  {
    replace h := finset.nonempty_of_ne_empty h,
    have h' := generator_face_nonempty' G u,
    let S := finset.product (generator_face' G u) (generator_face' G u)ᶜ,
    have ne : S.nonempty := finset.nonempty_product.mpr ⟨h', h⟩,
    let f : fin k.succ × fin k.succ → ℝ := λ p, ⟪G p.2 - G p.1, u⟫_ℝ,
    rcases ex_finset_argmax f ne with ⟨p, hp, prop⟩,
    simp only [finset.mem_product] at hp,
    let δ := f p,
    let ε := -(1/2) * δ,
    have hδ : δ < 0,
    {
      simp only [δ, f],
      rw [finset.mem_compl] at hp,
      by_contra,
      replace h := le_of_not_gt h,
      simp only [inner_sub_left, sub_nonneg] at h,
      rcases hp with ⟨hp₁, hp₂⟩,
      have p2gen : p.2 ∈ generator_face' G u,
      {
        simp only [generator_face', finset.mem_filter] at hp₁ ⊢,
        refine ⟨finset.mem_fin_range _, _⟩,
        intro n,
        exact le_trans (hp₁.2 n) h,
      },
      exact hp₂ p2gen,
    },
    refine ⟨ε, _, _⟩,
    {
      apply mul_pos_of_neg_of_neg,
      {simp only [one_div, right.neg_neg_iff, inv_pos, zero_lt_bit0, zero_lt_one]},
      {exact hδ},
    },
    {
      intros l m hl hm,
      simp only [ε],
      rw [←neg_sub, inner_neg_left, neg_mul, gt_iff_lt, neg_lt_neg_iff],
      have hle := prop ⟨m, l⟩ (finset.mem_product.mpr ⟨hm, finset.mem_compl.mpr hl⟩),
      simp only [f, ge_iff_le] at hle,
      refine lt_of_le_of_lt hle _,
      change δ < 1 / 2 * δ,
      rw [←neg_lt_neg_iff, ←mul_neg],
      rw [←neg_neg δ] at hδ,
      refine lt_of_le_of_lt (le_of_eq _) (half_lt_self (pos_of_neg_neg hδ)),
      ring,
    },
  },
end

lemma facial_stability {k : ℕ}
(G : unbounded_microid_generator V k)
(u : metric.sphere (0 : V) 1) :
∃ (U : set (unbounded_microid_generator V k))
(W : set (metric.sphere (0 : V) 1)),
U ∈ 𝓝 G ∧
W ∈ 𝓝 u ∧
∀ H v, H ∈ U → v ∈ W →
generator_face' H v ⊆ generator_face' G u :=
begin
  rcases exists_facial_gap G u with ⟨ε, hε, gap⟩,

  let f := λ x : ℝ, 2 * x + 2 * ∥G∥ * x,
  have fcont : continuous f := by continuity,
  have ftt : filter.tendsto f (𝓝 0) (𝓝 _) := fcont.continuous_at,
  have f0 : f 0 = 0,
  {
    simp only [f],
    ring,
  },
  simp only [filter.tendsto_def, f0] at ftt,
  replace ftt := ftt _ (metric.ball_mem_nhds 0 hε),
  simp only [metric.mem_nhds_iff, real.ball_eq_Ioo] at ftt,
  rcases ftt with ⟨τ, hτ, balls⟩,
  let ρ := τ / 2,
  have hρ : ρ > 0 := by exact half_pos hτ,
  have fρ : f ρ < ε,
  {
    simp only [zero_add] at balls,
    refine (balls _).2,
    split,
    {
      simp only [ρ],
      apply sub_left_lt_of_lt_add,
      positivity,
    },
    {
      exact half_lt_self hτ,
    },
  },

  let δ : ℝ := ρ,--min (ε / (8 * (∥G∥ + 1))) (real.sqrt ε) / 4,
  have hδ : δ > 0 := hρ,
  let γ : ℝ := ρ, --ε / 8,
  have hγ : γ > 0 := hρ,
  refine ⟨metric.ball G γ, metric.ball u δ,
    metric.ball_mem_nhds G hγ, metric.ball_mem_nhds u hδ, _⟩,
  intros H v hH hv,
  intros x hx,
  by_contra,
  rcases generator_face_nonempty' G u with ⟨y, hy⟩,
  have xygap := gap x y h hy,
  rw [←neg_sub, inner_neg_left] at xygap,
  rw [gt_iff_lt, lt_neg] at xygap,
  have eq₁ : (↑v : V) = ↑u + (↑v - ↑u) := (add_sub_cancel'_right _ _).symm,
  have eq₂ : H = G + (H - G) := (add_sub_cancel'_right _ _).symm,
  simp only [generator_face', finset.mem_filter] at hx,
  replace hx := hx.2 y,
  simp only [ge_iff_le] at hx,
  rw [←sub_nonneg, ←inner_sub_left] at hx,
  have := le_trans hx (dist_inner_inner (H x - H y) (G x - G y) v u),
  replace := lt_of_le_of_lt this (add_lt_add_right xygap _),
  have i1 : ∥u.val - v.val∥ ≤ δ,
  {
    rw [←dist_eq_norm, dist_comm],
    apply le_of_lt,
    exact hv,
  },
  have i2 : ∥(G x - G y) - (H x - H y)∥ ≤ 2 * γ,
  {
    rw [sub_sub_sub_comm],
    refine le_trans (norm_sub_le _ _) _,
    change ∥(G - H) x∥ + ∥(G - H) y∥ ≤ 2 * γ,
    refine le_trans (add_le_add (norm_le_pi_norm (G - H) _) (norm_le_pi_norm (G - H) _)) _,
    rw [←dist_eq_norm, dist_comm],
    apply le_of_lt,
    refine lt_of_lt_of_le (add_lt_add hH hH) _,
    ring_nf,
  },
  have i3 : ∥G x - G y∥ ≤ 2 * ∥G∥,
  {
    refine le_trans (norm_sub_le _ _) _,
    refine le_trans (add_le_add (norm_le_pi_norm _ _) (norm_le_pi_norm _ _)) _,
    ring_nf,
  },
  simp only [norm_eq_of_mem_sphere, mul_one, lt_neg_add_iff_add_lt,
    add_zero] at this,
  simp only [subtype.val_eq_coe.symm] at this,
  replace := lt_of_lt_of_le this
    (add_le_add i2 (mul_le_mul i3 i1 (norm_nonneg _) (by positivity))),

  replace := lt_trans this fρ,
  linarith,
end

def facial_chop_fn {k₁ k₂ : ℕ}
{G : microid_generator_space V k₂}
{u : metric.sphere (0 : V) 1}
(gfin : generator_face G u ≃ fin k₁.succ) :
fin k₁.succ → fin k₂.succ :=
coe ∘ gfin.inv_fun

lemma face_eq_hull_generator_face {k : ℕ}
(G : microid_generator_space V k)
(u : metric.sphere (0 : V) 1) :
normal_face (polytope_of_microid_generator G).val u =
convex_hull ℝ (G.val '' generator_face G u) :=
begin
  simp only [polytope_of_microid_generator],
  simp only [normal_face_spanned_by_verts],
  apply subset_antisymm,
  {
    apply convex_hull_mono,
    intros x hx,
    simp only [mem_normal_face] at hx,
    rcases hx.1 with ⟨px, rfl⟩,
    refine ⟨px, _, rfl⟩,
    {
      simp only [generator_face, finset.mem_coe, finset.mem_filter],
      refine ⟨finset.mem_fin_range _, _⟩,
      intro n,
      exact hx.2 (G.val n) ⟨n, rfl⟩,
    },
  },
  {
    apply convex_hull_mono,
    intros x hx,
    simp only [mem_normal_face],
    rcases hx with ⟨px, hpx, rfl⟩,
    split,
    {
      exact ⟨px, rfl⟩,
    },
    {
      intros y hy,
      rcases hy with ⟨py, rfl⟩,
      simp only [generator_face, finset.mem_coe, finset.mem_filter] at hpx,
      exact hpx.2 py,
    },
  },
end

lemma face_chop_eq_of_generator_face {k₁ k₂ : ℕ}
{G : microid_generator_space V k₂}
{u : metric.sphere (0 : V) 1}
(φ : fin k₁.succ → fin k₂.succ)
(h : (generator_face G u : set (fin k₂.succ)) ⊆ set.range φ) :
normal_face
(polytope_of_microid_generator (chop_generator φ G)).val u =
normal_face
(polytope_of_microid_generator G).val u :=
begin
    simp only [face_eq_hull_generator_face],
    refine congr_arg _ _,
    have hge : (chop_generator φ G).val '' ↑(generator_face (chop_generator φ G) u) ≥ G.val '' ↑(generator_face G u),
    {
      rintro x ⟨px, hpx, rfl⟩,
      rcases h hpx with ⟨ppx, hppx, rfl⟩,
      refine ⟨ppx, _, rfl⟩,
      {
        rw [generator_face, finset.mem_coe, finset.mem_filter] at hpx ⊢,
        refine ⟨finset.mem_fin_range _, _⟩,
        intro n,
        simp only [chop_generator, chop_generator', function.comp_app],
        exact hpx.2 (φ n),
      },
    },
    apply le_antisymm,
    {
      rintro x ⟨px, hpx, rfl⟩,
      simp only [chop_generator, chop_generator'],
      refine ⟨φ px, _, rfl⟩,
      rw [generator_face, finset.mem_coe, finset.mem_filter] at hpx ⊢,
      refine ⟨finset.mem_fin_range _, _⟩,
      intro n,

      rcases generator_face_nonempty G u with ⟨m, hm⟩,
      rcases hge ⟨m, hm, rfl⟩ with ⟨pm, hpm, hpmeq⟩,
      rw [generator_face, finset.mem_filter] at hm,
      refine le_trans (hm.2 n) _,
      rw [←hpmeq],
      exact hpx.2 pm,
    },
    {
      exact hge,
    }
end

lemma facial_chopping_lemma {k₁ k₂ : ℕ}
{G : microid_generator_space V k₂}
{u : metric.sphere (0 : V) 1}
(gfin : generator_face G u ≃ fin k₁.succ) :
∃ (U : set (microid_generator_space V k₂))
(W : set (metric.sphere (0 : V) 1)),
U ∈ 𝓝 G ∧
W ∈ 𝓝 u ∧
∀ H, H ∈ U →
lfe W
(polytope_of_microid_generator H)
(polytope_of_microid_generator
(chop_generator (facial_chop_fn gfin) H)) :=
begin
  rcases facial_stability G.val u
    with ⟨U', W, hU', hW, h⟩,
  let U : set (microid_generator_space V k₂) := coe ⁻¹' U',
  refine ⟨U, W, _, hW, _⟩,
  {
    simp only [U],
    rw [preimage_coe_mem_nhds_subtype],
    exact mem_nhds_within_of_mem_nhds hU',
  },
  {
    intros H hH,
    intros w hw,
    refine ⟨0, 1, zero_lt_one, _⟩,
    rw [one_smul],
    simp only [subtype.val_eq_coe, set.singleton_add, zero_add, set.image_id'],
    symmetry,
    refine face_chop_eq_of_generator_face _ _,
    rintro l hl,
    refine ⟨gfin ⟨l, _⟩, _⟩,
    {exact (h H.val w hH hw) hl},
    {
      simp only [facial_chop_fn, equiv.inv_fun_as_coe,
        function.comp_app, equiv.symm_apply_apply,
        subtype.coe_mk],
    },
  },
end

lemma lfe_prunenorm {k₁ k₂ : ℕ}
{t : ℕ → microid_generator_space V k₂}
{tl : microid_generator_space V k₂}
{u : metric.sphere (0 : V) 1}
(gfin : generator_face tl u ≃ fin k₁.succ)
(tt : filter.tendsto t filter.at_top (𝓝 tl)) :
∃ U : set (metric.sphere (0 : V) 1),
U ∈ 𝓝 u ∧
∀ᶠ n in filter.at_top, lfe U
(polytope_of_microid_generator (t n))
(polytope_of_microid_generator
  (prunenorm_generator (coe ∘ gfin.inv_fun) (t n))) :=
begin
  rcases facial_chopping_lemma gfin
    with ⟨U, W, hU, hW, h⟩,
  refine ⟨W, hW, _⟩,
  rw [filter.tendsto_def] at tt,
  refine filter.eventually.mono (tt U hU) _,
  intros n hn,
  simp only [prunenorm_generator],
  rw [←set.inter_univ W],
  refine lfe_trans _ (gen_lfe_norm _),
  exact h _ hn,
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

lemma prunenorm_norm {c₁ c₂: ℕ}
(φ₁ : fin c₁.succ → fin c₂.succ)
(G : microid_generator_space V c₂) :
prunenorm_generator φ₁ (norm_generator G) =
prunenorm_generator (φ₁) G :=
begin
  rw [←prunenorm_id_eq_norm, prunenorm_prunenorm, function.left_id],
end

def is_pre_pruning_seq {k₁ k₂ : ℕ} (u : metric.sphere (0 : V) 1)
(t : ℕ → microid_generator_space V k₂)
(tl : microid_generator_space V k₁)
(φ : fin k₁.succ → fin k₂.succ)
(m : fin k₂.succ)
(ϕ : ℕ → ℕ) :=
strict_mono ϕ ∧
filter.tendsto (prunenorm_generator φ ∘ t ∘ ϕ) filter.at_top (𝓝 tl) ∧
(∀ (l : fin k₁.succ), l ∈ generator_face tl u) ∧
(∀ l : fin k₂.succ, anglett l m u t → l ∈ finset.image φ finset.univ)

lemma subseq_is_pre_pruning_seq {k₁ k₂ : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → microid_generator_space V k₂}
{tl : microid_generator_space V k₁}
{φ : fin k₁.succ → fin k₂.succ}
{m : fin k₂.succ}
{ϕ : ℕ → ℕ}
{ns : ℕ → ℕ}
(h : is_pre_pruning_seq u t tl φ m ϕ)
(mon : strict_mono ns) : is_pre_pruning_seq u t tl φ m (ϕ ∘ ns) :=
begin
  rcases h with ⟨hϕ, h2, h3, h4⟩,
  exact ⟨strict_mono.comp hϕ mon, tendsto_subseq_of_tendsto _ mon h2, h3, h4⟩,
end

lemma pre_pruning_lemma {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → microid_generator_space V k}
{m : fin k.succ}
(hm : ∀ n : ℕ, m ∈ generator_face (t n) u) :
∃ (c : ℕ) (φ : fin c.succ → fin k.succ) (ϕ : ℕ → ℕ)
(tl : microid_generator_space V c),
c ≤ k ∧
is_pre_pruning_seq u t tl φ m ϕ ∧
∃ U : set (metric.sphere (0 : V) 1), U ∈ 𝓝 u ∧
∀ n : ℕ,
lfe U
(polytope_of_microid_generator (t (ϕ n)))
(polytope_of_microid_generator ((prunenorm_generator φ ∘ t ∘ ϕ) n))
:=
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
    refine ⟨ϕ₂, tl₂, le_refl 0, ⟨mon1, _, _, _⟩, _⟩,
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
    {
      simp only [prunenorm_id_eq_norm, function.comp_app],
      refine ⟨⊤, filter.univ_mem, _⟩,
      intro n,
      apply gen_lfe_norm,
    },
  },
  {
    let t₁ := norm_generator ∘ t,
    rcases exists_convergent_subseq t₁ with ⟨ϕ₂, mon1, ⟨tl₂, cv₂⟩⟩,
    let t₂ := t₁ ∘ ϕ₂,
    by_cases generator_face tl₂ u = finset.univ,
    {
      clear ih,
      refine ⟨k, id, ϕ₂, tl₂, le_refl k, ⟨mon1, _, _, _⟩, _⟩,
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
      {
        simp only [prunenorm_id_eq_norm, function.comp_app],
        refine ⟨⊤, filter.univ_mem, _⟩,
        intro n,
        apply gen_lfe_norm,
      },
    },
    {
      -- replace h := finset.ssubset_iff_subset_ne.mpr ⟨finset.subset_univ _, h⟩,
      -- rcases finset.exists_of_ssubset h with ⟨x, ⟨-, xnface⟩⟩,
      let S := generator_face tl₂ u,
      rcases generator_face_equiv_fin tl₂ u with ⟨c, hc, ⟨Sfin⟩⟩,
      let incl : fin c.succ → fin k.succ := coe ∘ Sfin.inv_fun,
      have cltk : c < k,
      {
        apply nat.lt_of_succ_lt_succ,
        rw [←hc],
        simpa only [fintype.card_fin] using (finset.card_lt_iff_ne_univ _).mpr h,
      },
      have Scard : c ≤ k₀,
      {
        apply nat.le_of_lt_succ,
        refine nat.lt_of_lt_of_le _ hk,
        exact cltk,
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
      rcases @ih _ t' _ hm' Scard with ⟨c', φ, ϕ₃, tl₃, c'lec, ⟨mon₃, h1, h2, h3⟩, h4⟩,
      clear ih,
      let t₃ := prunenorm_generator φ ∘ t' ∘ ϕ₃,
      have heq: prunenorm_generator (incl ∘ φ) ∘ t ∘ (ϕ₂ ∘ ϕ₃) = prunenorm_generator φ ∘ t' ∘ ϕ₃,
      {
        simp only [t', t₂, t₁],
        rw [←prunenorm_id_eq_norm],
        funext,
        simp only [function.comp_app, prunenorm_prunenorm, function.comp.left_id],
      },
      have : is_pre_pruning_seq u t tl₃ (incl ∘ φ) m (ϕ₂ ∘ ϕ₃),
      {
        refine ⟨_, _, h2, _⟩,
        {
          exact strict_mono.comp mon1 mon₃,
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
      have cv₃ := tendsto_subseq_of_tendsto _ mon₃ cv₂,
      rcases lfe_prunenorm Sfin cv₃ with
        ⟨U₂, oU₂, lU₂⟩,
      let p := λ n : ℕ, lfe U₂ (polytope_of_microid_generator ((t₁ ∘ ϕ₂) n)) (polytope_of_microid_generator (prunenorm_generator (coe ∘ Sfin.inv_fun) ((t₁ ∘ ϕ₂) n))),
      rcases subseq_forall_of_frequently' p lU₂.frequently with
        ⟨ϕ₄, mono₄, lU₂'⟩,
      replace this := subseq_is_pre_pruning_seq this mono₄,
      refine ⟨c', incl ∘ φ, (ϕ₂ ∘ ϕ₃) ∘ ϕ₄, tl₃, _, this, _⟩,
      {
        exact le_trans c'lec (le_of_lt cltk),
      },
      {
        rcases h4 with ⟨U₁, oU₁, lU₁⟩,
        simp only [function.comp_app],
        simp only [t', t₂, t₁, function.comp_app] at lU₁,
        simp only [p, t₁, function.comp_app] at lU₂',
        simp only [prunenorm_norm] at lU₁ lU₂', -- rw not working
        refine ⟨U₂ ∩ U₁, filter.inter_mem oU₂ oU₁, _⟩,
        intro n,
        rw [←prunenorm_prunenorm],
        simp only [incl] at lU₁ ⊢,
        refine lfe_trans _ (lU₁ (ϕ₄ n)),
        rw [←set.univ_inter U₂],
        exact lfe_trans (gen_lfe_norm _) (lU₂' n),
      },
    },
  },
end

end blob