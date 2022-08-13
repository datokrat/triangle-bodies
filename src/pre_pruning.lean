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
∀ i : fin k, ⟪prune_gen_fn t i, u⟫_ℝ ≤ ⟪prune_cusp t, u⟫_ℝ ∧
prune_cusp t ≠ prune_secondary t

noncomputable def prune_direction {k : ℕ}
(t : prune_triple V k) : V :=
prune_cusp t - prune_secondary t

noncomputable def cuspiness {k : ℕ}
(u : metric.sphere (0 : V) 1) (t : prune_triple V k) : ℝ :=
⟪prune_direction t, u⟫_ℝ / ∥prune_direction t∥



noncomputable def generator_face {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) : finset (fin k.succ) :=
(finset.fin_range k.succ).filter (λ m, ∀ n : fin k.succ, ⟪G.val m, u⟫_ℝ ≥ ⟪G.val n, u⟫_ℝ)

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

end blob