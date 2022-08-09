import convex convex_body multiset brunn_minkowski microid

open_locale pointwise
open_locale topological_space

section defs

variables (V : Type) [inner_product_space ℝ V] [finite_dimensional ℝ V]

def prune_triple (k : ℕ) :=
microid_generator_space V k × fin k × fin k

end defs

section blob

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]


def prune_triple_generator {k : ℕ}
(t : prune_triple V k) : microid_generator_space V k := t.1

def prune_gen_fn {k : ℕ}
(t : prune_triple V k) : fin k → V := t.1.val

def prune_cusp_index {k : ℕ}
(t : prune_triple V k) : fin k := t.2.1

def prune_cusp {k : ℕ}
(t : prune_triple V k) : V :=
prune_gen_fn t (prune_cusp_index t)

def prune_secondary_index {k : ℕ}
(t : prune_triple V k) : fin k := t.2.2

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
(φ : fin c → fin k)
(G : microid_generator_space V k) :
microid_generator_space V c :=
begin
  refine ⟨G.val ∘ φ, _⟩,
  simp only [subtype.val_eq_coe, mem_ball_zero_iff],
  admit,
end

def diam_generator {k : ℕ}
(G : microid_generator_space V k) : nnreal := sorry

noncomputable def norm_generator {k : ℕ}
(G : microid_generator_space V k) : microid_generator_space V k :=
if diam_generator G = 0 then G else sorry

noncomputable def prunenorm_generator {k : ℕ} {c : ℕ}
(φ : fin c → fin k)
(G : microid_generator_space V k) : microid_generator_space V c :=
norm_generator (chop_generator φ G)

lemma prunenorm_def {k : ℕ} {c : ℕ}
(φ : fin c → fin k) :
(prunenorm_generator φ : microid_generator_space V k → microid_generator_space V c) =
norm_generator ∘ chop_generator φ := sorry

lemma prunenorm_prunenorm {c₁ c₂ c₃: ℕ}
(φ₁ : fin c₁ → fin c₂) (φ₂ : fin c₂ → fin c₃)
(G : microid_generator_space V c₃) :
prunenorm_generator φ₁ (prunenorm_generator φ₂ G) =
prunenorm_generator (φ₂ ∘ φ₁) G :=
sorry

lemma diam_norm_generator_eq {k : ℕ}
(G : microid_generator_space V k) :
diam_generator G ≠ 0 → diam_generator (norm_generator G) = 1 := sorry

lemma gen_lfe_norm {k : ℕ}
(G : microid_generator_space V k) :
lfe ⊤ (polytope_of_microid_generator G) (polytope_of_microid_generator (norm_generator G)) :=
sorry

lemma lim_norm_gen {k : ℕ}
{t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k }
(htt : filter.tendsto t filter.at_top (𝓝 tl))
(hd : ∀ n : ℕ, diam_generator (t n) = 1) :
diam_generator tl = 1 := sorry

lemma prunenorm_id_eq_norm {k : ℕ} :
(prunenorm_generator id : microid_generator_space V k → microid_generator_space V k) =
norm_generator := sorry

noncomputable def generator_face {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) : finset (fin k) :=
(finset.fin_range k).filter (λ m, ∀ n : fin k, ⟪G.val m, u⟫_ℝ ≥ ⟪G.val n, u⟫_ℝ)

lemma norm_face_eq {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) :
generator_face (norm_generator G) u = generator_face G u := sorry

lemma chop_preserves_face_verts {k : ℕ}
{G : microid_generator_space V k} {c : ℕ} {S : fin c → fin k}
{u : metric.sphere (0 : V) 1}
{m : fin c} (h : S m ∈ generator_face G u) :
m ∈ generator_face (chop_generator S G) u := sorry

lemma prunenorm_preserves_face_verts {k : ℕ}
{G : microid_generator_space V k} {c : ℕ} {S : fin c → fin k}
{u : metric.sphere (0 : V) 1}
{m : fin c} (h : S m ∈ generator_face G u) :
m ∈ generator_face (prunenorm_generator S G) u :=
begin
  simp only [prunenorm_generator, norm_face_eq],
  exact chop_preserves_face_verts h,
end

lemma pruning {k : ℕ}
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
sorry

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
∃ ϕ : ℕ → ℕ, strict_mono ϕ ∧ genseq_convergent (t ∘ ϕ) := sorry

noncomputable def angle {k : ℕ} -- x / 0 = 0
(l m : fin k) (u : metric.sphere (0 : V) 1) (G : microid_generator_space V k): ℝ :=
⟪G.val m - G.val l, u⟫_ℝ / ∥ G.val m - G.val l ∥

def anglett {k : ℕ}
(l m : fin k) (u : metric.sphere (0 : V) 1) (t : ℕ → microid_generator_space V k) : Prop :=
filter.tendsto (angle l m u ∘ t) filter.at_top (𝓝 0)

def face_of_anglett {k : ℕ}
{l m : fin k} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k}
(htt : filter.tendsto t filter.at_top (𝓝 tl))
(hl : anglett l m u t)
(hm : m ∈ generator_face tl u) :
l ∈ generator_face tl u := sorry

lemma anglett_subsequence {k: ℕ}
{l m : fin k} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k}
{ϕ : ℕ → ℕ} (hmon : strict_mono ϕ) (ha : anglett l m u t) : anglett l m u (t ∘ ϕ) :=
sorry

lemma anglett_norm_iff {k: ℕ}
{l m : fin k} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k} :
anglett l m u t ↔ anglett l m u (norm_generator ∘ t) :=
sorry

lemma anglett_chop {k₁ k₂ : ℕ}
{l m : fin k₁} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k₂}
(φ : fin k₁ → fin k₂) (h : anglett (φ l) (φ m) u t) :
anglett l m u (chop_generator φ ∘ t) := sorry

lemma anglett_prunenorm {k₁ k₂ : ℕ}
{l m : fin k₁} {u : metric.sphere (0 : V) 1} {t : ℕ → microid_generator_space V k₂}
(φ : fin k₁ → fin k₂) (h : anglett (φ l) (φ m) u t) :
anglett l m u (prunenorm_generator φ ∘ t) := sorry

lemma common_face_subset_face_lim {k : ℕ}
{t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k}
{m : fin k}
{u : metric.sphere (0 : V) 1}
(htt : filter.tendsto t filter.at_top (𝓝 tl))
(hf : ∀ n : ℕ, m ∈ generator_face (t n) u) :
m ∈ generator_face tl u := sorry

lemma pre_pruning_lemma {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → microid_generator_space V k}
{m : fin k}
(hm : ∀ n : ℕ, m ∈ generator_face (t n) u) :
∃ (c : ℕ) (φ : fin c → fin k) (ϕ : ℕ → ℕ) (tl : microid_generator_space V c),
strict_mono ϕ ∧
filter.tendsto (prunenorm_generator φ ∘ t ∘ ϕ) filter.at_top (𝓝 tl) ∧
(∀ (l : fin c),
l ∈ generator_face tl u) ∧
∀ l : fin k, anglett l m u t →
l ∈ finset.image φ finset.univ :=
begin
  let k₀ := k,
  have hk : k ≤ k₀ := le_refl k,
  clear_value k₀,
  induction k₀ with k₀ ih generalizing k,
  {
    refine ⟨0, fin.elim0, id, ⟨0, _⟩, _⟩,
    {simp only [mem_ball_zero_iff], admit},
    {admit},
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
      let Sfin := finset.equiv_fin S,
      let incl : fin S.card → fin k := coe ∘ Sfin.inv_fun,
      have Scard : S.card ≤ k₀,
      {
        apply nat.le_of_lt_succ,
        refine nat.lt_of_lt_of_le _ hk,
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
