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

def prune_generator {k : ℕ}
(S : finset (fin k)) (G : microid_generator_space V k) :
microid_generator_space V (S.card) := sorry

def diam_generator {k : ℕ}
(G : microid_generator_space V k) : nnreal := sorry

noncomputable def norm_generator {k : ℕ}
(G : microid_generator_space V k) : microid_generator_space V k :=
if diam_generator G = 0 then G else sorry

noncomputable def prunenorm_generator {k : ℕ}
(S : finset (fin k))
(G : microid_generator_space V k) : microid_generator_space V S.card :=
norm_generator (prune_generator S G)

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

lemma prunenorm_top_eq_norm {k : ℕ}
(G : microid_generator_space V k) :
prunenorm_generator ⊤ G == norm_generator G := sorry

noncomputable def generator_face {k : ℕ}
(G : microid_generator_space V k) (u : metric.sphere (0 : V) 1) : finset (fin k) :=
(finset.fin_range k).filter (λ m, ∀ n : fin k, ⟪G.val m, u⟫_ℝ ≥ ⟪G.val n, u⟫_ℝ)

lemma pruning {k : ℕ}
{t : ℕ → microid_generator_space V k}
{tl : microid_generator_space V k}
(u : metric.sphere (0 : V) 1)
(ht : filter.tendsto t filter.at_top (𝓝 tl)) :
∃ (U ∈ 𝓝 u),
∀ n : ℕ,
lfe U
(polytope_of_microid_generator (t n))
(polytope_of_microid_generator (prune_generator (generator_face tl u) (t n))) :=
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



lemma pre_pruning_lemma {k : ℕ} {u : metric.sphere (0 : V) 1}
{t : ℕ → microid_generator_space V k}
{m : fin k}
(hm : ∀ n : ℕ, m ∈ generator_face (t n) u) :
∃ (S : finset (fin k)) (ϕ : ℕ → ℕ) (tl : microid_generator_space V S.card),
filter.tendsto (prunenorm_generator S ∘ t ∘ ϕ) filter.at_top (𝓝 tl) ∧
(∀ (l : fin S.card) (n : ℕ),
l ∈ generator_face ((prunenorm_generator S ∘ t ∘ ϕ) n) u) ∧
∀ l ∈ S, (filter.tendsto (angle l m u ∘ t) filter.at_top (𝓝 0)) → l ∈ S :=
begin
  let k₀ := k,
  have hk : k ≤ k₀ := le_refl k,
  clear_value k₀,
  induction k₀ with k₀ ih generalizing k,
  {
    refine ⟨∅, id, ⟨0, _⟩, _⟩,
    {simp only [mem_ball_zero_iff], admit},
    {admit},
  },
  {
    let t₁ := norm_generator ∘ t,
    rcases exists_convergent_subseq t₁ with ⟨ϕ₂, mon1, ⟨tl₂, cv₂⟩⟩,
    let t₂ := t₁ ∘ ϕ₂,
    by_cases generator_face tl₂ u = ⊤,
    {
      clear ih,
      have topcard : (⊤ : finset (fin k)).card = k,
      {
        change finset.univ.card = k,
        field_simp [finset.order_top],
      },
      refine ⟨⊤, ϕ₂, _, _, _, _⟩,
      {
        rw [topcard],
        exact tl₂,
      },
      {
        
      }
    },
    {
      admit,
    }
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
