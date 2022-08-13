import convex convex_body brunn_minkowski microid
  measure set_pi
  init.data.fin.ops

open_locale pointwise
open_locale topological_space
open_locale nat

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]


def lfe --locally face equivalent
(U : set (metric.sphere (0 : V) 1))
(P Q : polytope V) :=
∀ u : metric.sphere (0 : V) 1,
u ∈ U → vector_span ℝ (normal_face P.val u) = vector_span ℝ (normal_face Q.val u)

def in_combinatorial_closure
(u : metric.sphere (0 : V) 1)
(S : set (convex_body V))
(K : convex_body V) :=
∀ Ps : multiset (convex_body V), dim V = Ps.card + 1 →
u ∈ msupport (bm.area (K ::ₘ Ps)) →
u ∈ closure (⋃ L ∈ S, msupport (bm.area (L ::ₘ Ps)))

lemma comb_cl_of_lfe
{U : set (metric.sphere (0 : V) 1)}
{u : metric.sphere (0 : V) 1}
{t : ℕ → polytope V}
{S : set (polytope V)}
{tl : convex_body V}
(hU : is_open U)
(uU : u ∈ U)
(tt : filter.tendsto (λ n, convex_body_of_polytope V (t n))
  filter.at_top (𝓝 tl))
(hl : ∀ n : ℕ, ∃ P ∈ S, lfe U (t n) P) :
in_combinatorial_closure u (convex_body_of_polytope V '' S)
tl := sorry