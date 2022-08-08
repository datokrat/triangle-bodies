import convex convex_body multiset brunn_minkowski
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

abbreviation microid_generator_space (k : ℕ) := metric.ball (0 : fin k → V) 1

noncomputable instance borel_measurable_space_microid_generator_space (k : ℕ) :=
borel
(microid_generator_space V k)

instance borel_space_microid_generator_space (k : ℕ) :
borel_space (microid_generator_space V k) :=
⟨rfl⟩

instance proper_space_microid_generator_space (k : ℕ) :
proper_space (microid_generator_space V k) := sorry

def function_of_generator {k : ℕ}
(G : microid_generator_space V k) : fin k → V := G.val

abbreviation microid_measure (k : ℕ) :=
measure_theory.finite_measure (microid_generator_space V k)

end types

section bla

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

-- bad edge case: k = 0
def polytope_of_microid_generator {k : ℕ} (G : microid_generator_space V k) :
polytope V := sorry

def body_of_microid_generator {k : ℕ} (G : microid_generator_space V k) :
convex_body V := sorry

def microid_of_measure {k : ℕ} (μ : microid_measure V k) :
convex_body V := sorry


-- only used for c > 0
def cuspy_cone (x : V) (u : V) (c : ℝ) :=
{ y : V | ⟪x - y, u⟫_ℝ ≥ c * ∥ y - x ∥ }

def is_cuspy (A : set V) (u : V) (c : ℝ) :=
∃ x ∈ A, A ⊆ cuspy_cone x u c

lemma cuspy_iff_TS_zero (K : convex_body V) (u : V) :
TS K.val = 0 ↔ ∃ c > 0, is_cuspy K.val u c := sorry

lemma cuspy_generators_of_cuspy {k : ℕ} {μ : microid_measure V k} {u : V} {c > 0}
(h : is_cuspy (microid_of_measure μ).val u c) :
∀ G ∈ msupport μ, is_cuspy (polytope_of_microid_generator G).val u c := sorry

def polytope_to_convex_body
(P : polytope V) : convex_body V :=
⟨P.val, sorry⟩

def is_default_polytope {k : ℕ} (μ : microid_measure V k) (u : metric.sphere (0 : V) 1)
(P : microid_generator_space V k) :=
vector_span ℝ (polytope_of_microid_generator P).val ≤ vector_orth u.val ∧
TS (polytope_of_microid_generator P).val u ≠ 0 ∧
(∀ C : multiset (convex_body V),
C.card = dim V - 2 →
u ∈ msupport (bm.area ((polytope_to_convex_body (polytope_of_microid_generator P)) ::ₘ C)) →
u ∈ msupport (bm.area (microid_of_measure μ ::ₘ C)))

-- uses pruning lemma
lemma exists_default_polytope_of_TS_nonzero {k : ℕ} {μ : microid_measure V k}
(h : TS (microid_of_measure μ).val ≠ 0) (u : metric.sphere (0 : V) 1) :
∃ P : microid_generator_space V k, is_default_polytope μ u P := sorry

end bla