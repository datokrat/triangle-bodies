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

lemma microid_supp_locally_linear_of_generators {k : ℕ}
(U : set V)
(μ : microid_measure V k)
(h : ∀ G ∈ msupport μ,
supp_locally_linear U (body_of_microid_generator G)) :
supp_locally_linear U (microid_of_measure μ) :=
sorry

lemma normal_face_singleton_iff_locally_linear_with
{U : set V} (oU : is_open U)
{K : convex_body V}
{x : V} :
supp_locally_linear_with U K x ↔  
∀ u ∈ U, (K.normal_face u).val = {x} := sorry

lemma normal_face_singleton_iff_locally_linear
{U : set V} (oU : is_open U)
{K : convex_body V} :
supp_locally_linear U K ↔  
∃ x : V, ∀ u ∈ U, (K.normal_face u).val = {x} := sorry