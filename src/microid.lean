import convex linalg support_function
  linear_algebra.affine_space.affine_subspace
  topology.continuous_function.bounded
  measure_theory.measure.measure_space

open_locale pointwise

def sphere (V : Type) [inner_product_space ℝ V] [finite_dimensional ℝ V] := (metric.sphere (0 : V) 1)

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def vertex_bounded_polytope (k : ℕ) (A : set V) :=
∃ S : set V, cardinal.mk S ≤ k ∧ S.nonempty ∧ A = convex_hull ℝ S

section microid

lemma convex_body_of_hull {S : set V}
(h : is_compact S) (hne : S.nonempty) :
is_convex_body (convex_hull ℝ S) := sorry

def hull_of_vertices {k : ℕ} (verts : fin k → V) :=
convex_hull ℝ (set.range verts)

lemma polytope_hull_of_vertices {k : ℕ} (verts : fin k → V) :
is_polytope (hull_of_vertices verts) := sorry

lemma convex_body_hull_of_vertices {k : ℕ} (verts : fin k → V) :
is_convex_body (convex_hull ℝ (set.range verts)) := sorry

noncomputable def vertices_to_support_function
(k : ℕ) (verts : fin k → V) : bounded_continuous_function (sphere V) ℝ := sorry
/- finite_support_function
  (convex_body_hull_of_vertices verts) -/

lemma vertices_to_support_function_continuous {k : ℕ} :
continuous
((vertices_to_support_function k) :
(fin k → V) → bounded_continuous_function (sphere V) ℝ) :=
begin
  admit,
end

-- baaaad
noncomputable instance x := borel (bounded_continuous_function (sphere V) ℝ)

def generating_measure :=
measure_theory.measure (bounded_continuous_function (sphere V) ℝ)



end microid

/- def is_microid (A : set V) :=
is_convex_body A ∧ ∃ k ∈ ℕ,  -/