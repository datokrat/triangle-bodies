import convex

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma polytope_facial_gap {P : set V} (hP : is_polytope P) (u : V) :
∃ ε : ℝ, ε > 0 ∧ ∀ v ∈ metric.ball u ε,
normal_face P v ⊆ normal_face P u :=
begin
  admit,
end

lemma polytope_normal_face_nonempty {P : set V} (hP : is_polytope P) (u : V) :
(normal_face P u).nonempty := sorry

lemma polytope_convex {P : set V} (hP : is_polytope P) :
convex ℝ P := sorry