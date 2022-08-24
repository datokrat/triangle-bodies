import convex convex_body

open_locale topological_space

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def polytope (V : Type) [inner_product_space ℝ V] [finite_dimensional ℝ V] :=
{ P : set V // is_polytope P }

instance polytope.has_lift_t : has_lift_t (polytope V) (set V) :=
{
  lift := (coe : { P // is_polytope P } → set V)
}

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

lemma is_convex_body_of_is_polytope {P : set V} (hP : is_polytope P) :
is_convex_body P := sorry

def convex_body_of_polytope (P : polytope V) : convex_body V :=
⟨P.val, sorry⟩

lemma polytope.finite_faces (P : polytope V) : finite (faces P.val) :=
sorry


@[simp]
lemma normal_face_idem_poly
(P : polytope V) (u : V) :
normal_face (normal_face ↑P u) u = normal_face ↑P u :=
begin
  ext,
  simp only [mem_normal_face, ge_iff_le, and_imp, and_iff_left_iff_imp],
  intros xK hx y yK hy,
  exact hx y yK,
end

/- lemma approximate_with_polytopes (K : convex_body V) :
∃ P : ℕ → polytope V,
filter.tendsto (convex_body_of_polytope ∘ P) filter.at_top (𝓝 K) := sorry -/