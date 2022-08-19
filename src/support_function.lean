import touching_cone convex
  data.real.ereal

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

noncomputable def support_function (A : set V) (u : V) : ereal :=
@supr ereal _ _ (λ a : A, (⟪a.1, u⟫_ℝ : ereal))

lemma normal_face_support_function (A : set V) (u : V) :
normal_face A u = { x ∈ A | (⟪x, u⟫_ℝ : ereal) = support_function A u } :=
begin
  apply le_antisymm,
  {
    rintro x hx,
    simp only [set.mem_sep_eq],
    simp only [mem_normal_face] at hx,
    split,
    {tauto},
    simp only [support_function],
    apply eq.symm ∘ is_lub.supr_eq,
    apply is_greatest.is_lub,
    split,
    {
      simp only [
        set.mem_range, ereal.coe_eq_coe_iff,
        set_coe.exists, exists_prop],
      refine ⟨x, _⟩,
      tauto,
    },
    {
      simp [mem_upper_bounds],
      tauto,
    }
  },
  {
    rintro x hx,
    simp only [mem_normal_face],
    simp only [set.mem_sep_eq] at hx,
    split,
    {tauto},
    rintro y hy,
    simp only [support_function] at hx,
    apply ereal.coe_le_coe_iff.mp,
    simp only [hx.2],
    rw [show y = (⟨y, hy⟩ : A).val, by refl],
    have := le_supr (λ x : A, (⟪x.val, u⟫_ℝ : ereal)),
    simp only [subtype.val_eq_coe, set_coe.forall, subtype.coe_mk] at this,
    apply this,
    assumption,
  }
end

noncomputable def finite_support_function {A : set V} 
(h : is_convex_body A) : V → ℝ :=
λ u, supr (λ a : A, ⟪a.1, u⟫_ℝ)

lemma support_function_finite {A : set V}
(Abd : is_convex_body A) (u : V) :
support_function A u = (finite_support_function Abd u : ereal) := sorry

def pos_homogeneous (f : V → ℝ) :=
∀ v : V, ∀ a : ℝ, a ≥ 0 → f (a • v) = a * (f v)

