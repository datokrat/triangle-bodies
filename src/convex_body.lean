import convex linalg support_function
  linear_algebra.affine_space.affine_subspace

open_locale pointwise

def convex_body (V : Type)
[inner_product_space ℝ V] [finite_dimensional ℝ V] :=
{ K : set V // is_convex_body K }

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def convex_body_subset (E : submodule ℝ V) (K : convex_body V) : Prop :=
K.val ⊆ (E : set V)

def convex_body_amb (E : submodule ℝ V) :=
{ K : convex_body V // K.val ⊆ (E : set V)}

def extend_amb {E F : submodule ℝ V} (h : E ≤ F)
(K : convex_body_amb E) : convex_body_amb F
:= ⟨K.val, begin
      dsimp only [convex_body_amb], -- simp doesn't work?
      refine subset_trans K.prop h,
    end⟩

def restrict_amb {E F : submodule ℝ V} (h : E ≤ F)
(K : convex_body_amb F)
(hE : K.val.val ⊆ (E : set V)) : convex_body_amb E :=
⟨K.val, hE⟩

def restrict_amb_coll {E F : submodule ℝ V} (h : E ≤ F)
(C : multiset (convex_body_amb F))
(hE : ∀ K : convex_body_amb F, K ∈ C → K.val.val ⊆ (E : set V)) :
multiset (convex_body_amb E) := sorry -- Problem: Map does not pass info that mem C

def noamb {E : submodule ℝ V}
(K : convex_body_amb E) : convex_body V := K.val

def extend_amb_coll {E F : submodule ℝ V} (h : E ≤ F)
(C : multiset (convex_body_amb E)) : multiset (convex_body_amb F) :=
C.map (extend_amb h)

def proj_amb_coll {E : submodule ℝ V}
(F : submodule ℝ V)
(C : multiset (convex_body_amb E)) :
multiset (convex_body_amb (E.map (proj F))) := sorry

def proj_body
(E : submodule ℝ V)
(K : convex_body V) :
convex_body E :=
begin
  refine ⟨proj E '' K.val, _⟩,
  admit,
end

def proj_coll
(E : submodule ℝ V)
(C : multiset (convex_body V)) :
multiset (convex_body E) :=
C.map (proj_body E)

/- noncomputable def span_of_convex_body_amb {E : submodule ℝ V}
(K : convex_body_amb E) : submodule ℝ V :=
submodule.span ℝ K.val.val -/

noncomputable def span_of_convex_body
(K : convex_body V) : submodule ℝ V :=
submodule.span ℝ K.val

instance pmetric_convex_body : pseudo_metric_space (convex_body V) :=
sorry

instance metric_convex_body : metric_space (convex_body V) :=
sorry


lemma compact_convex_body {K : set V} (Kcb : is_convex_body K) :
is_compact K := Kcb.2.1

lemma nonempty_convex_body {K : set V} (Kcb : is_convex_body K) :
K.nonempty := Kcb.2.2

lemma zero_convex_body : is_convex_body ({0} : set V) :=
begin
  simp only [is_convex_body],
  repeat {split},
  {apply convex_singleton},
  {apply is_compact_singleton},
end

lemma sum_convex_body {K L : set V}
(Kbd : is_convex_body K) (Lbd : is_convex_body L) :
is_convex_body (K + L) :=
begin
  simp only [is_convex_body],
  refine ⟨_, _, _⟩,
  {
    apply convex_sum,
    all_goals {apply convex_convex_body, assumption},
  },
  {
    rw [←set.add_image_prod],
    apply is_compact.image_of_continuous_on,
    {
      apply is_compact.prod,
      all_goals {apply compact_convex_body, assumption},
    },
    {
      apply continuous.continuous_on,
      exact continuous_add,
    },
  },
  {
    apply set.add_nonempty.mpr,
    split,
    all_goals {apply nonempty_convex_body, assumption},
  },
end

instance convex_body_add_monoid :
add_cancel_comm_monoid (convex_body V) :=
{
  add := λ K L, ⟨K.val + L.val, sum_convex_body K.prop L.prop⟩,
  add_assoc :=
  begin
    intros K L M,
    apply subtype.coe_injective,
    simp only [add_assoc, subtype.coe_mk], -- why does it work here but not for add_comm?
  end,
  add_left_cancel := sorry,
  add_comm :=
  begin
    intros K L,
    apply subtype.coe_injective,
    change K.val + L.val = L.val + K.val, -- ugly
    simp only [add_comm],
  end,
  zero := ⟨{0}, zero_convex_body⟩,
  zero_add :=
  begin
    intro K,
    apply subtype.coe_injective,
    change 0 + K.val = K.val,
    simp only [zero_add],
  end,
  add_zero :=
  begin
    intro K,
    apply subtype.coe_injective,
    change K.val + 0 = K.val,
    simp only [add_zero],
  end,
}

lemma coe_zero_body_eq : ((0 : convex_body V) : set V) = ({0} : set V) :=
rfl

noncomputable def convex_body_to_positive_homogeneous : convex_body V →+ (V → ℝ) :=
{
  to_fun := λ K, finite_support_function K.prop,
  map_zero' :=
  begin
    simp only [finite_support_function, support_function, coe_zero_body_eq, supr_unique, set.default_coe_singleton, inner_zero_left,
  ereal.coe_zero, ereal.to_real_zero],
  funext,
  trivial,
  end,
  map_add' :=
  begin
    simp only [finite_support_function, support_function],
    intros K L,
    funext,
    simp only [subtype.val_eq_coe, pi.add_apply],
    sorry,
  end
}

