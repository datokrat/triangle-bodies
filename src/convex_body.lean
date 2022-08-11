import convex linalg support_function
  linear_algebra.affine_space.affine_subspace

open_locale pointwise

def convex_body (V : Type)
[inner_product_space ℝ V] [finite_dimensional ℝ V] :=
{ K : set V // is_convex_body K }

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma nonempty_of_convex_body {K : convex_body V} : K.val.nonempty :=
K.property.2.2

lemma bounded_of_convex_body {K : convex_body V} : metric.bounded K.val :=
(metric.compact_iff_closed_bounded.mp K.property.2.1).2

lemma closed_of_convex_body {K : convex_body V} : is_closed K.val :=
(metric.compact_iff_closed_bounded.mp K.property.2.1).1

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
vector_span ℝ K.val

noncomputable instance has_dist_convex_body : has_dist (convex_body V) :=
{
  dist := λ K L, metric.Hausdorff_dist K.val L.val,
}

lemma edist_body_ne_top {K L : convex_body V} :
emetric.Hausdorff_edist K.val L.val ≠ ⊤ :=
begin
  apply metric.Hausdorff_edist_ne_top_of_nonempty_of_bounded,
  any_goals {apply nonempty_of_convex_body},
  any_goals {apply bounded_of_convex_body},
end

noncomputable instance pmetric_convex_body : pseudo_metric_space (convex_body V) :=
{
  to_has_dist := has_dist_convex_body,
  dist_self := λ K, metric.Hausdorff_dist_self_zero,
  dist_comm := λ K L, metric.Hausdorff_dist_comm,
  dist_triangle := λ K L M, metric.Hausdorff_dist_triangle edist_body_ne_top,
}

noncomputable instance metric_convex_body : metric_space (convex_body V) :=
{
  to_pseudo_metric_space := pmetric_convex_body,
  eq_of_dist_eq_zero :=
  begin
    intros K L hd,
    apply subtype.coe_inj.mp,
    rw [←subtype.val_eq_coe, ←subtype.val_eq_coe],
    refine (emetric.Hausdorff_edist_zero_iff_eq_of_closed _ _).mp _,
    any_goals {exact closed_of_convex_body},
    replace hd := congr_arg ennreal.of_real hd,
    simpa only [dist, metric.Hausdorff_dist, ennreal.of_real_zero, 
      ennreal.of_real_to_real edist_body_ne_top] using hd,
  end
}

lemma dist_body_eq_Hausdorff_edist
(K L: convex_body V) :
ennreal.of_real (dist K L) = emetric.Hausdorff_edist K.val L.val :=
begin
  simp only [dist, metric.Hausdorff_dist],
  rw [ennreal.of_real_to_real edist_body_ne_top],
end


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

