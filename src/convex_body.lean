import convex linalg
  linear_algebra.affine_space.affine_subspace
  analysis.normed_space.hahn_banach.separation
  analysis.inner_product_space.dual

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

/- -- MOVETO convex.lean
lemma affine_image_convex {W : Type}
[inner_product_space ℝ W] [finite_dimensional ℝ W]
(f : V →ₗ[ℝ] W)
{A : set V}
(Acv : convex ℝ A) :
convex ℝ (f '' A) :=
begin

end -/

def proj_body
(E : submodule ℝ V)
(K : convex_body V) :
convex_body E :=
begin
  refine ⟨proj E '' K.val, _⟩,
  rcases K with ⟨Kset, Kcv, Kcp, Kne⟩,
  refine ⟨_, _, _⟩,
  {
    exact Kcv.linear_image (proj E),
  },
  {
    change is_compact (orthogonal_projection E '' Kset),
    exact Kcp.image (orthogonal_projection E).continuous,
  },
  {
    simpa only [set.nonempty_image_iff] using Kne,
  },
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

lemma edist_body_eq_Hausdorff_edist
(K L : convex_body V) :
edist K L = emetric.Hausdorff_edist K.val L.val :=
begin
  simp only [edist, pseudo_metric_space.edist,
    metric.Hausdorff_dist],
  convert ennreal.of_real_to_real _,
  {
    simp only [max_eq_left, ennreal.to_real_nonneg],
  },
  {
    apply edist_body_ne_top,
  },
end

lemma Hausdorff_edist_dist
{A B : set V} (h : emetric.Hausdorff_edist A B ≠ ⊤) :
emetric.Hausdorff_edist A B =
ennreal.of_real (metric.Hausdorff_dist A B) :=
begin
  simp only [metric.Hausdorff_dist],
  rw [ennreal.of_real_to_real h],
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
add_comm_monoid (convex_body V) :=
{
  add := λ K L, ⟨K.val + L.val, sum_convex_body K.prop L.prop⟩,
  add_assoc :=
  begin
    intros K L M,
    apply subtype.coe_injective,
    simp only [add_assoc, subtype.coe_mk], -- why does it work here but not for add_comm?
  end,
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

instance : has_lift_t (convex_body V) (set V) :=
{
  lift := (coe : { K // is_convex_body K } → set V)
}

lemma coe_zero_body_eq : (coe (0 : convex_body V) : set V) = ({0} : set V) :=
rfl

lemma convex_body.is_closed (K : convex_body V) : is_closed K.val :=
closed_of_convex_body

lemma convex_body.nonempty (K : convex_body V) : K.val.nonempty :=
nonempty_of_convex_body

noncomputable def convex_body.supp (K : convex_body V) (u : V) : ℝ :=
Sup (flip inner u '' K.val)

-- MOVETO linalg.lean
lemma inner_left_continuous (u : V) :
continuous (flip inner u : V → ℝ) :=
begin
  let f : V → V × V := λ v, (v, u),
  let g : V × V → ℝ := λ x, ⟪x.fst, x.snd⟫_ℝ,
  let h := g ∘ f,
  have gc : continuous g := continuous_inner,
  have hc : continuous h := by continuity,
  exact hc,
end

lemma convex_body.exists_inner_eq_supp (K : convex_body V) (u : V) :
∃ x : V, x ∈ K.val ∧ ⟪x, u⟫_ℝ = K.supp u :=
begin
  rcases K with ⟨Kset, Kcv, Kcp, Kne⟩,
  have := (Kcp.image (inner_left_continuous u)).Sup_mem (set.nonempty.image _ Kne),
  simpa only [set.mem_image] using this,
end

lemma convex_body.mem_normal_face_of_inner_eq_supp (K : convex_body V) (u : V)
{x : V} (xK : x ∈ K.val) (hx : ⟪x, u⟫_ℝ = K.supp u) :
x ∈ normal_face K.val u :=
begin
  rw [mem_normal_face],
  refine ⟨xK, _⟩,
  intros y yK,
  have : ⟪y, u⟫_ℝ ∈ (flip inner u) '' K.val,
  {
    rw [set.mem_image],
    exact ⟨y, yK, rfl⟩,
  },
  rcases K with ⟨Kset, Kcv, Kcp, Kne⟩,
  refine le_trans (le_cSup (Kcp.image (inner_left_continuous u)).bdd_above this) _,
  rw [hx],
  refl,
end

lemma convex_body.normal_face_supp (K : convex_body V) (u : V) :
normal_face K.val u = { x : V | x ∈ K.val ∧ ⟪x, u⟫_ℝ = K.supp u } :=
begin
  ext, split,
  {
    intro h,
    refine ⟨_, _⟩,
    {
      exact normal_face_subset h,
    },
    {
      rcases K.exists_inner_eq_supp u with
        ⟨y, yK, hy⟩,
      rw [←hy],
      apply inner_eq_of_mem_normal_face h,
      exact K.mem_normal_face_of_inner_eq_supp u yK hy,
    },
  },
  {
    rintro ⟨xK, hx⟩,
    exact K.mem_normal_face_of_inner_eq_supp u xK hx,
  },
end

def convex_body.normal_face_nonempty (K : convex_body V) (u : V) :
(normal_face K.val u).nonempty :=
begin
  rcases K.exists_inner_eq_supp u with ⟨x, xK, hx⟩,
  refine ⟨x, _⟩,
  exact K.mem_normal_face_of_inner_eq_supp u xK hx,
end

def convex_body.normal_face (K : convex_body V) (u : V) : convex_body V :=
begin
  refine ⟨normal_face K.val u, _⟩,
  rcases K with ⟨Kset, Kcv, Kcp, Kne⟩,
  have isface : is_face Kset (normal_face Kset u) :=
    normal_face_is_face Kcv _,
  refine ⟨_, _, _⟩,
  {
    exact face_convex isface,
  },
  {
    apply compact_of_is_closed_subset Kcp,
    {
      exact face_closed Kcp.is_closed isface,
    },
    {
      exact normal_face_subset,
    },
  },
  {
    exact convex_body.normal_face_nonempty _ _,
  },
end

lemma convex_body.supp_exists_mem_face (K : convex_body V) (u : V) :
∃ x ∈ normal_face K.val u, ⟪x, u⟫_ℝ = K.supp u :=
begin
  rcases K.exists_inner_eq_supp u with ⟨x, xK, hx⟩,
  refine ⟨x, _, hx⟩,
  apply K.mem_normal_face_of_inner_eq_supp u xK hx,
end

lemma convex_body.subset_of_supp_le (K L : convex_body V) :
K.supp ≤ L.supp → K.val ⊆ L.val :=
begin
  intros h x xK,
  rw [pi.le_def] at h,
  by_contradiction hc,
  let L' := L,
  rcases L with ⟨Lset, Lcv, Lcp, Lne⟩,
  rcases geometric_hahn_banach_point_closed Lcv Lcp.is_closed hc
    with ⟨f, ν, h₁, h₂⟩,
  let g := -f,
  let u := (inner_product_space.to_dual ℝ _).inv_fun g,
  rcases L'.supp_exists_mem_face u with ⟨y, fy, hy⟩,
  rw [real_inner_comm, ←inner_product_space.to_dual_apply] at hy,
  simp only [u] at hy,
  simp only [linear_equiv.inv_fun_eq_symm, linear_isometry_equiv.to_linear_equiv_symm, linear_isometry_equiv.coe_to_linear_equiv,
  linear_isometry_equiv.apply_symm_apply] at hy,
  change g y = L'.supp u at hy,
  replace h₂ := h₂ y (normal_face_subset fy),
  --replace hy := congr_arg has_neg.neg hy,
  --simp only [continuous_linear_map.neg_apply, neg_neg] at hy,
  rw [←neg_lt_neg_iff] at h₂,
  simp only [continuous_linear_map.neg_apply] at hy,
  simp only [hy, L'] at h₂,
  replace h₂ := lt_of_le_of_lt (h _) h₂,
  rcases K.supp_exists_mem_face u with ⟨z, fz, hz⟩,
  rw [←hz] at h₂,
  rw [mem_normal_face] at fz,
  replace fz := fz.2 x xK,
  have : f x = -⟪x, u⟫_ℝ,
  {
    simp only [u, linear_equiv.inv_fun_eq_symm, linear_isometry_equiv.to_linear_equiv_symm,
  linear_isometry_equiv.coe_to_linear_equiv, map_neg, inner_neg_right, neg_neg],
    rw [real_inner_comm, inner_product_space.to_dual_symm_apply],
  },
  rw [this] at h₁,
  linarith,
end

lemma convex_body.supp_injective (K L : convex_body V) :
K.supp = L.supp → K = L :=
begin
  intro h,
  apply subtype.coe_injective,
  apply subset_antisymm,
  all_goals {
    refine convex_body.subset_of_supp_le _ _ _,
    rw [h],
    exact le_refl _,
  },
end

lemma convex_body.proj_supp (K : convex_body V) (E : submodule ℝ V) :
(proj_body E K).supp = λ u, K.supp u :=
begin
  funext u,
  rcases K.supp_exists_mem_face u with ⟨x, fx, hx⟩,
  rcases (proj_body E K).supp_exists_mem_face u with ⟨y, fy, hy⟩,
  rcases normal_face_subset fy with ⟨z, zK, rfl⟩,
  rw [←hx, ←hy],
  apply le_antisymm,
  {
    rw [submodule.coe_inner, inner_orthogonal_eq_inner],
    rw [mem_normal_face] at fx,
    exact fx.2 _ zK,
  },
  {
    rw [←inner_orthogonal_eq_inner],
    exact fy.2 _ ⟨x, normal_face_subset fx, rfl⟩,
  },
end

/- noncomputable def convex_body_to_positive_homogeneous : convex_body V →+ (V → ℝ) :=
{
  to_fun := λ K, finite_support_function K.prop,
  map_zero' :=
  begin
    simp only [finite_support_function, support_function, coe_zero_body_eq, supr_unique, set.default_coe_singleton, inner_zero_left,
  ereal.coe_zero, ereal.to_real_zero],
  funext,
  simp only [pi.zero_apply],
  end,
  map_add' :=
  begin
    simp only [finite_support_function, support_function],
    intros K L,
    funext,
    simp only [subtype.val_eq_coe, pi.add_apply],
    sorry,
  end
} -/

