import convex face linalg
  linear_algebra.affine_space.affine_subspace
  analysis.normed_space.hahn_banach.separation
  analysis.inner_product_space.dual

open_locale pointwise
open_locale nnreal

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

@[simp]
lemma convex_body.coe_add
{K L : convex_body V} :
(↑(K + L) : set V) = ↑K + ↑L := rfl

@[simp]
lemma convex_body.coe_zero :
(↑(0 : convex_body V) : set V) = (0 : set V) := rfl

instance convex_body_has_smul : has_smul ℝ≥0 (convex_body V) :=
{
  smul :=
  begin
    intros c K,
    refine ⟨c • K.val, _⟩,
    obtain ⟨Kcv, Kcp, Kne⟩ := K.property,
    refine ⟨_, _, _⟩,
    {
      apply Kcv.smul,
    },
    {
      simp only [has_smul.smul],
      simp only [has_smul.comp.smul, nnreal.coe_to_real_hom],
      refine Kcp.image _,
      by continuity,
    },
    {
      apply Kne.smul_set,
    },
  end,
}

@[simp]
lemma convex_body.coe_smul
{c : ℝ≥0} {K : convex_body V} :
(↑(c • K) : set V) = c • ↑K := rfl

instance convex_body_mul_action : mul_action ℝ≥0 (convex_body V) :=
{
  to_has_smul := convex_body_has_smul,
  one_smul :=
  begin
    intro K,
    simp only [has_smul.smul, subtype.val_eq_coe, has_smul.comp.smul, nnreal.coe_to_real_hom, nonneg.coe_one, one_smul,
    set.image_id', subtype.coe_eta],
  end,
  mul_smul :=
  begin
    intros c d K,
    simp only [has_smul.smul],
    simp only [has_smul.comp.smul, nnreal.coe_to_real_hom, nonneg.coe_mul, set.image_smul, subtype.val_eq_coe, subtype.mk_eq_mk],
    simp only [smul_smul],
  end
}

instance convex_body_distrib_mul_action : distrib_mul_action ℝ≥0 (convex_body V) :=
{
  to_mul_action := convex_body_mul_action,
  smul_add :=
  begin
    intros c K L,
    simp only [has_smul.smul],
    simp only [has_smul.comp.smul, nnreal.coe_to_real_hom, set.image_smul, subtype.val_eq_coe, convex_body.coe_add, smul_add],
    simp only [subtype.ext_iff],
    simp only [convex_body.coe_add, subtype.coe_mk],
  end,
  smul_zero :=
  begin
    intros c,
    simp only [subtype.ext_iff, convex_body.coe_smul, convex_body.coe_zero, smul_zero],
  end
}

instance convex_body_module : module ℝ≥0 (convex_body V) :=
{
  to_distrib_mul_action := convex_body_distrib_mul_action,
  add_smul :=
  begin
    intros c d K,
    simp only [subtype.ext_iff, convex_body.coe_smul, convex_body.coe_add],
    simp only [has_smul.smul],
    ext,
    simp only [set.mem_image, set.mem_add],
    split,
    {
      rintro ⟨x, xK, rfl⟩,
      refine ⟨c • x, d • x, ⟨x, _, rfl⟩, ⟨x, _, rfl⟩, _⟩,
      {assumption}, {assumption},
      simp only [add_smul, has_smul.comp.smul, nnreal.coe_to_real_hom, nonneg.coe_add],
      refl,
    },
    {
      rintro ⟨cx, cy, ⟨x, hx, rfl⟩, ⟨x', hx', rfl⟩, rfl⟩,
      by_cases h : c = 0 ∧ d = 0,
      {
        simp only [h.1, h.2, add_zero, has_smul.comp.smul, nnreal.coe_to_real_hom, nonneg.coe_zero, zero_smul,
        eq_self_iff_true, and_true],
        exact ⟨x, hx⟩,
      },
      {
        have : c + d > 0,
        {
          by_contra hc,
          push_neg at hc,
          rw [←bot_eq_zero, le_bot_iff, bot_eq_zero] at hc,
          simp only [add_eq_zero_iff] at hc,
          exact h hc,
        },
        replace : (↑c : ℝ) + ↑d > 0 := this,
        simp only [has_smul.comp.smul, nnreal.coe_to_real_hom, nonneg.coe_add],
        refine ⟨(c / (c + d)) • x + (d / (c + d)) • x', _⟩,
        have ha : (c + d) • (c / (c + d)) • x = x,
        {
          admit,
        },
        have hb : (c + d) • (d / (c + d)) • x' = x',
        {
          admit,
        },
        refine ⟨_, _⟩,
        {
          apply K.property.1 hx hx',
          any_goals {apply nnreal.coe_nonneg},
          rw [←map_add],
          simp only [nnreal.coe_to_real_hom, nonneg.coe_add, nonneg.coe_div],
          rw [←add_div, div_self (ne_of_gt this)],
        },
        {
          rw [smul_add],
          simp only [nnreal.smul_def, nonneg.coe_div, nonneg.coe_add],
          simp only [smul_smul, mul_div_cancel' _ (ne_of_gt this)],
        },
      },
    },
  end,
  zero_smul :=
  begin
    intro K,
    apply subtype.coe_injective,
    simp only [convex_body.coe_smul, convex_body.coe_zero],
    rw [←subtype.val_eq_coe, set.zero_smul_set K.property.2.2],
  end
}

instance convex_body_has_singleton : has_singleton V (convex_body V) :=
{
  singleton :=
  begin
    intro x,
    refine ⟨{x}, _, _, _⟩,
    {
      exact convex_singleton x,
    },
    {
      exact is_compact_singleton,
    },
    {
      exact set.singleton_nonempty x,
    },
  end
}

@[simp]
lemma convex_body.coe_singleton
(x : V) :
(↑({x} : convex_body V) : set V) = {x} := rfl

lemma coe_zero_body_eq : (coe (0 : convex_body V) : set V) = ({0} : set V) :=
rfl

lemma convex_body.is_closed (K : convex_body V) : is_closed K.val :=
closed_of_convex_body

lemma convex_body.nonempty (K : convex_body V) : K.val.nonempty :=
nonempty_of_convex_body

noncomputable def convex_body.supp (K : convex_body V) (u : V) : ℝ :=
Sup (flip inner u '' K.val)

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

lemma convex_body.inner_le_supp (K : convex_body V) {u : V} {x : V}
(xK : x ∈ K.val) :
⟪x, u⟫_ℝ ≤ K.supp u :=
begin
  obtain ⟨y, yKu, ye⟩ := K.supp_exists_mem_face u,
  rw [←ye],
  rw [mem_normal_face] at yKu,
  exact yKu.2 x xK,
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

@[simp]
lemma normal_face_normalize
(K : convex_body V) (u : V) :
↑(K.normal_face u) = normal_face ↑K u :=
begin
  simp only [convex_body.normal_face, subtype.val_eq_coe, subtype.coe_mk],
end

@[simp]
lemma normal_face_add
(K L : convex_body V) (u : V) :
(K + L).normal_face u = K.normal_face u + L.normal_face u :=
begin
  ext,
  simp only [convex_body.normal_face],
  simp only [subtype.val_eq_coe, subtype.coe_mk, mem_normal_face],
  split,
  {
    simp only [and_imp],
    rintro ⟨y, z, hy, hz, rfl⟩ h,
    refine ⟨y, z, _, _, rfl⟩,
    {
      rw [subtype.val_eq_coe, subtype.coe_mk, mem_normal_face],
      refine ⟨by assumption, _⟩,
      intros w hw,
      have := h (w + z) ⟨w, z, hw, hz, rfl⟩,
      simpa only [inner_add_left, ge_iff_le, add_le_add_iff_right] using this,
    },
    {
      rw [subtype.val_eq_coe, subtype.coe_mk, mem_normal_face],
      refine ⟨by assumption, _⟩,
      intros w hw,
      have := h (y + w) ⟨y, w, hy, hw, rfl⟩,
      simpa only [inner_add_left, ge_iff_le, add_le_add_iff_left] using this,
    },
  },
  {
    rintro ⟨y, z, hy, hz, rfl⟩,
    simp only [mem_normal_face] at hy hz,
    refine ⟨⟨y, z, hy.1, hz.1, rfl⟩, _⟩,
    rintro - ⟨a, b, ha, hb, rfl⟩,
    simp only [inner_add_left],
    exact add_le_add (hy.2 a ha) (hz.2 b hb),
  },
end

@[simp]
lemma normal_face_add'
(K L : convex_body V) (u : V) :
normal_face ↑(K + L) u = normal_face ↑K u + normal_face ↑L u :=
begin
  have := normal_face_add K L u,
  replace this := congr_arg (coe : convex_body V → set V) this,
  exact this,
end

@[simp]
lemma normal_face_idem'
(K : convex_body V) (u : V) :
normal_face (normal_face ↑K u) u = normal_face ↑K u :=
begin
  ext,
  simp only [mem_normal_face, ge_iff_le, and_imp, and_iff_left_iff_imp],
  intros xK hx y yK hy,
  exact hx y yK,
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

