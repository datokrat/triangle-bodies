import convex relint

open_locale pointwise

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

lemma inner_eq_of_mem_normal_face {A : set V} {u x y : V}
(hx : x ∈ normal_face A u) (hy : y ∈ normal_face A u) :
⟪x, u⟫_ℝ = ⟪y, u⟫_ℝ :=
begin
  rw [mem_normal_face] at hx hy,
  apply le_antisymm,
  all_goals {tauto},
end

lemma summands_eq_of_summands_le_of_sum_ge
{a a' b b' : ℝ} : a ≤ a' → b ≤ b' → a + b ≥ a' + b' → a = a' ∧ b = b' :=
begin
  intros ha hb hab,
  split,
  {
    apply le_antisymm ha,
    rw [ge_iff_le, ←le_sub_iff_add_le] at hab,
    refine le_trans hab _,
    simp only [tsub_le_iff_right, add_le_add_iff_left],
    exact hb,
  },
  {
    apply le_antisymm hb,
    rw [ge_iff_le, ←le_sub_iff_add_le'] at hab,
    refine le_trans hab _,
    rw [add_sub_right_comm],
    simp only [add_le_iff_nonpos_left, sub_nonpos],
    exact ha,
  },
end

lemma eq_of_le_of_combo_ge
{ca a a' cb b b' : ℝ} :
ca > 0 → cb > 0 → a ≤ a' → b ≤ b' → ca • a + cb • b ≥ ca • a' + cb • b' → a = a' ∧ b = b' :=
begin
  intros hca hcb ha hb hab,
  suffices hs : ca • a = ca • a' ∧ cb • b = cb • b',
  {
    exact ⟨
      eq_of_smul_eq_smul_of_pos_of_le hs.1 hca ha,
      eq_of_smul_eq_smul_of_pos_of_le hs.2 hcb hb⟩,
  },
  apply summands_eq_of_summands_le_of_sum_ge,
  {
    exact smul_le_smul_of_nonneg ha (le_of_lt hca),
  },
  {
    exact smul_le_smul_of_nonneg hb (le_of_lt hcb),
  },
  {
    exact hab,
  },
end

lemma eq_of_le_of_combo_ge'
{ca a cb b c : ℝ} :
ca > 0 → cb > 0 → ca + cb = 1 → a ≤ c → b ≤ c → ca • a + cb • b ≥ c → a = c ∧ b = c :=
begin
  intros hca hcb hcab ha hb hab,
  have := eq_of_le_of_combo_ge hca hcb ha hb,
  simp only [←add_smul, hcab, one_smul] at this,
  exact this hab,
end

lemma ge_of_le_of_combo_ge'
{ca a cb b c : ℝ} :
ca > 0 → cb > 0 → ca + cb = 1 → a ≤ c → b ≤ c → ca • a + cb • b ≥ c → a ≥ c ∧ b ≥ c :=
begin
  intros hca hcb hcab ha hb hab,
  have := eq_of_le_of_combo_ge' hca hcb hcab ha hb hab,
  rw [this.1, this.2],
  exact ⟨le_refl c, le_refl c⟩,
end

lemma normal_face_convex {A : set V} (h : convex ℝ A) :
∀ u : V, convex ℝ (normal_face A u) :=
begin
  intros u x y hx hy a b ann bnn hab,
  refine ⟨h (normal_face_subset hx) (normal_face_subset hy)
    ann bnn hab, _⟩,
  intros z zA,
  simp only [inner_add_left, inner_smul_left,
    is_R_or_C.conj_to_real],
  rw [mem_normal_face] at hx hy,
  refine le_trans _ (add_le_add
    (mul_le_mul_of_nonneg_left (hx.2 z zA) ann)
    (mul_le_mul_of_nonneg_left (hy.2 z zA) bnn)),
  rw [←add_mul, hab, one_mul],
end

lemma normal_face_is_face {A : set V} (h : convex ℝ A) :
∀ u : V, is_face A (normal_face A u) :=
begin
  intro u,
  simp only [is_face],
  refine ⟨normal_face_subset, normal_face_convex h u, _⟩,
  {
    intros x hx y hy hh,
    rcases hh with ⟨z, hz₁, hz₂⟩,
    rcases hz₁ with ⟨a, b, apos, bpos, hab, rfl⟩,
    suffices hs : x ∈ normal_face A u ∧ y ∈ normal_face A u,
    {
      rw [←convex_hull_pair],
      rw [convex.convex_hull_subset_iff (normal_face_convex h u)],
      simp only [set.insert_subset, set.singleton_subset_iff],
      exact hs,
    },
    {
      simp only [mem_normal_face] at hz₂ ⊢,
      rw [and_and_and_comm],
      refine ⟨⟨hx, hy⟩, _⟩,
      simp only [←forall_and_distrib, ←imp_and_distrib],
      intros z zA,
      suffices hs : ⟪x, u⟫_ℝ = ⟪a • x + b • y, u⟫_ℝ ∧ ⟪y, u⟫_ℝ = ⟪a • x + b • y, u⟫_ℝ,
      {
        rw [hs.1, hs.2, and_self],
        exact hz₂.2 z zA,
      },
      apply eq_of_le_of_combo_ge' apos bpos hab,
      {
        exact hz₂.2 x hx,
      },
      {
        exact hz₂.2 y hy,
      },
      {
        simp only [inner_add_left, inner_smul_left, is_R_or_C.conj_to_real] at hz₂,
        exact hz₂.2 _ hz₂.1,
      },
    },
  },
end

lemma set_own_face {A : set V} (Acv : convex ℝ A) : is_face A A :=
begin
  simp only [is_face],
  refine ⟨_, _, _⟩,
  {tauto},
  {assumption},
  {
    rintro x hx y hy ⟨z, ⟨hzs, hz⟩⟩ p hp,
    refine convex.segment_subset Acv hx hy hp,
  }
end

lemma mem_normal_face_iff_subset_halfspace (A : set V) (u : V) {x : V}
(xA : x ∈ A) :
x ∈ normal_face A u ↔ A ⊆ { w : V | ⟪w, u⟫_ℝ ≤ ⟪x, u⟫_ℝ } :=
begin
  rw [mem_normal_face],
  tauto,
end

lemma mem_normal_face_iff_subset_halfspace' (A : set V) (u : V) {x : V} :
x ∈ normal_face A u ↔ x ∈ A ∧ A ⊆ { w : V | ⟪w, u⟫_ℝ ≤ ⟪x, u⟫_ℝ } :=
begin
  rw [mem_normal_face],
  tauto,
end

lemma convex_halfspace_le' (u : V) (r : ℝ) :
convex ℝ { w : V | ⟪w, u⟫_ℝ ≤ r} :=
begin
  conv {
    congr,
    congr,
    funext,
    rw [real_inner_comm],
    simp only [←inner_product_space.to_dual_apply],
  },
  apply convex_halfspace_le,
  apply linear_map.is_linear,
end

lemma convex_hyperplane' (u : V) (r : ℝ) :
convex ℝ { w : V | ⟪w, u⟫_ℝ = r} :=
begin
  conv {
    congr,
    congr,
    funext,
    rw [real_inner_comm],
    simp only [←inner_product_space.to_dual_apply],
  },
  apply convex_hyperplane,
  apply linear_map.is_linear,
end

lemma normal_face_subset_normal_face_hull {A : set V} {u : V} :
normal_face A u ⊆ normal_face (convex_hull ℝ A) u :=
begin
  intros w,
  rw [mem_normal_face_iff_subset_halfspace',
  mem_normal_face_iff_subset_halfspace'],
  intro h,
  refine ⟨subset_convex_hull _ _ h.1, _⟩,
  rw [convex.convex_hull_subset_iff (convex_halfspace_le' u _)],
  exact h.2,
end

lemma normal_face_subset_hyperplane_of_mem {A : set V} {u : V} {x : V}
(hx : x ∈ normal_face A u) :
normal_face A u ⊆ { w : V | ⟪w, u⟫_ℝ = ⟪x, u⟫_ℝ } :=
begin
  intros y hy,
  exact inner_eq_of_mem_normal_face hy hx,
end

lemma inner_eq_of_mem_hull_normal_face {A : set V} {u : V} {x y : V}
(hx : x ∈ convex_hull ℝ (normal_face A u)) (hy : y ∈ convex_hull ℝ (normal_face A u)) :
⟪x, u⟫_ℝ = ⟪y, u⟫_ℝ :=
begin
  have : (convex_hull ℝ (normal_face A u)).nonempty := ⟨x, hx⟩,
  rw [convex_hull_nonempty_iff] at this,
  rcases this with ⟨z, hz⟩,
  have : convex_hull ℝ (normal_face A u) ⊆ { w : V | ⟪w, u⟫_ℝ = ⟪z, u⟫_ℝ },
  {
    rw [convex.convex_hull_subset_iff (convex_hyperplane' u _)],
    exact normal_face_subset_hyperplane_of_mem hz,
  },
  rw [mem_normal_face_iff_subset_halfspace'] at hz,
  replace hx := this hx,
  replace hy := this hy,
  simp only [set.mem_set_of] at hx hy,
  rw [hx, hy],
end

lemma mem_normal_face_iff_mem_hull_normal_face {A : set V} {u : V} {x : V}
(xA : x ∈ A) :
x ∈ normal_face A u ↔ x ∈ convex_hull ℝ (normal_face A u) :=
begin
  split,
  {
    intro h,
    exact subset_convex_hull _ _ h,
  },
  {
    rw [mem_normal_face_iff_subset_halfspace _ _ xA],
    intro hx,
    have : (convex_hull ℝ (normal_face A u)).nonempty := ⟨x, hx⟩,
    rw [convex_hull_nonempty_iff] at this,
    rcases this with ⟨z, hz⟩,
    have := inner_eq_of_mem_hull_normal_face hx (subset_convex_hull _ _ hz),
    intros a ha,
    rw [set.mem_set_of, this],
    rw [mem_normal_face] at hz,
    exact hz.2 _ ha,
  },
end

lemma normal_face_spanned_by_verts {S : set V} (u : V) :
normal_face (convex_hull ℝ S) u = convex_hull ℝ (normal_face S u) :=
begin
  let 𝓜 := { x ∈ convex_hull ℝ S | x ∈ normal_face (convex_hull ℝ S) u ↔ x ∈ convex_hull ℝ (normal_face S u) },
  suffices hs : 𝓜 = convex_hull ℝ S,
  {
    ext, split,
    {
      intro h,
      have : x ∈ convex_hull ℝ S := normal_face_subset h,
      rw [←hs, set.mem_sep_iff] at this,
      exact this.2.mp h,
    },
    {
      intro h,
      have : x ∈ convex_hull ℝ S := convex_hull_mono normal_face_subset h,
      rw [←hs, set.mem_sep_iff] at this,
      exact this.2.mpr h,
    },
  },
  apply subset_antisymm,
  {
    rintro x ⟨hx₁, hx₂⟩,
    exact hx₁,
  },
  {
    rw [convex.convex_hull_subset_iff],
    {
      intros x hx,
      refine ⟨subset_convex_hull _ _ hx, _⟩,
      simp only,
      rw [mem_normal_face_iff_subset_halfspace _ _ (subset_convex_hull _ _ hx)],
      rw [convex.convex_hull_subset_iff (convex_halfspace_le' u _)],
      rw [←mem_normal_face_iff_subset_halfspace _ _ hx],
      rw [←mem_normal_face_iff_mem_hull_normal_face hx],
    },
    {
      rw [convex_iff_open_segment_subset],
      intros x y hx hy z hz,
      simp only [set.mem_sep_eq] at hx hy,
      refine ⟨_, _⟩,
      {
        have := convex_convex_hull ℝ S,
        rw [convex_iff_open_segment_subset] at this,
        exact this hx.1 hy.1 hz,
      },
      {
        simp only, split,
        {
          intro hh,
          have := normal_face_is_face (convex_convex_hull ℝ S) u,
          rcases this with ⟨-, -, this⟩,
          replace := this x hx.1 y hy.1 ⟨z, hz, hh⟩,
          have xmem := this (left_mem_segment ℝ _ _),
          have ymem := this (right_mem_segment ℝ _ _),
          rw [hx.2] at xmem,
          rw [hy.2] at ymem,
          exact convex_iff_open_segment_subset.mp (convex_convex_hull _ _) xmem ymem hz,
        },
        {
          rw [mem_normal_face_iff_mem_hull_normal_face],
          {
            suffices hs : normal_face S u ⊆ normal_face (convex_hull ℝ S) u,
            {
              apply convex_hull_mono hs,
            },
            {
              exact normal_face_subset_normal_face_hull,
            },
          },
          {
            have : convex ℝ (convex_hull ℝ S) := convex_convex_hull ℝ S,
            rw [convex_iff_open_segment_subset] at this,
            exact this hx.1 hy.1 hz,
          },
        },
      },
    },
  },
end

--lemma face_body {A : set V} (u : V) (h : is_convex_body A) : is_convex_body (face A u) := sorry
--lemma face_polytope {A F : set V} (h : is_polytope A) (hf : is_face A F) : is_polytope F := sorry


lemma face_closed {A F : set V} (h : is_closed A) (hf : is_face A F) :
is_closed F :=
begin
  simp only [is_face] at hf,
  rw [closed_iff_segments_closable (face_convex hf)],
  intros x y hs,
  rcases open_segment_nonempty x y with ⟨z, hz⟩,
  replace h := segments_closable_of_closed h,
  have : segment ℝ x y ⊆ A,
  {
    refine h _ _ _,
    refine subset_trans hs _,
    exact hf.1,
  },
  have := hf.2.2 x (this (left_mem_segment ℝ _ _)) y (this (right_mem_segment ℝ _ _)),
  refine this ⟨z, hz, hs hz⟩,
end

-- lemma relopen_iff_open {A : set V} (hA : vector_span ℝ A = ⊤) :
-- is_relopen A ↔ is_open A := sorry

/- theorem cl_relint {A : set V} (h : convex ℝ A) :
is_closed A → closure (relint A) = A := sorry

theorem relint_cl {A : set V} (h : convex ℝ A) :
is_relopen A → relint (closure A) = A := sorry

theorem relint_affine_span {A : set V} (h : convex ℝ A) :
affine_span ℝ (relint A) = affine_span ℝ A := sorry

lemma relopen_of_inter_relopen {A B : set V} :
is_relopen A → is_relopen B → is_relopen (A ∩ B) := sorry

lemma relint_eq_relint_inter_relint {A B : set V}
(Acv : convex ℝ A) (BCv: convex ℝ B):
(relint A ∩ relint B).nonempty →
relint (A ∩ B) = relint A ∩ relint B := sorry -/

/- lemma relopen_subspace (E : submodule ℝ V) :
is_relopen (E : set V) := sorry

lemma relint_coe_invariant {E : submodule ℝ V}
(A : set E) : E.subtype '' (relint A) = relint (E.subtype '' A) := sorry
 -/


lemma face_inter {A F G : set V} (h : convex ℝ A)
(hF : is_face A F) (hG : is_face A G) :
is_face A (F ∩ G) :=
begin
  simp only [is_face],
  refine ⟨_, _, _⟩,
  {
    rintro x ⟨xF, -⟩,
    exact (face_subset hF) xF,
  },
  {
    exact convex.inter (face_convex hF) (face_convex hG),
  },
  {
    have aF := face_absorbs_segments hF,
    have aG := face_absorbs_segments hG,
    rintro x hx y hy ⟨z, ⟨hzs, hz⟩⟩ p hp,
    exact ⟨
      aF x hx y hy ⟨z, ⟨hzs, hz.1⟩⟩ hp, -- why omit p?
      aG x hx y hy ⟨z, ⟨hzs, hz.2⟩⟩ hp,
    ⟩,
  },
end

lemma face_sInter {A : set V} {M : set (set V)}
(Acv : convex ℝ A) (h : ∀ F ∈ M, is_face A F)
(ne : M.nonempty) :
is_face A (set.sInter M) :=
begin
  rcases ne with ⟨F, hF⟩,
  simp only [is_face],
  refine ⟨_, _, _⟩,
  {
    rintro x hx,
    exact (face_subset (h F hF)) (hx F hF),
  },
  {
    exact convex_sInter (λ G hG, face_convex (h G hG)),
  },
  {
    rintro x hx y hy ⟨z, ⟨hzs, hz⟩⟩ p hp,
    rintro G hG,
    exact face_absorbs_segments (h G hG) x hx y hy ⟨z, ⟨hzs, hz G hG⟩⟩ hp,
  },
end

def faces (A : set V) := { F : set V | is_face A F }

def faces_containing {A B : set V} (h : B ⊆ A) :=
{ F : set V | is_face A F ∧ B ⊆ F }

lemma face_subset' {A : set V} (F : faces A) :
↑F ⊆ A :=
begin
  apply face_subset,
  exact F.property,
end

def smallest_face_containing {A B : set V}
(Acv : convex ℝ A) (BA : B ⊆ A) : faces A :=
⟨
  set.sInter (faces_containing BA),
  face_sInter Acv (λ G hG, hG.1) ⟨A, ⟨set_own_face Acv, BA⟩⟩
⟩

lemma smallest_face_containing_contains {A B : set V}
(Acv : convex ℝ A) (BA : B ⊆ A) :
B ⊆ smallest_face_containing Acv BA :=
begin
  simp only [smallest_face_containing, faces_containing, subtype.coe_mk, set.subset_sInter_iff, set.mem_set_of_eq, and_imp,
  imp_self, implies_true_iff],
end

lemma smallest_face_containing_subset {A B F : set V}
(Acv : convex ℝ A) (hAF : is_face A F) (hBF : B ⊆ F) :
(smallest_face_containing Acv (subset_trans hBF hAF.1)).val ⊆ F :=
begin
  simp only [smallest_face_containing, faces_containing],
  apply set.sInter_subset_of_mem,
  exact ⟨hAF, hBF⟩,
end

def smallest_face_containing_point {A : set V}
(Acv : convex ℝ A) {x : V} (xA : x ∈ A) : faces A :=
smallest_face_containing Acv (set.singleton_subset_iff.mpr xA)

lemma smallest_face_containing_point_contains {A : set V} {x : V}
(Acv : convex ℝ A) (xA : x ∈ A) :
x ∈ (smallest_face_containing_point Acv xA).val :=
begin
  simp only [smallest_face_containing_point],
  apply smallest_face_containing_contains Acv,
  exact set.mem_singleton _,
end

lemma smallest_face_containing_point_subset {A F : set V} {x : V}
(Acv : convex ℝ A) (hAF : is_face A F) (xF : x ∈ F) :
(smallest_face_containing_point Acv (hAF.1 xF)).val ⊆ F :=
begin
  simp only [smallest_face_containing_point],
  refine smallest_face_containing_subset Acv hAF _,
  simpa only [set.singleton_subset_iff] using xF,
end

/- lemma point_in_proper_face_of_relbd {A : set V}
(Acv : convex ℝ A) {x : V} (hx : x ∈ relbd A ∩ A) :
(smallest_face_containing_point Acv hx.2 : set V) ⊂ A :=
begin
  admit,
end -/


lemma is_closed_halfspace (u : V) (c : ℝ) :
is_closed { v : V | ⟪v, u⟫_ℝ ≤ c } :=
begin
  have := inner_left_continuous u,
  rw [continuous_iff_is_closed] at this,
  exact this _ is_closed_Iic,
end

lemma exists_supporting_halfspace' {A : set V}
(Acv : convex ℝ A) (Atop : vector_span ℝ A = ⊤) {x : V}
(h : x ∈ frontier A ∩ A) :
∃ u : V, u ≠ 0 ∧ A ⊆ { v : V | ⟪v, u⟫_ℝ ≤ ⟪x, u⟫_ℝ } :=
begin
  have xniA : x ∉ interior A := h.1.2,
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point
    (interior_convex Acv) is_open_interior xniA,
  simp only [←inner_product_space.to_dual_symm_apply'] at hf,
  refine ⟨(inner_product_space.to_dual ℝ V).symm f, _, _⟩,
  {
    obtain ⟨y, hy⟩ : (interior A).nonempty,
    {
      rw [←relint_eq_int Atop],
      exact relint_nonempty Acv ⟨x, h.2⟩,
    },
    intro hc,
    simp only [hc, inner_zero_right] at hf,
    have := hf y hy,
    linarith,
  },
  {
    refine subset_trans subset_closure _,
    rw [←cl_relint_eq_cl Acv, relint_eq_int Atop,
      ←closure_eq_iff_is_closed.mpr (is_closed_halfspace _ _)],
    apply closure_mono,
    intros a ha,
    exact le_of_lt (hf a ha),
    apply_instance,
  },
end

lemma exists_supporting_halfspace {A : set V}
(Acv : convex ℝ A) {x : V}
(h : x ∈ relbd A ∩ A) :
∃ u : V, x ∈ normal_face A u ∧ normal_face A u ⊂ A
:=
begin
  let E := vector_span ℝ A,
  let A' : set E := coe ⁻¹' (A - {x}),
  have A'cv : convex ℝ A',
  {
    intros y z hy hz a b hnn bnn hab,
    simp only [set.sub_singleton, set.mem_preimage, set.mem_image] at hy hz ⊢,
    rcases hz with ⟨z, zA, hz⟩,
    rcases hy with ⟨y, yA, hy⟩,
    refine ⟨a • y + b • z, _, _⟩,
    {
      apply Acv,
      all_goals {assumption},
    },
    {
      simp only [←hy, ←hz, submodule.coe_add,
      submodule.coe_smul_of_tower, smul_sub,
      sub_add_sub_comm, ←add_smul, hab, one_smul],
    },
  },
  have A'top : vector_span ℝ A' = ⊤,
  {
    rw [submodule.eq_top_iff'],
    simp only [←set_like.mem_coe],
    suffices hs : (set.univ : set E) ⊆ vector_span ℝ A',
    {
      rintro e,
      exact hs (set.mem_univ _),
    },
    --simp only [E] at eE,
    --simp only [vector_span] at eE ⊢,
    suffices hs' : ∀ e : V, e ∈ vector_span ℝ A → ∀ h : e ∈ vector_span ℝ A, (⟨e, h⟩ : vector_span ℝ A) ∈ vector_span ℝ A',
    {
      rintro ⟨e, eE⟩ -,
      exact hs' e eE eE,
    },
    intros e eE,
    apply submodule.span_induction eE,
    {
      rintro - ⟨a, b, ha, hb, rfl⟩ eE',
      apply submodule.subset_span,
      refine ⟨⟨a - x, _⟩, ⟨b - x, _⟩, _, _, _⟩,
      {
        apply submodule.subset_span,
        exact ⟨a, x, ha, h.2, rfl⟩,
      },
      {
        apply submodule.subset_span,
        exact ⟨b, x, hb, h.2, rfl⟩,
      },
      any_goals {
        simp only [set.mem_preimage, subtype.coe_mk, set.sub_singleton, set.mem_image, sub_left_inj, exists_eq_right],
        assumption,
      },
      {
        apply submodule.injective_subtype,
        simp only [vsub_eq_sub, submodule.coe_subtype, add_subgroup_class.coe_sub, subtype.coe_mk, sub_sub_sub_cancel_right],
      },
    },
    {
      simp only [submodule.zero_mem, forall_true_left],
      exact submodule.zero_mem _,
    },
    {
      intros y z hy hz h,
      admit,
    },
    admit,
  },
  admit,
end

abbreviation halfspace (u : V) (c : ℝ) := {v : V | ⟪v, u⟫_ℝ ≤ c}
abbreviation hyperplane (u : V) (c : ℝ) := {v : V | ⟪v, u⟫_ℝ = c}

/- lemma relopen_subset_hyperplane_of_subset_halfspace
{A : set V} {x u : V} {c : ℝ} (hx : x ∈ A ∩ hyperplane u c)
(hA₁ : is_relopen A) (hA₂ : A ⊆ halfspace u c) :
A ⊆ hyperplane u c := sorry -/

lemma face_trans {A F G: set V}
(hGF : is_face F G) (hFA : is_face A F) : is_face A G :=
begin
  refine ⟨subset_trans hGF.1 hFA.1, hGF.2.1, _⟩,
  intros x hx y hy h,
  rcases h with ⟨z, hz, zG⟩,
  have ssubs:= hFA.2.2 x hx y hy ⟨z, hz, hGF.1 zG⟩,
  refine hGF.2.2 x (ssubs (left_mem_segment _ _ _))
                 y (ssubs (right_mem_segment _ _ _))
                 ⟨z, hz, zG⟩,
end

lemma relopen_subset_face_of_relopen_of_mem {A B F : set V} {x : V}
(hFA : is_face A F) (hBA : B ⊆ A) (hB : is_relopen B) (xBF : x ∈ B ∩ F) :
B ⊆ F :=
begin
  intros y yB,
  have xrB : x ∈ relint B,
  {
    rw [relint_relopen hB],
    exact xBF.1,
  },
  obtain ⟨z, zB, hs⟩ := exists_mem_open_segment_of_mem_relint
    xrB (subset_affine_span _ _ yB),
  exact hFA.2.2 y (hBA yB) z (hBA zB) ⟨x, hs, xBF.2⟩
    (left_mem_segment _ _ _),
end

lemma relopen_set_in_relint_face {A B : set V}
(Acv : convex ℝ A) (BA : B ⊆ A)
(Bro : is_relopen B) (Bcv : convex ℝ B) (Bne : B.nonempty):
B ⊆ relint (smallest_face_containing Acv BA) :=
begin
  let F := smallest_face_containing Acv BA,
  by_contradiction,
  rw [set.subset_def] at h,
  push_neg at h,
  rcases h with ⟨x, xB, xr⟩,
  have xfr : x ∈ relbd (smallest_face_containing Acv BA).val ∩ (smallest_face_containing Acv BA).val,
  {
    have : x ∈ (smallest_face_containing Acv BA).val :=
      smallest_face_containing_contains Acv BA xB,
    exact ⟨⟨subset_closure this, xr⟩, this⟩,
  },
  obtain ⟨u, xG, hGF⟩ := exists_supporting_halfspace
    (face_convex (smallest_face_containing Acv BA).property) xfr,
  let G := normal_face F.val u,
  change G ⊂ F.val at hGF,
  have hGA : is_face A G := face_trans
    (normal_face_is_face (face_convex F.property) u) F.property,
  have hBG := relopen_subset_face_of_relopen_of_mem hGA BA Bro ⟨xB, xG⟩,
  have hFG : F.val ⊆ G := smallest_face_containing_subset Acv hGA hBG,
  exact hGF.2 hFG,
end

lemma relint_faces_disjoint {A F G : set V}
(Acv : convex ℝ A) (hF : is_face A F) (hG : is_face A G) :
F = G ∨ relint F ∩ relint G = ∅ :=
begin
  by_cases h : (relint F ∩ relint G).nonempty,
  {
    left,
    by_contradiction hc,
    rcases h with ⟨x, hx⟩,
    rw [subset_antisymm_iff] at hc,
    push_neg at hc,
    simp only [imp_iff_or_not, set.not_subset] at hc,
    cases hc,
    {
      rcases hc with ⟨y, yG, ynF⟩,
      obtain ⟨z, zG, hs⟩ := exists_mem_open_segment_of_mem_relint
        hx.2 (subset_affine_span _ _ yG),
      apply ynF,
      refine hF.2.2 _ (hG.1 yG) _ (hG.1 zG) _ (left_mem_segment _ _ _),
      exact ⟨x, hs, relint_subset_self _ hx.1⟩,
    },
    {
      rcases hc with ⟨y, yF, ynG⟩,
      obtain ⟨z, zF, hs⟩ := exists_mem_open_segment_of_mem_relint
        hx.1 (subset_affine_span _ _ yF),
      apply ynG,
      refine hG.2.2 _ (hF.1 yF) _ (hF.1 zF) _ (left_mem_segment _ _ _),
      exact ⟨x, hs, relint_subset_self _ hx.2⟩,
    },
  },
  {
    right,
    rw [set.nonempty_def] at h,
    push_neg at h,
    ext,
    tauto,
  },
end

/- lemma surrounding_relint_face_unique {A B F : set V}
(Acv : convex ℝ A) (BA : B ⊆ A) (Bne : B.nonempty) (h : is_face A F) :
B ⊆ relint F → F = smallest_face_containing Acv BA :=
begin
  intro hBF,
  cases relint_faces_disjoint Acv h (smallest_face_containing Acv BA).property with hc hc,
  {
    exact hc,
  },
  {
    rcases Bne with ⟨x, xB⟩,
    have : x ∈ relint F ∩ relint (smallest_face_containing Acv BA).val,
    {
      refine ⟨hBF xB, _⟩,
      admit,
    },
    admit,
  },
end -/

lemma relopen_singleton (x : V) : is_relopen ({x} : set V) :=
begin
  simp only [is_relopen],
  have := affine_subspace.coe_affine_span_singleton ℝ V x,
  convert is_open_univ,
  ext y,
  simp only [set.mem_preimage, set.mem_singleton_iff, set.mem_univ, iff_true],
  have hy := y.property,
  change y.val ∈ (affine_span ℝ ({x} : set V) : set V) at hy,
  rw [this] at hy,
  exact set.eq_of_mem_singleton hy,
end

lemma point_in_relint_face {A : set V}
(Acv : convex ℝ A) {x : V} (xA : x ∈ A) :
x ∈ relint (smallest_face_containing_point Acv xA : set V) :=
begin
  have := relopen_set_in_relint_face Acv
    (set.singleton_subset_iff.mpr xA)
    (relopen_singleton x)
    (convex_singleton x)
    ⟨x, rfl⟩,
  exact set.singleton_subset_iff.mp this,
end

lemma surrounding_relint_face_unique {A F : set V} {x : V}
(Acv : convex ℝ A) (xA : x ∈ A) (h : is_face A F) :
x ∈ relint F → F = smallest_face_containing_point Acv xA :=
begin
  intro hBF,
  cases relint_faces_disjoint Acv h (smallest_face_containing_point Acv xA).property with hc hc,
  {
    exact hc,
  },
  {
    have : x ∈ relint F ∩ relint (smallest_face_containing_point Acv xA).val,
    {
      refine ⟨hBF, _⟩,
      exact point_in_relint_face Acv xA,
    },
    rw [hc, set.mem_empty_eq] at this,
    contradiction,
  },
end

/- lemma point_in_relint_face {A : set V}
(Acv : convex ℝ A) {x : V} (xA : x ∈ A) :
x ∈ relint (smallest_face_containing_point Acv xA : set V) :=
begin
  let F := smallest_face_containing_point Acv xA,
  by_contradiction xr,
  have xfr : x ∈ relbd F.val ∩ F.val,
  {
    have : x ∈ F.val :=
      smallest_face_containing_point_contains Acv xA,
    exact ⟨⟨subset_closure this, xr⟩, this⟩,
  },
  obtain ⟨u, xG, hGF⟩ := exists_supporting_halfspace
    (face_convex F.property) xfr,
  let G := normal_face F.val u,
  change G ⊂ F.val at hGF,
  have hGA : is_face A G := face_trans
    (normal_face_is_face (face_convex F.property) u) F.property,
  have hFG : F.val ⊆ G := smallest_face_containing_point_subset Acv hGA xG,
  exact hGF.2 hFG,
end -/

lemma convex_hull_subset_vector_space (A : set V) (E : submodule ℝ V) :
A ⊆ E → convex_hull ℝ A ⊆ E :=
begin
  rw [convex.convex_hull_subset_iff E.convex],
  exact id,
end

/- theorem relint_aff_int (A : set V) : is_relopen (relint A) :=
begin
  have hh: relint A = coerce_affine_subspace_set (affine_span ℝ A) (interior (set_into_affine_subspace A (affine_span ℝ A))) := sorry,
  have : set_into_affine_subspace (relint A) (affine_span ℝ A) = (interior (set_into_affine_subspace A (affine_span ℝ A))) := sorry,
  rw is_relopen,
  -- rw relint,
  simp,
  rw this,

end -/

lemma mem_vspan_normal_face (A : set V) (u : V) :
u ∈ (vector_span ℝ (normal_face A u))ᗮ :=
begin
  simp only [vector_span, mem_orthogonal_span],
  rintro - ⟨a, b, ha, hb, rfl⟩,
  simp only [mem_normal_face] at ha hb,
  simp only [vsub_eq_sub, inner_sub_left, sub_eq_zero],
  apply le_antisymm,
  all_goals {tauto},
end

/- lemma add_mem_normal_face (A : set V) (u : V) {x y : V}
(hx : x ∈ normal_face A u) (hy : y ∈ (vector_span ℝ (normal_face A u))ᗮ)
(hxy : x + y ∈ A) : x + y ∈ normal_face A u := sorry

lemma add_mem_normal_face' (A : set V) (u : V) :
A ∩ (normal_face A u + (vector_span ℝ (normal_face A u))ᗮ) = normal_face A u := sorry -/

lemma is_face_refl {A : set V} (hA : convex ℝ A) :
is_face A A :=
begin
  suffices h : A = normal_face A 0,
  {
    nth_rewrite 1 [h],
    apply normal_face_is_face hA,
  },
  simp only [normal_face],
  ext, split,
  {
    intro xA,
    refine ⟨xA, _⟩,
    simp only [inner_zero_right],
    rintro - -,
    exact le_refl 0,
  },
  {
    rintro ⟨xA, -⟩,
    exact xA,
  },
end
