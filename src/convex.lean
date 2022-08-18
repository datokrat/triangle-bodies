import measure_theory.measure.finite_measure_weak_convergence
  algebra.category.FinVect
  analysis.inner_product_space.basic
  analysis.convex.basic
  topology.basic
  topology.subset_properties
  topology.metric_space.basic
  analysis.convex.cone
  order.complete_lattice
  linear_algebra.affine_space.affine_subspace
  data.set.basic
  data.set.pointwise
  topology.basic

open_locale pointwise

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma convex_sum {A B : set V}
(Acv : convex ℝ A) (Bcv : convex ℝ B) :
convex ℝ (A + B) :=
begin
  rintro - - ⟨xa, xb, xaA, xbB, rfl⟩ ⟨ya, yb, yaA, ybB, rfl⟩,
  rintro a b a0 b0 ab1,
  refine ⟨a • xa + b • ya, a • xb + b • yb, _, _, _⟩,
  {
    apply Acv,
    all_goals {assumption},
  },
  {
    apply Bcv,
    all_goals {assumption},
  },
  {
    simp only [smul_add],
    abel,
  },
end

def is_convex_body (K : set V) : Prop :=
convex ℝ K ∧ is_compact K ∧ set.nonempty K

lemma convex_convex_body {K : set V} (Kcv : is_convex_body K) :
convex ℝ K := Kcv.1

def is_polytope (P : set V) : Prop :=
  ∃ S : set V, S.finite ∧ S.nonempty ∧ P = convex_hull ℝ S

def normal_face (K : set V) (u : V): set V :=
  { x | x ∈ K ∧ ∀ y ∈ K, ⟪x, u⟫_ℝ ≥ ⟪y, u⟫_ℝ }

lemma mem_normal_face {K : set V} {u : V} {x : V} :
x ∈ normal_face K u ↔ x ∈ K ∧ ∀ y ∈ K, ⟪x, u⟫_ℝ ≥ ⟪y, u⟫_ℝ :=
begin
  simp only [normal_face, set.mem_set_of],
end

def normal_face_subset {K : set V} {u : V} :
normal_face K u ⊆ K :=
begin
  rintro x hx,
  simp only [mem_normal_face] at hx,
  tauto,
end

lemma subset_normal_face {K : set V} {u : V} {S : set V}:
S ⊆ normal_face K u ↔ S ⊆ K ∧ ∀ s ∈ S, ∀ y ∈ K, ⟪s, u⟫_ℝ ≥ ⟪y, u⟫_ℝ :=
begin
  simp only [set.subset_def, mem_normal_face],
  split,
  {
    rintro h,
    split,
    {rintro x hx, exact (h x hx).1},
    {rintro s hs y hy, exact (h s hs).2 y hy},
  },
  {
    rintro h x hx,
    split,
    {exact h.1 x hx},
    {rintro y hy, exact h.2 x hx y hy},
  }
end 

def is_face (A : set V) (F : set V) :=
F ⊆ A ∧ convex ℝ F ∧
∀ x y ∈ A, (∃ z ∈ open_segment ℝ x y, z ∈ F)
→ segment ℝ x y ⊆ F

lemma face_convex {A F: set V} (h : is_face A F) : convex ℝ F :=
begin
  simp only [is_face] at h,
  cases_matching* [_ ∧ _],
  assumption,
end

lemma face_subset {A F : set V} (h : is_face A F) : F ⊆ A :=
begin
  simp only [is_face] at h,
  cases_matching* [_ ∧ _],
  assumption,
end

lemma face_absorbs_segments {A F : set V} (h : is_face A F) :
∀ x y ∈ A, (∃ z ∈ open_segment ℝ x y, z ∈ F)
→ segment ℝ x y ⊆ F :=
begin
  simp only [is_face] at h,
  cases_matching* [_ ∧ _],
  assumption,
end

lemma polytope_face_normal {A F : set V} (h : is_polytope A) :
is_face A F → ∃ u : V, F = normal_face A u := sorry

lemma normal_face_is_face {A : set V} (h : convex ℝ A) :
∀ u : V, is_face A (normal_face A u) := sorry

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

lemma normal_face_spanned_by_verts {S : set V} (u : V) :
normal_face (convex_hull ℝ S) u = convex_hull ℝ (normal_face S u) := sorry

--lemma face_body {A : set V} (u : V) (h : is_convex_body A) : is_convex_body (face A u) := sorry
lemma face_polytope {A F : set V} (h : is_polytope A) (hf : is_face A F) : is_polytope F := sorry

lemma face_closed {A F : set V} (h : is_closed A) (hf : is_face A F) :
is_closed F := sorry

def relint (A : set V) : set V :=
coe '' interior ((coe : affine_span ℝ A → V) ⁻¹' A)

def relbd (A : set V) : set V :=
(closure A) \ (relint A)

def is_relopen (A : set V) : Prop :=
is_open ((coe : affine_span ℝ A → V) ⁻¹' A)

theorem open_in_subspace (E : affine_subspace ℝ V) (A : set V) (h : is_open A) : is_open ((coe : E → V) ⁻¹' A) :=
begin
  let c := (coe : E → V),
  have : c = (coe : E → V) := rfl,
  let cc : continuous (coe : E → V) := continuous_subtype_coe,
  refine is_open.preimage cc h,
end

-- lemma relopen_iff_open {A : set V} (hA : vector_span ℝ A = ⊤) :
-- is_relopen A ↔ is_open A := sorry

lemma relint_eq_int {A : set V} (hA : vector_span ℝ A = ⊤) :
relint A = interior A := sorry

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
lemma relint_inter_flat {A : set V} {E : submodule ℝ V}
{x : V} (xA : x ∈ relint A) (xE : x ∈ E) :
(⟨x, xE⟩ : E) ∈ relint ((coe : E → V) ⁻¹' A) := sorry


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

def smallest_face_containing {A B : set V}
(Acv : convex ℝ A) (BA : B ⊆ A) : faces A :=
⟨
  set.sInter (faces_containing BA),
  face_sInter Acv (λ G hG, hG.1) ⟨A, ⟨set_own_face Acv, BA⟩⟩
⟩

lemma smallest_face_containing_contains {A B : set V}
(Acv : convex ℝ A) (BA : B ⊆ A) :
B ⊆ smallest_face_containing Acv BA := sorry

def smallest_face_containing_point {A : set V}
(Acv : convex ℝ A) {x : V} (xA : x ∈ A) : faces A :=
smallest_face_containing Acv (set.singleton_subset_iff.mpr xA)

lemma point_in_proper_face_of_relbd {A : set V}
(Acv : convex ℝ A) {x : V} (hx : x ∈ relbd A ∩ A) :
(smallest_face_containing_point Acv hx.2 : set V) ⊂ A := sorry

lemma relopen_set_in_relint_face {A B : set V}
(Acv : convex ℝ A) (BA : B ⊆ A)
(Bro : is_relopen B) (Bcv : convex ℝ B) (Bne : B.nonempty):
B ⊆ relint (smallest_face_containing Acv BA) :=
begin
  let F := smallest_face_containing Acv BA,
  by_contradiction,
  admit,
end

lemma relint_faces_disjoint {A F G : set V}
(Acv : convex ℝ A) (hF : is_face A F) (hG : is_face A G) :
F = G ∨ relint F ∩ relint G = 0 := sorry

lemma surrounding_relint_face_unique {A B F : set V}
(Acv : convex ℝ A) (BA : B ⊆ A) (Bne : B.nonempty) (h : is_face A F) :
B ⊆ relint F → F = smallest_face_containing Acv BA := sorry

lemma relopen_singleton (x : V) : is_relopen ({x} : set V) := sorry

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

lemma convex_hull_subset_vector_space (A : set V) (E : submodule ℝ V) :
A ⊆ E → convex_hull ℝ A ⊆ E := sorry


/- theorem relint_aff_int (A : set V) : is_relopen (relint A) :=
begin
  have hh: relint A = coerce_affine_subspace_set (affine_span ℝ A) (interior (set_into_affine_subspace A (affine_span ℝ A))) := sorry,
  have : set_into_affine_subspace (relint A) (affine_span ℝ A) = (interior (set_into_affine_subspace A (affine_span ℝ A))) := sorry,
  rw is_relopen,
  -- rw relint,
  simp,
  rw this,

end -/
