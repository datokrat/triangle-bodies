import linalg
  analysis.inner_product_space.basic
  analysis.convex.basic
  topology.basic
  topology.subset_properties
  topology.metric_space.basic
  linear_algebra.affine_space.affine_subspace
  data.set.basic
  data.set.pointwise
  topology.basic
  analysis.inner_product_space.dual

open_locale pointwise
open_locale topological_space

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

lemma normal_face_subset {K : set V} {u : V} :
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

-- wrong for empty face
/- lemma polytope_face_normal {A F : set V} (h : is_polytope A) :
is_face A F → ∃ u : V, F = normal_face A u := sorry -/

/- lemma eq_inter_halfspaces_of_closed_convex
{A : set V} (Acv : convex ℝ A) (Acl : is_closed A) :
∃ S : set (V × ℝ), A = ⋂ pr ∈ S, { x : V | ⟪x, prod.fst pr⟫_ℝ ≤ pr.2 } :=
sorry -/

/- lemma closedify {A : set V} {u : V} :
∃ ε : ℝ, ε > 0 ∧ metric.ball u ε ⊆ A ↔ ∃ ε : ℝ, ε > 0 ∧ metric.closed_ball u ε ⊆ A :=
begin
  admit,
end -/

lemma closedify {A : set V} {u : V} :
(∃ (ε : ℝ) (εpos : ε > 0), metric.ball u ε ⊆ A) → ∃ (ε : ℝ) (εpos : ε > 0), metric.closed_ball u ε ⊆ A :=
begin
  rintro ⟨ε, εpos, εball⟩,
  refine ⟨ε / 2, half_pos εpos, _⟩,
  exact subset_trans (metric.closed_ball_subset_ball (half_lt_self εpos)) εball,
end

noncomputable def std_osegment_to_osegment (v w : V) :
open_segment ℝ (0 : ℝ) 1 → open_segment ℝ v w :=
begin
  intro s,
  refine ⟨(1 - s.val) • v + s.val • w, _⟩,
  rcases s with ⟨sval, sprop⟩,
  rw [open_segment_eq_Ioo (zero_lt_one : (0 : ℝ) < 1), set.mem_Ioo] at sprop,
  simp only,
  refine ⟨1 - sval, sval, _, _, _, rfl⟩,
  {
    simp only [sub_pos, sprop.2],
  },
  {
    exact sprop.1,
  },
  {
    simp only [sub_add_cancel],
  },
end

lemma mem_open_segment' {x y z : V} :
z ∈ open_segment ℝ x y ↔ ∃ c : ℝ, c ∈ set.Ioo (0 : ℝ) 1 ∧
z = c • x + (1 - c) • y :=
begin
  rw [open_segment, set.mem_set_of],
  split,
  {
    rintro ⟨a, b, ha, hb, hab, rfl⟩,
    refine ⟨a, _, _⟩,
    {
      rw [set.mem_Ioo],
      refine ⟨ha, _⟩,
      linarith,
    },
    {
      rw [←hab, add_tsub_cancel_left],
    },
  },
  {
    rintro ⟨c, hc, rfl⟩,
    rw [set.mem_Ioo] at hc,
    refine ⟨c, 1 - c, _, _, _, rfl⟩,
    {
      exact hc.1,
    },
    {
      simp only [sub_pos, hc.2],
    },
    {
      simp only [add_sub_cancel'_right],
    },
  },
end

lemma segments_closable_of_closed {A : set V}
(h : is_closed A) :
∀ x y : V, open_segment ℝ x y ⊆ A → segment ℝ x y ⊆ A :=
begin
  --rw [←is_open_compl_iff] at h,
  intros x y hseg,
  intros z hz,
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩,
  by_cases hc : a = 0 ∨ b = 0,
  {
    cases hc with hc hc,
    {
      rcases hc with rfl,
      rw [zero_add] at hab,
      rcases hab with rfl,
      rw [zero_smul, zero_add, one_smul],
      let f : ℝ → V := λ t, t • x + (1 - t) • y,
      have fc : continuous f := by continuity,
      have : filter.tendsto f (𝓝[set.Ioo 0 1] 0) (𝓝 y),
      {
        convert fc.continuous_within_at,
        simp only [f],
        simp only [zero_smul, sub_zero, zero_add, one_smul],
      },
      haveI : (𝓝[set.Ioo (0 : ℝ) 1] 0).ne_bot := left_nhds_within_Ioo_ne_bot zero_lt_one,
      refine is_closed.mem_of_tendsto h this _,
      refine filter.eventually.mp
        eventually_mem_nhds_within
        (filter.eventually_of_forall _),
      intros z hz,
      apply hseg,
      simp only [mem_open_segment', f],
      exact ⟨z, hz, rfl⟩,
    },
    {
      rcases hc with rfl,
      rw [add_zero] at hab,
      rcases hab with rfl,
      rw [zero_smul, add_zero, one_smul],
      let f : ℝ → V := λ t, t • x + (1 - t) • y,
      have fc : continuous f := by continuity,
      have : filter.tendsto f (𝓝[set.Ioo 0 1] 1) (𝓝 x),
      {
        convert fc.continuous_within_at,
        simp only [f],
        simp only [one_smul, sub_self, add_zero, zero_smul],
      },
      haveI : (𝓝[set.Ioo (0 : ℝ) 1] 1).ne_bot := right_nhds_within_Ioo_ne_bot zero_lt_one,
      refine is_closed.mem_of_tendsto h this _,
      refine filter.eventually.mp
        eventually_mem_nhds_within
        (filter.eventually_of_forall _),
      intros z hz,
      apply hseg,
      simp only [mem_open_segment', f],
      exact ⟨z, hz, rfl⟩,
    },
  },
  {
    push_neg at hc,
    replace ha := lt_of_le_of_ne ha (hc.1 ∘ eq.symm),
    replace hb := lt_of_le_of_ne hb (hc.2 ∘ eq.symm),
    apply hseg,
    simp only [open_segment],
    refine ⟨a, b, ha, hb, hab, rfl⟩,
  },
end

lemma closed_iff_segments_closable {A : set V}
(Acv : convex ℝ A):
is_closed A ↔ ∀ x y : V, open_segment ℝ x y ⊆ A → segment ℝ x y ⊆ A :=
begin
  split,
  {
    exact segments_closable_of_closed,
  },
  {
    intro h,
    admit,
  },
end

lemma open_segment_nonempty (x y : V) :
(open_segment ℝ x y).nonempty :=
begin
  let half : ℝ := 1 / 2,
  refine ⟨half • x + half • y, half, half, _, _, _, rfl⟩,
  all_goals {simp only [half]},
  {positivity},
  {positivity},
  {ring},
end
