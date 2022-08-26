import convex convex_body finset

open_locale topological_space

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V: Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def polytope (V : Type) [inner_product_space ℝ V] [finite_dimensional ℝ V] :=
{ P : set V // is_polytope P }

instance polytope.has_lift_t : has_lift_t (polytope V) (set V) :=
{
  lift := (coe : { P // is_polytope P } → set V)
}

lemma polytope_convex {P : set V} (hP : is_polytope P) :
convex ℝ P :=
begin
  obtain ⟨S, Sfin, Sne, rfl⟩ := hP,
  exact convex_convex_hull ℝ S,
end

lemma is_convex_body_of_is_polytope {P : set V} (hP : is_polytope P) :
is_convex_body P :=
begin
  --let hP' := hP,
  obtain ⟨S, Sfin, Sne, rfl⟩ := id hP,
  refine ⟨_, _, _⟩,
  {
    exact polytope_convex hP,
  },
  {
    exact Sfin.compact_convex_hull,
  },
  {
    exact Sne.convex_hull,
  },
end

def convex_body_of_polytope (P : polytope V) : convex_body V :=
⟨P.val, is_convex_body_of_is_polytope P.property⟩

lemma polytope_normal_face_nonempty {P : set V} (hP : is_polytope P) (u : V) :
(normal_face P u).nonempty :=
begin
  let K : convex_body V := ⟨P, is_convex_body_of_is_polytope hP⟩,
  exact K.normal_face_nonempty u,
end


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



lemma finset_facial_gap {S : finset V} (u : V) (Sne : (normal_face ↑S u).nonempty) :
∃ ε : ℝ, ε > 0 ∧
∀ x y : V, x ∈ ↑S \ normal_face ↑S u → y ∈ normal_face ↑S u →
⟪(y - x), u⟫_ℝ > ε :=
begin
  by_cases hne : S.nonempty, rotate,
  {
    simp only [finset.not_nonempty_iff_eq_empty] at hne,
    obtain rfl := hne,
    refine ⟨1, zero_lt_one, _⟩,
    simp only [finset.coe_empty, set.empty_diff, set.mem_empty_eq, is_empty.forall_iff, forall_const, implies_true_iff],
  },
  by_cases h : normal_face ↑S u = ↑S,
  {
    refine ⟨1, zero_lt_one, _⟩,
    rw [h],
    intros x y hx xy,
    simp only [set.diff_self, set.mem_empty_eq] at hx,
    contradiction,
  },
  have Sfin : (↑S : set V).finite,
  {
    apply set.finite.of_finset S,
    simp only [finset.mem_coe, iff_self, forall_const],
  },
  have nSfin : (normal_face ↑S u).finite := Sfin.subset normal_face_subset,
  let nS' := nSfin.to_finset,
  have cSfin : (↑S \ normal_face ↑S u).finite := Sfin.subset (set.diff_subset _ _),
  have cSne : (↑S \ normal_face ↑S u).nonempty,
  {
    rw [←set.ne_empty_iff_nonempty],
    intro hc,
    apply h,
    refine subset_antisymm normal_face_subset _,
    rw [set.diff_eq_empty] at hc,
    exact hc,
  },
  let cS' := cSfin.to_finset,
  have nS'ne : nS'.nonempty,
  {
    obtain ⟨x, hx⟩ := Sne,
    refine ⟨x, _⟩,
    rw [set.finite.mem_to_finset],
    exact hx,
  },
  have cS'ne : cS'.nonempty,
  {
    obtain ⟨x, hx⟩ := cSne,
    refine ⟨x, _⟩,
    rw [set.finite.mem_to_finset],
    exact hx,
  },
  let T := finset.product nS' cS',
  let f : V × V → ℝ := λ pr, ⟪pr.snd - pr.fst, u⟫_ℝ,
  obtain ⟨p, hp, prop⟩ := ex_finset_argmax f (finset.nonempty_product.mpr ⟨nS'ne, cS'ne⟩),
  rw [finset.mem_product] at hp,
  let δ := f p,
  let ε := -(1/2) * δ,
  have hδ : δ < 0,
  {
    simp only [δ, f],
    by_contra,
    replace h := le_of_not_gt h,
    simp only [inner_sub_left, sub_nonneg] at h,
    rcases hp with ⟨hp₁, hp₂⟩,
    simp only [set.finite.mem_to_finset, set.mem_diff] at hp₁ hp₂,
    apply hp₂.2,
    simp only [mem_normal_face] at hp₁ ⊢,
    refine ⟨hp₂.1, _⟩,
    intros y hy,
    exact le_trans (hp₁.2 y hy) h,
  },
  refine ⟨ε, _, _⟩,
  {
    apply mul_pos_of_neg_of_neg,
    {simp only [one_div, right.neg_neg_iff, inv_pos, zero_lt_bit0, zero_lt_one]},
    {exact hδ},
  },
  {
    intros l m hl hm,
    simp only [ε],
    rw [←neg_sub, inner_neg_left, neg_mul, gt_iff_lt, neg_lt_neg_iff],
    simp only [finset.mem_product, set.finite.mem_to_finset] at prop,
    have hle := prop ⟨m, l⟩ ⟨hm, hl⟩,
    simp only [f, ge_iff_le] at hle,
    refine lt_of_le_of_lt hle _,
    change δ < 1 / 2 * δ,
    rw [←neg_lt_neg_iff, ←mul_neg],
    rw [←neg_neg δ] at hδ,
    refine lt_of_le_of_lt (le_of_eq _) (half_lt_self (pos_of_neg_neg hδ)),
    ring,
  },
end

lemma polytope_facial_gap {P : set V} (hP : is_polytope P) (u : V) :
∃ ε : ℝ, ε > 0 ∧ ∀ v ∈ metric.ball u ε,
normal_face P v ⊆ normal_face P u :=
begin
  obtain ⟨S, Sfin, Sne, rfl⟩ := id hP,
  let S' := Sfin.to_finset,
  have S'ne : S'.nonempty,
  {
    obtain ⟨x, hx⟩ := Sne,
    refine ⟨x, _⟩,
    simp only [set.finite.mem_to_finset],
    exact hx,
  },
  have fne := polytope_normal_face_nonempty hP u,
  have fne' : (normal_face ↑S' u).nonempty,
  {
    rw [normal_face_spanned_by_verts, convex_hull_nonempty_iff] at fne,
    obtain ⟨x, hx⟩ := fne,
    refine ⟨x, _⟩,
    simp only [set.finite.coe_to_finset],
    exact hx,
  },
  rcases finset_facial_gap u fne' with ⟨ε, hε, gap⟩,
  let g := λ x : V, ∥x∥,
  obtain ⟨z, zS, hz⟩ := ex_finset_argmax g S'ne,
  simp only [set.finite.mem_to_finset] at zS hz,
  simp only [g] at hz,
  
  let f := λ x : ℝ, (∥z∥ + ∥z∥) * x,
  have fcont : continuous f := by continuity,
  have ftt : filter.tendsto f (𝓝 0) (𝓝 _) := fcont.continuous_at,
  have f0 : f 0 = 0,
  {
    simp only [f],
    ring,
  },
  simp only [filter.tendsto_def, f0] at ftt,
  replace ftt := ftt _ (metric.ball_mem_nhds 0 hε),
  simp only [metric.mem_nhds_iff, real.ball_eq_Ioo] at ftt,
  rcases ftt with ⟨τ, hτ, balls⟩,
  let ρ := τ / 2,
  have hρ : ρ > 0 := by exact half_pos hτ,
  have fρ : f ρ < ε,
  {
    simp only [zero_add] at balls,
    refine (balls _).2,
    split,
    {
      simp only [ρ],
      apply sub_left_lt_of_lt_add,
      positivity,
    },
    {
      exact half_lt_self hτ,
    },
  },

  let δ : ℝ := ρ,
  have hδ : δ > 0 := hρ,
  refine ⟨δ, hδ, _⟩,
  intros v hv,
  simp only [normal_face_spanned_by_verts],
  apply convex_hull_mono,
  intros x hx,
  rw [mem_normal_face] at hx,
  obtain ⟨y, hy⟩ := fne',
  by_contradiction hc,
  replace hc : x ∈ ↑S' \ normal_face ↑S' u,
  {
    simp only [set.finite.coe_to_finset, set.mem_diff],
    exact ⟨hx.1, hc⟩,
  },
  replace gap := gap _ _ hc hy,
  rw [inner_sub_left, gt_iff_lt, lt_sub] at gap,
  have yS : y ∈ S,
  {
    simp only [set.finite.coe_to_finset] at hy,
    exact normal_face_subset hy,
  },
  have hx' := hx.2 y yS,
  have hyu : ⟪y, u⟫_ℝ ≤ ⟪y, v⟫_ℝ + ∥y∥ * δ,
  {
    rw [metric.mem_ball_comm, mem_ball_iff_norm] at hv,
    rw [←sub_le_iff_le_add', ←inner_sub_right],
    refine le_trans (real_inner_le_norm y (u - v)) _,
    exact mul_le_mul_of_nonneg_left (le_of_lt hv) (norm_nonneg _),
  },
  have hxv : ⟪x, v⟫_ℝ ≤ ⟪x, u⟫_ℝ + ∥x∥ * δ,
  {
    rw [mem_ball_iff_norm] at hv,
    rw [←sub_le_iff_le_add', ←inner_sub_right],
    refine le_trans (real_inner_le_norm x (v - u)) _,
    exact mul_le_mul_of_nonneg_left (le_of_lt hv) (norm_nonneg _),
  },
  have := gap,
  replace := lt_of_lt_of_le this (sub_le_sub_right hyu _),
  rw [add_sub_assoc] at this,
  replace := lt_of_lt_of_le this (add_le_add_right hx' _),
  replace := lt_of_lt_of_le this (add_le_add_right hxv _),
  rw [add_assoc, lt_add_iff_pos_right, ←add_sub_assoc, ←add_mul, sub_pos] at this,
  rw [set.finite.coe_to_finset] at hc,
  replace := lt_of_lt_of_le this
  (mul_le_mul_of_nonneg_right (
    add_le_add (hz x hc.1) (hz y yS)
  ) (le_of_lt hδ)),
  simp only [δ, f, ρ] at this fρ,
  linarith,
end