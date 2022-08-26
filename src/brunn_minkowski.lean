import convex convex_body linalg measure criticality polytope
  submodule_pair
  analysis.convex.basic
  data.multiset.basic
  measure_theory.measure.measure_space
  topology.basic

open_locale pointwise
open_locale ennreal -- for ∞ notation
open_locale topological_space -- for 𝓝 notation

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

variables {V: Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]

noncomputable instance sph_borel :=
borel (metric.sphere (0 : V) 1)

instance : borel_space (metric.sphere (0 : V) 1) :=
⟨rfl⟩

-- instance : opens_measurable_space (metric.sphere (0 : V) 1) := sorry

def set_res_amb
(E : submodule ℝ V)
(A : set V) : set E :=
E.subtype ⁻¹' A

def coll_res_amb
(C : multiset (set V))
(E : submodule ℝ V) : multiset (set E) :=
C.map (set_res_amb E)

def coe_sph (E : submodule ℝ V) : metric.sphere (0 : E) 1 → metric.sphere (0 : V) 1 :=
begin
  intro x,
  refine ⟨x.val.val, x.property⟩,
end

def uncoe_sph (E : submodule ℝ V) (u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) : metric.sphere (0 : E) 1 :=
begin
  refine ⟨⟨u, uE⟩, _⟩,
  simp only [mem_sphere_zero_iff_norm, submodule.coe_norm, submodule.coe_mk,
             norm_eq_of_mem_sphere],
end

lemma coe_uncoe_sph {E : submodule ℝ V}
(u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) :
coe_sph E (uncoe_sph E u uE) = u :=
begin
  simp only [coe_sph, uncoe_sph],
  apply subtype.coe_injective,
  simp only [subtype.coe_eta],
end

namespace bm

axiom vol
(C : multiset (convex_body V))
: nnreal

axiom area
(C : multiset (convex_body V))
: measure_theory.finite_measure (metric.sphere (0 : V) 1)

def is_vol_coll (C : multiset (convex_body V)) (E : submodule ℝ V) : Prop :=
dim E = C.card ∧ multiset_all (convex_body_subset E) C

def is_area_coll (C : multiset (convex_body V))  : Prop :=
dim V = C.card + 1

lemma factorize_vol
{C : multiset (convex_body V)}
{D : multiset (convex_body V)}
{E F : submodule ℝ V}
(hC : is_vol_coll C E)
(hCD : is_vol_coll (C + D) F)
(hEF : E ≤ F) :
vol (C + D) = vol C * vol (proj_coll Eᗮ D) :=
sorry

-- What happens if F is not ⊤?
lemma factorize_area
{E : submodule ℝ V}
{C : multiset (convex_body V)}
{D : multiset (convex_body V)}
(hC : is_vol_coll C E)
(hCD : is_area_coll (C + D))
(hsc : semicritical_spaces (C.map span_of_convex_body)) :
msupport (area (C + D)) = coe_sph Eᗮ '' msupport (area (proj_coll Eᗮ D)) :=
sorry

lemma vol_continuous
{E : submodule ℝ V}
(C : multiset (convex_body V))
(C1 : ℕ → convex_body V)
(C1lim : convex_body V)
(hC : ∀ n : ℕ, is_vol_coll (C1 n ::ₘ C) E)
(ht : filter.tendsto
  C1
  filter.at_top
  (𝓝 C1lim))
: filter.tendsto (λ n, vol (C1 n ::ₘ C)) filter.at_top (𝓝 (vol (C1lim ::ₘ C))) :=
sorry

lemma area_cons_translate
{K : convex_body V}
{C : multiset (convex_body V)} {x : V}
(hC : is_area_coll (K ::ₘ C)) :
area ((K + {x}) ::ₘ C) = area (K ::ₘ C) := sorry

lemma area_cons_smul
{K : convex_body V}
{C : multiset (convex_body V)} {c : nnreal}
(hC : is_area_coll (K ::ₘ C)) :
area ((c • K) ::ₘ C) = c • area (K ::ₘ C) := sorry

lemma area_continuous
(C : multiset (convex_body V))
(C1 : ℕ → convex_body V)
(C1lim : convex_body V)
(hC : ∀ n : ℕ, is_area_coll (C1 n ::ₘ C))
(ht : filter.tendsto
  C1
  filter.at_top
  (𝓝 C1lim))
: filter.tendsto (λ n, area (C1 n ::ₘ C)) filter.at_top (𝓝 (area (C1lim ::ₘ C))) :=
sorry

lemma area_empty : msupport (area (0 : multiset (convex_body V))) = ⊤ :=
sorry

/- lemma polytope_area_discrete
{C : multiset (polytope V)}
(hC : is_area_coll (C.map convex_body_of_polytope) ⊤)
{U : set (metric.sphere (0 : V) 1)}
(hU : measurable_set U) :
(area (C.map convex_body_of_polytope)).discrete := sorry -/

/- lemma polytope_area_by_faces
{C : multiset (polytope V)}
(hC : is_area_coll (C.map convex_body_of_polytope) ⊤)
(u : metric.sphere (0 : V) 1) :
area (C.map convex_body_of_polytope) {u} =
vol (C.map (λ P, (convex_body_of_polytope P).normal_face u)) :=
sorry -/

def τ' (A : set V) (U : set (metric.sphere (0 : V) 1)) : set V :=
⋃ (u : metric.sphere (0 : V) 1) (uU : u ∈ U),
normal_face A u.val

def τ (K : convex_body V) (U : set (metric.sphere (0 : V) 1)) : set V :=
⋃ (u : metric.sphere (0 : V) 1) (H : u ∈ U),
normal_face K.val u.val

-- This is tricky.
-- If K, L are full-dimensional, follows by polarization and the formula for the "unmixed" area.
-- The area measures of all sums appearing in the polarization formula are equal:
-- If K/L is not part of the sum, trivial
-- Otherwise, use the τ formula (Schneider, Theorem 4.2.3)
-- If K, L are not full-dimensional, apply the above special case
-- for K+B/L+B and B/B and use additivity of area
lemma area_determined_by_τ_add
{C : multiset (convex_body V)}
{K L : convex_body V}
(hC : is_area_coll (K ::ₘ C))
(hD : is_area_coll (L ::ₘ C))
{U : set (metric.sphere (0 : V) 1)}
(hU : measurable_set U)
(h : ∀ M : convex_body V, τ (K + M) U = τ (L + M) U) :
area (K ::ₘ C) U = area (L ::ₘ C) U := sorry

lemma is_area_coll_cons_of_head_subset
{C : multiset (convex_body V)} {K L : convex_body V}
{E : submodule ℝ V}
(CD : K.val ⊆ L.val)
(h : is_area_coll (L ::ₘ C)) :
is_area_coll (K ::ₘ C) :=
begin
  simp only [is_area_coll, multiset.card_cons] at h ⊢,
  exact h,
end

end bm