import convex convex_body linalg measure criticality
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
sorry

def uncoe_sph (E : submodule ℝ V) (u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) : metric.sphere (0 : E) 1 :=
begin
  refine ⟨⟨u, uE⟩, _⟩,
  simp only [mem_sphere_zero_iff_norm, submodule.coe_norm, submodule.coe_mk,
             norm_eq_of_mem_sphere],
end

namespace bm

def vol
(C : multiset (convex_body V))
-- (hdim : common_dimension C ≤ C.card)
: nnreal :=
sorry

def area
(C : multiset (convex_body V))
: measure_theory.finite_measure (metric.sphere (0 : V) 1) :=
sorry

def is_vol_coll (C : multiset (convex_body V)) (E : submodule ℝ V) : Prop :=
dim E = C.card ∧ multiset_all (convex_body_subset E) C

def is_area_coll (C : multiset (convex_body V)) (E : submodule ℝ V) : Prop :=
dim E = C.card + 1 ∧ multiset_all (convex_body_subset E) C

lemma factorize_vol
{C : multiset (convex_body V)}
{D : multiset (convex_body V)}
{E F : submodule ℝ V}
(hC : is_vol_coll C E)
(hCD : is_vol_coll (C + D) F)
(hEF : E ≤ F) :
vol (C + D) = vol C * vol (proj_coll Eᗮ D) :=
sorry

lemma factorize_area
{E F : submodule ℝ V}
{C : multiset (convex_body V)}
{D : multiset (convex_body V)}
(hC : is_vol_coll C E)
(hCD : is_area_coll (C + D) F)
(hEF : E ≤ F)
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

lemma area_continuous
{E : submodule ℝ V}
(C : multiset (convex_body V))
(C1 : ℕ → convex_body V)
(C1lim : convex_body V)
(hC : ∀ n : ℕ, is_area_coll (C1 n ::ₘ C) E)
(ht : filter.tendsto
  C1
  filter.at_top
  (𝓝 C1lim))
: filter.tendsto (λ n, area (C1 n ::ₘ C)) filter.at_top (𝓝 (area (C1lim ::ₘ C))) :=
sorry

end bm