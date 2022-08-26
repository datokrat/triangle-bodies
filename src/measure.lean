import measure_theory.measure.measure_space
  measure_theory.constructions.borel_space
  measure_theory.measure.finite_measure_weak_convergence

open_locale topological_space

section msupport

variables {α : Type}
  [metric_space α] [proper_space α]
  [measurable_space α] [borel_space α]

def msupport
(μ : measure_theory.finite_measure α) : set α :=
{ x : α | ∀ U : set α, x ∈ U → is_open U → μ U > 0 }

/- lemma closed_msupport (μ : measure_theory.finite_measure α) :
is_closed (msupport μ) := sorry -/

-- needs second-countability
lemma integral_eq_of_eq_on_msupport {f g : α → ℝ}
{μ : measure_theory.finite_measure α}
(hf : measure_theory.integrable f μ.val)
(hg : measure_theory.integrable g μ.val)
(h : ∀ G ∈ msupport μ, f G = g G) :
∫ G, f G ∂μ.val = ∫ G, g G ∂μ.val := sorry

lemma msupport_subset_of_tendsto
(μ : ℕ → measure_theory.finite_measure α)
(lμ : measure_theory.finite_measure α)
(h : filter.tendsto μ filter.at_top (𝓝 lμ)) :
msupport lμ ⊆ closure (⋃ (n : ℕ), msupport (μ n)) :=
sorry

instance finite_measure_val {α : Type} [measurable_space α] {μ : measure_theory.finite_measure α} :
measure_theory.is_finite_measure μ.val := μ.property

noncomputable def finite_measure_map {α β : Type}
[measurable_space α] [measurable_space β]
(f : α → β)
(μ : measure_theory.finite_measure α) : measure_theory.finite_measure β :=
begin
  refine ⟨measure_theory.measure.map f μ.val, _⟩,
  exact measure_theory.measure.is_finite_measure_map μ f,
end

/- def measure_theory.finite_measure.discrete (μ : measure_theory.finite_measure α) :=
∃ S : set α, S.countable ∧ μ(Sᶜ) = 0

lemma discrete_measure_ext
{μ ν : measure_theory.finite_measure α}
(hμ : μ.discrete) (hν : ν.discrete)
{U : set α} (hU : measurable_set U) :
μ U = ν U ↔ ∀ x : α, x ∈ U → μ {x} = ν {x} := sorry -/

end msupport