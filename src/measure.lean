import measure_theory.measure.measure_space
  measure_theory.constructions.borel_space
  measure_theory.measure.finite_measure_weak_convergence

open_locale topological_space

section msupport

variables {α : Type}
  [measurable_space α] [topological_space α] [borel_space α]

def msupport
(μ : measure_theory.finite_measure α) : set α :=
{ x : α | ∀ U ∈ 𝓝 x, μ U > 0 }

lemma closed_msupport (μ : measure_theory.finite_measure α) :
is_closed (msupport μ) := sorry

lemma msupport_subset_of_tendsto
(μ : ℕ → measure_theory.finite_measure α)
(lμ : measure_theory.finite_measure α)
(h : filter.tendsto μ filter.at_top (𝓝 lμ)) :
msupport lμ ⊆ closure (⋃ (n : ℕ), msupport (μ n)) :=
sorry

end msupport