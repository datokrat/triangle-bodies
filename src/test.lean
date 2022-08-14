import algebra.group.defs group_theory.submonoid.basic
  group_theory.submonoid.operations tactic matryoshka microid_ops pre_pruning

def p (V : Type) [add_monoid V] : Prop := sorry

@[congr]
lemma congr_p {V V' : Type} [add_monoid V] (h : V = V') : p V = @p V' (by { subst h, apply_instance }) :=
begin
  subst h,
end

/- @[congr]
lemma congr_lambda {α β : Type} {a b : α → β} (h : a = b) : (λ x, a x) = (λ x, b x) := sorry
 -/
--set_option pp.implicit true

#check eq.rec

example {V : Type}
  [add_monoid V]
  (k : ℕ → add_submonoid V)
  (h : p (k (0 - 0))) : false :=
begin
  simp only [nat.sub_self] at h,
  simp at h,
  admit,
end

theorem one_a (n : ℕ) : (n^2 + (n+1)^2 = (n+2)^2 → n = 3) :=
begin
  intro h,
  zify at h ⊢,
  rw ← sub_eq_zero at h,
  have : ((n:ℤ) - 3) * (n + 1) = 0,
  { rw ← h, ring_exp, },
  rw [mul_eq_zero, sub_eq_zero] at this,
  apply this.resolve_right,
  rw [add_eq_zero_iff_eq_neg],
  apply int.no_confusion,
end

example {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]
{k : ℕ} {u: metric.sphere (0 : V) 1}
(E : submodule ℝ V)
(B : multiset (microid_pair k u))
(b : microid_pair k u) :
(λ x : microid_pair k u, microid_of_measure (project_microid_measure E (pair_to_measure x))) =
(λ x : microid_pair k u, proj_body E (microid_of_measure (pair_to_measure x))) :=
begin
  simp only [proj_microid_of_measure E], -- rw does not work
end


variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

example {k : ℕ} (v : V) :
false :=
begin
  let x : fin k.succ := sorry,
  let y : fin k.succ := sorry,
  replace J : unbounded_microid_generator V k := sorry,
  replace hx : ⟪(J x), v⟫_ℝ ≥ ⟪(J y), v⟫_ℝ := sorry,
  have : ∀ a b : ℝ, a ≥ b ↔ a - b ≤ 0 := sorry,
  rw [this ⟪(J x), v⟫_ℝ ⟪(J y), v⟫_ℝ] at hx, -- !??
end

