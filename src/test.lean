import algebra.group.defs group_theory.submonoid.basic
  group_theory.submonoid.operations tactic matryoshka microid_ops

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

#check @eq.rec

def q (V : Type) [add_monoid V] : ℕ := sorry

@[congr]
lemma congr_q {V V' : Type} [add_monoid V] (h : V = V') : q V = @q V' (by { subst h, apply_instance }) :=
begin
  subst h,
end

example {V : Type} {α β : Type}
  [add_monoid V]
  (A' : multiset α)
  (f : α → β)
  (g : α → β)
  (k : multiset β → add_submonoid V)
  (h : f = g) :
  let E : add_submonoid V := k (multiset.map f A')
  in q ↥E = q (k (A'.map g)) :=
begin
  intros E,
  simp only [E, function.comp_app],
  rw [h],
end

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

example {V : Type} {c₁ c₂ c₃ : ℕ}
  [inner_product_space ℝ V]
  [finite_dimensional ℝ V]
  (φ₁ : fin c₁.succ → fin c₂.succ)
  (φ₂ : fin c₂.succ → fin c₃.succ)
  (G : ↥(microid_generator_space V c₃))
  (h : 0 < metric.diam (set.range ((G.val ∘ φ₂) ∘ φ₁))) :
  metric.diam (set.range (G.val ∘ φ₂)) > 0 :=
begin
  simp only [subtype.val_eq_coe, gt_iff_lt],
  refine lt_of_lt_of_le _ _,
end
