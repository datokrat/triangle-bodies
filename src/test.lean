import algebra.group.defs group_theory.submonoid.basic
  group_theory.submonoid.operations

def p (V : Type) [add_monoid V] : Prop := sorry

@[congr]
lemma congr_p {V V' : Type} [add_monoid V] (h : V = V') : p V = @p V' (by { subst h, apply_instance }) :=
begin
  subst h,
end

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