import data.multiset.basic
import tactic.wlog

variables {α : Type}

lemma pauls_multiset_induction {α: Type} {p : multiset α → Prop} (C : multiset α) :
p 0 → (Π C' : multiset α, (Π a : α, p C' → p (a ::ₘ C'))) → p C :=
begin
  induction C using multiset.strong_induction_on,
  by_cases C_s = 0,
  {
    rcases h with rfl,
    tauto,
  },
  {
    intro _,
    rcases multiset.exists_mem_of_ne_zero h with ⟨d, hd⟩,
    rcases multiset.exists_cons_of_mem hd with ⟨D, rfl⟩,
    intro f,
    have D_lt_C : D < d ::ₘ D := multiset.lt_iff_cons_le.mpr ⟨d, le_refl (d ::ₘ D)⟩,
    have := C_ᾰ D D_lt_C ᾰ f,
    exact f D d this,
  }
end

lemma multiset_split_le' {F : multiset α} :
∀ C D : multiset α, ∀ (h : F ≤ C + D), ∃ G H : multiset α, G ≤ C ∧ H ≤ D ∧ F = G + H :=
begin
  induction F using pauls_multiset_induction with K l ih,
  {
    intros C D h,
    refine ⟨0, 0, _⟩,
    simp,
  },
  {
    intros C D h,
    have hl : l ∈ C + D :=
    begin
      refine multiset.mem_of_subset _ (multiset.mem_cons_self l K),
      exact multiset.subset_of_le h,
    end,
    wlog hlC : l ∈ C using [C D, D C],
    {exact multiset.mem_add.mp hl},
    {
      rcases multiset.exists_cons_of_mem hlC with ⟨T, rfl⟩,
      have KssTD : K ≤ T + D :=
      begin --multiset.cons_subset_cons, multiset.cons_add] using h,
        rw [multiset.cons_add] at h,
        refine (multiset.cons_le_cons_iff l).mp h,
      end,
      rcases ih _ _ KssTD with ⟨G', H', hG, hH, rfl⟩,
      refine ⟨l ::ₘ G', H', _⟩,
      split,
      any_goals {simp [hG, hH, multiset.cons_le_cons]},
    },
    {
      rw [add_comm] at h hl,
      rcases this h hl with ⟨G', H', hG, hH, hhh⟩,
      refine ⟨H', G', _⟩,
      rw [add_comm],
      tauto,
    }
  }
end

lemma multiset_split_le {C D F : multiset α}
(h : F ≤ C + D) : ∃ G H : multiset α, G ≤ C ∧ H ≤ D ∧ F = G + H :=
begin
  exact multiset_split_le' C D h
end