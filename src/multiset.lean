import data.multiset.basic data.real.basic
import tactic.wlog

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

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

def multiset_all {α : Type} (p : α → Prop) (C : multiset α) : Prop :=
∀ a : α, a ∈ C → p a

lemma ex_multiset_argmax {α : Type} (f : α → ℝ) {m : multiset α} (hm : m ≠ 0) :
∃ a ∈ m, ∀ b ∈ m, f a ≥ f b :=
begin
  induction m using pauls_multiset_induction,
  {contradiction},
  {
    by_cases hz : m_C' = 0,
    {
      rw [hz],
      refine ⟨m_a, multiset.mem_cons_self _ _, _⟩,
      simp only [multiset.mem_cons, multiset.not_mem_zero, or_false,
        ge_iff_le, forall_eq],
    },
    {
      rcases m_ᾰ hz with ⟨z, ⟨zmem, zprop⟩⟩,
      by_cases hle : f z ≤ f m_a,
      {
        refine ⟨m_a, multiset.mem_cons_self _ _, _⟩,
        intros b hb,
        rcases multiset.mem_cons.mp hb with ⟨-, -⟩,
        {apply le_refl},
        {exact le_trans (zprop b h) hle},
      },
      {
        refine ⟨z, multiset.mem_cons_of_mem zmem, _⟩,
        intros b hb,
        rcases multiset.mem_cons.mp hb with ⟨-, -⟩,
        {apply le_of_not_ge hle},
        {exact zprop b h},
      },
    },
  },
end


lemma multiset_exists_of_le_map {α β : Type} {f : α → β} {b : multiset β} {l : multiset α} :
b ≤ multiset.map f l → ∃ as : multiset α, as ≤ l ∧ multiset.map f as = b :=
begin
  induction b,
  begin
    induction b generalizing l,
    begin
      simp,
    end,
    begin
      intro h,
      simp only [multiset.quot_mk_to_coe''] at *,
      rw [←multiset.cons_coe] at *,
      have := multiset.mem_of_le h (multiset.mem_cons_self b_hd b_tl),
      simp only [multiset.mem_map] at this,
      rcases this with ⟨a, ⟨a_mem_l, a_to_b_hd⟩⟩,
      rcases (multiset.exists_cons_of_mem a_mem_l) with ⟨l_tl, rfl⟩,
      simp only [multiset.map_cons, a_to_b_hd] at h,
      have := multiset.erase_le_erase b_hd h,
      simp only [multiset.erase_cons_head] at this,
      rcases b_ih this with ⟨as_tl, ⟨hle, heq⟩⟩,
      apply exists.intro (a ::ₘ as_tl),
      simp only [multiset.cons_le_cons_iff, hle, multiset.map_cons, a_to_b_hd],
      simp [multiset.cons_eq_cons, heq],
    end,
  end,
  begin
    simp,
  end
end