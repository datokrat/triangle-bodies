import data.multiset.basic data.real.basic
  analysis.inner_product_space.basic
  data.multiset.fintype
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

lemma multiset.card_induction {α: Type} {β : α → Type} {p : Π {a : α}, multiset (β a) → Prop} {a : α} (C : multiset (β a)) :
(∀ {b : α} (D : multiset (β b)), (∀ {c : α} (E : multiset (β c)), E.card < D.card → p E) → p D) → p C :=
begin
  intro ps,
  generalize hn : C.card = n,
  replace hn : C.card ≤ n := le_of_eq hn,
  induction n with n ih generalizing C a,
  {
    rw [nat.le_zero_iff, multiset.card_eq_zero] at hn,
    rcases hn with rfl,
    apply ps,
    simp only [multiset.card_zero, not_lt_zero', is_empty.forall_iff, forall_const],
    tauto,
  },
  {
    apply (ps C),
    intros b E hE,
    apply ih,
    apply nat.le_of_lt_succ,
    exact lt_of_lt_of_le hE hn,
  },
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


lemma ex_maximal_multiset {α : Type} {p : multiset α → Prop}
{C D : multiset α}
(hDC : D ≤ C) (pD : p D) :
∃ F : multiset α, F ≤ C ∧ p F ∧
∀ G : multiset α, F ≤ G → G ≤ C → p G → F = G :=
begin
  simp only [multiset.le_iff_exists_add] at hDC,
  rcases hDC with ⟨D', rfl⟩,
  let q : ℕ → Prop := λ k, ∃ F : multiset α, F.card + k = (D.card + D'.card) ∧ D ≤ F ∧ F ≤ D + D' ∧ p F,
  have ex : ∃ k : ℕ, q k,
  {
    refine ⟨D'.card, D, rfl, le_refl D, multiset.le_add_right _ _, pD⟩,
  },
  let k := nat.find ex,
  rcases nat.find_spec ex with ⟨F, hk, leF, Fle, pF⟩,
  refine ⟨F, Fle, pF, _⟩,
  intros G hFG Gle pG,
  let l := D.card + D'.card - G.card,
  have hl : G.card + l = D.card + D'.card,
  {
    simp only [l, ←multiset.card_add D D'],
    rw [add_tsub_cancel_of_le (multiset.card_mono Gle)],
  },
  have ql : q l := ⟨G, hl, le_trans leF hFG, Gle, pG⟩,
  have : k ≤ l := nat.find_min' ex ql,
  simp only [←hk] at hl,
  replace this := add_le_add_left this G.card,
  rw [hl] at this,
  simp only [k, add_le_add_iff_right] at this,
  exact multiset.eq_of_le_of_card_le hFG this,
end

lemma ex_minimal_multiset {α : Type} {p : multiset α → Prop}
{C D : multiset α}
(hDC : D ≤ C) (pD : p D) :
∃ F : multiset α, F ≤ C ∧ p F ∧
∀ G : multiset α, G ≤ F → p G → F = G :=
begin
  simp only [multiset.le_iff_exists_add] at hDC,
  rcases hDC with ⟨D', rfl⟩,
  let q : ℕ → Prop := λ k, ∃ F : multiset α, F.card = k ∧ F ≤ D ∧ p F,
  have ex : ∃ k : ℕ, q k,
  {
    refine ⟨D.card, D, rfl, le_refl D, pD⟩,
  },
  let k := nat.find ex,
  rcases nat.find_spec ex with ⟨F, hk, Fle, pF⟩,
  refine ⟨F, le_trans Fle (multiset.le_add_right _ _), pF, _⟩,
  intros G Gle pG,
  let l := G.card,
  have ql : q l := ⟨G, rfl, le_trans Gle Fle, pG⟩,
  have : k ≤ l := nat.find_min' ex ql,
  symmetry,
  simp only [k, ←hk] at this,
  exact multiset.eq_of_le_of_card_le Gle this,
end



lemma sum_multiset_le {V : Type} [inner_product_space ℝ V]
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
(h : multiset_all (λ W, W ≤ E) C) :
C.sum ≤ E :=
begin
  induction C using multiset.induction,
  {simp only [multiset.sum_zero, submodule.zero_eq_bot, bot_le]},
  {
    simp only [multiset.sum_cons, submodule.add_eq_sup, sup_le_iff],
    split,
    {
      refine h C_a _,
      simp only [multiset.mem_cons_self],
    },
    {
      refine C_ᾰ _,
      intros W hW,
      refine h W _,
      simp only [hW, multiset.mem_cons, or_true],
    },
  },
end

lemma le_sum_multiset_of_mem {V : Type} [inner_product_space ℝ V]
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
(h : E ∈ C) :
E ≤ C.sum :=
begin
  rcases multiset.exists_cons_of_mem h with ⟨D, rfl⟩,
  simp only [multiset.sum_cons, submodule.add_eq_sup, le_sup_left],
end

lemma multiset_sum_mono {V α: Type} [inner_product_space ℝ V]
{C : multiset α}
{f g : α → submodule ℝ V}
(h : f ≤ g) : (C.map f).sum ≤ (C.map g).sum :=
begin
  induction C using pauls_multiset_induction,
  {
    simp only [multiset.map_zero, multiset.sum_zero, submodule.zero_eq_bot, le_bot_iff],
  },
  {
    simp only [multiset.map_cons, multiset.sum_cons, submodule.add_eq_sup, sup_le_iff],
    split,
    {
      exact le_trans (h C_a) le_sup_left,
    },
    {
      exact le_trans C_ᾰ le_sup_right,
    },
  },
end


lemma map_lambda
{α β : Type}
(f : α → β) (C : multiset α) :
C.map f = C.map (λ x, f x) := rfl

lemma cons_erase_cons {α : Type}
(C D: multiset α) (a : α) :
a ::ₘ C - a ::ₘ D = C - D :=
begin
  simp only [multiset.sub_cons, multiset.erase_cons_head],
end

lemma dite_true {α : Type} {p : Prop} (h : p) (ft : p → α) (ff : ¬p → α) :
dite p ft ff = ft h :=
begin
  have : ft = λ h', ft h,
  {
    funext, refl,
  },
  rw [this],
  apply dite_eq_left_iff.mpr,
  intro hc,
  have := hc h,
  contradiction,
end

lemma dite_false {α : Type} {p : Prop} (h : ¬p) (ft : p → α) (ff : ¬p → α) :
dite p ft ff = ff h :=
begin
  have : ff = λ h', ff h := rfl,
  rw [this],
  apply dite_eq_right_iff.mpr,
  intro hc,
  have := h hc,
  contradiction,
end

noncomputable def multiset.add_to_enum_finset {α : Type}
(C D : multiset α) :
(C + D).to_enum_finset ≃ C.to_enum_finset ⊕ D.to_enum_finset :=
begin
  refine ⟨_, _, _, _⟩,
  {
    intro x,
    by_cases h : x.val.snd < C.count x.val.fst,
    {
      left,
      refine ⟨x.val, _⟩,
      simp only [multiset.mem_to_enum_finset],
      exact h,
    },
    {
      right,
      refine ⟨⟨x.val.fst, x.val.snd - C.count x.val.fst⟩, _⟩,
      push_neg at h,
      have := x.property,
      simp only [multiset.mem_to_enum_finset] at this ⊢,
      simp only [multiset.count_add] at this,
      rcases nat.exists_eq_add_of_le h with ⟨l, hl⟩,
      rw [hl, add_tsub_cancel_left],
      zify at *,
      linarith,
    },
  },
  {
    intro x,
    rcases x with x | x,
    {
      refine ⟨x.val, _⟩,
      have := x.property,
      simp only [multiset.mem_to_enum_finset] at this ⊢,
      refine lt_of_lt_of_le this _,
      apply multiset.count_le_of_le,
      simp only [le_add_iff_nonneg_right, zero_le],
    },
    {
      refine ⟨⟨x.val.fst, x.val.snd + C.count x.val.fst⟩, _⟩,
      have := x.property,
      simp only [multiset.mem_to_enum_finset] at this ⊢,
      simp only [multiset.count_add],
      conv {to_lhs, rw [add_comm]},
      simp only [subtype.val_eq_coe, add_lt_add_iff_left],
      exact this,
    },
  },
  {
    simp only [function.left_inverse_iff_comp],
    funext x,
    simp only [function.comp_app, id.def],
    by_cases h : x.val.snd < multiset.count x.val.fst C,
    {
      rw [dite_true h],
      simp only [subtype.val_eq_coe, finset.mk_coe],
    },
    {
      rw [dite_false h],
      push_neg at h,
      simp only [nat.sub_add_cancel h],
      simp only [subtype.val_eq_coe, prod.mk.eta, finset.mk_coe],
    },
  },
  {
    simp only [function.right_inverse_iff_comp],
    funext x,
    cases x,
    {
      have := x.property,
      simp only [subtype.val_eq_coe, subtype.coe_mk, not_lt, function.comp_app, finset.mk_coe, id.def, dite_eq_left_iff] at this ⊢,
      simp only [multiset.mem_to_enum_finset] at this,
      intro hc,
      linarith,
    },
    {
      have := x.property,
      simp only [multiset.mem_to_enum_finset] at this,
      simp only [subtype.val_eq_coe, subtype.coe_mk, add_lt_iff_neg_right, not_lt_zero', not_false_iff, function.comp_app,
      add_tsub_cancel_right, prod.mk.eta, finset.mk_coe, dif_neg, id.def] at this ⊢,
    },
  },
end

noncomputable def multiset.glue_enum_fns {α β : Type}
{C D : multiset α}
(fC : C.to_enum_finset → β) (fD : D.to_enum_finset → β) :
(C + D).to_enum_finset → β :=
begin
  intro x,
  cases multiset.add_to_enum_finset C D x with k k,
  {
    exact fC k,
  },
  {
    exact fD k,
  },
end

@[simp]
lemma multiset.zero_to_enum_finset {α : Type} :
(0 : multiset α).to_enum_finset = ∅ :=
begin
  rw [←finset.card_eq_zero],
  rw [multiset.card_to_enum_finset, multiset.card_zero],
end

lemma multiset.exists_elementwise_preimage {α β : Type}
(C : multiset α) (f : β → α) (h : ∀ a : α, a ∈ C → a ∈ set.range f) :
∃ D : multiset β, D.map f = C :=
begin
  induction C using pauls_multiset_induction with C a ih,
  {
    simp only [multiset.map_eq_zero, exists_apply_eq_apply],
  },
  {
    obtain ⟨b, rfl⟩ := h a (multiset.mem_cons_self _ _),
    obtain ⟨D, hD⟩ := ih _, rotate,
    {
      intros a aC,
      exact h a (multiset.mem_cons_of_mem aC),
    },
    refine ⟨b ::ₘ D, _⟩,
    simpa only [multiset.map_cons, multiset.cons_inj_right] using hD,
  },
end

@[simp]
lemma multiset_all_zero {α : Type} {p : α → Prop} :
multiset_all p (0 : multiset α) = true :=
begin
  simp only [multiset_all, multiset.not_mem_zero, is_empty.forall_iff, implies_true_iff],
end

@[simp]
lemma multiset.zero_eq_map {α β : Type} {s : multiset α} {f : α → β} :
0 = s.map f ↔ s = 0 :=
begin
  split,
  {intro h, replace h := h.symm, simpa only [multiset.map_eq_zero] using h},
  {intro h, simp only [*, multiset.map_zero]},
end

lemma multiset.exists_join' {α β γ : Type} {f : α → γ} {g : β → γ}
{C : multiset α} {D : multiset β} (h : C.map f = D.map g) :
∃ E : multiset ({pr : α × β // f pr.fst = g pr.snd}),
E.map (λ pr, pr.val.fst) = C ∧ E.map (λ pr, pr.val.snd) = D :=
begin
  revert D,
  induction C using pauls_multiset_induction with C a ih,
  {
    intros D h,
    simp only [multiset.map_eq_zero, exists_eq_left, multiset.map_zero],
    simp only [multiset.map_zero, multiset.zero_eq_map] at h,
    simp only [h, eq_self_iff_true, true_and, multiset_all_zero],
  },
  {
    intros D h,
    simp only [multiset.map_cons] at h,
    have : f a ∈ D.map g := h ▸ multiset.mem_cons_self (f a) (C.map f),
    rw [multiset.mem_map] at this,
    obtain ⟨b, bD, hd⟩ := this,
    obtain ⟨D, rfl⟩ := multiset.exists_cons_of_mem bD,
    simp only [multiset.map_cons, hd, multiset.cons_inj_right] at h,
    obtain ⟨E, hE⟩ := ih h,
    refine ⟨⟨⟨a, b⟩, _⟩ ::ₘ E, _⟩,
    {simp only [hd]},
    {
      simp only [subtype.val_eq_coe, multiset.map_cons, subtype.coe_mk, multiset.cons_inj_right],
      exact hE,
    },
  },
end

lemma multiset.exists_join {α β γ : Type} {f : α → γ} {g : β → γ}
{C : multiset α} {D : multiset β} (h : C.map f = D.map g) :
∃ E : multiset (α × β), E.map prod.fst = C ∧ E.map prod.snd = D ∧
multiset_all (λ x : α × β, f x.fst = g x.snd) E :=
begin
  revert D,
  induction C using pauls_multiset_induction with C a ih,
  {
    intros D h,
    simp only [multiset.map_eq_zero, exists_eq_left, multiset.map_zero],
    simp only [multiset.map_zero, multiset.zero_eq_map] at h,
    simp only [h, eq_self_iff_true, true_and, multiset_all_zero],
  },
  {
    intros D h,
    simp only [multiset.map_cons] at h,
    have : f a ∈ D.map g := h ▸ multiset.mem_cons_self (f a) (C.map f),
    rw [multiset.mem_map] at this,
    obtain ⟨b, bD, hd⟩ := this,
    obtain ⟨D, rfl⟩ := multiset.exists_cons_of_mem bD,
    simp only [multiset.map_cons, hd, multiset.cons_inj_right] at h,
    obtain ⟨E, hE⟩ := ih h,
    refine ⟨⟨a, b⟩ ::ₘ E, _⟩,
    simp only [hE, multiset_all, multiset.map_cons, eq_self_iff_true, multiset.mem_cons, prod.forall, prod.mk.inj_iff, true_and],
    rintro a' b' (⟨rfl, rfl⟩ | h),
    {exact hd.symm},
    {simp only [multiset_all, prod.forall] at hE, tauto},
  },
end

@[simp]
lemma multiset.sum_linear_map
{V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]
{W : Type} [inner_product_space ℝ W] [finite_dimensional ℝ W]
(C : multiset (submodule ℝ V)) (f : V →ₗ[ℝ] W) :
submodule.map f C.sum = (C.map (submodule.map f)).sum :=
begin
  induction C using pauls_multiset_induction,
  {
    simp only [multiset.map_zero, multiset.sum_zero, submodule.zero_eq_bot, submodule.map_bot],
  },
  {
    simp only [*, multiset.map_cons, multiset.sum_cons, submodule.add_eq_sup, submodule.map_sup],
  },
end

lemma dim_add_le_dim_add_dim' {V : Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]
{U W : submodule ℝ V} :
finite_dimensional.finrank ℝ (U + W : submodule ℝ V) ≤ finite_dimensional.finrank ℝ U + finite_dimensional.finrank ℝ W :=
begin
  have := dim_add_le_dim_add_dim U W,
  simp only [←finite_dimensional.finrank_eq_dim] at this,
  rw [←cardinal.nat_cast_le, nat.cast_add],
  exact this,
end

lemma multiset.dim_sum_le_sum_dim {V : Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]
(C : multiset (submodule ℝ V)) :
finite_dimensional.finrank ℝ C.sum ≤ (C.map (λ W : submodule ℝ V, finite_dimensional.finrank ℝ W)).sum :=
begin
  induction C using pauls_multiset_induction with C W ih,
  {
    simp only [multiset.map_zero, multiset.sum_zero, le_zero_iff, finrank_eq_zero, submodule.zero_eq_bot],
  },
  {
    rw [multiset.map_cons, multiset.sum_cons, multiset.sum_cons],
    refine le_trans _ (add_le_add_left ih _),
    apply dim_add_le_dim_add_dim',
  },
end

lemma multiset.sum_one {C : multiset ℕ}
(h : multiset_all (λ n, n = 1) C) :
C.sum = C.card :=
begin
  induction C using pauls_multiset_induction with C n ih,
  {
    simp only [multiset.sum_zero, multiset.card_zero],
  },
  {
    simp only [multiset.sum_cons, multiset.card_cons],
    replace ih := ih (λ n hn, h n (multiset.mem_cons_of_mem hn)),
    rw [ih, h n (multiset.mem_cons_self _ _)],
    ac_refl,
  },
end

lemma multiset.all_map {α β: Type} {C : multiset α}
(f : α → β) (p : β → Prop) :
multiset_all p (C.map f) ↔ multiset_all (p ∘ f) C :=
begin
  simp only [multiset_all, multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
end

lemma multiset.all_of_le {α : Type} {C D : multiset α} {p : α → Prop}
(CD : C ≤ D) :
multiset_all p D → multiset_all p C :=
begin
  simp only [multiset_all],
  intros h a aC,
  exact h a ((multiset.subset_of_le CD) aC),
end

@[simp]
lemma multiset.all_add {α : Type} {C D : multiset α} {p : α → Prop} :
multiset_all p (C + D) ↔ multiset_all p C ∧ multiset_all p D :=
begin
  simp only [multiset_all, multiset.mem_add],
  split,
  {exact λ h, ⟨λ a aC, h a (or.inl aC), λ a aC, h a (or.inr aC)⟩},
  {tauto},
end