import data.finset.basic data.fintype.basic multiset

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

lemma finset_image_eq_set_image {α β: Type} (f : α → β)
(s : finset α) : f '' s = finset.image f s :=
begin
    ext, split,
    {
      intro hx,
      rcases hx with ⟨px, ⟨hpx, rfl⟩⟩,
      apply finset.mem_coe.mpr,
      apply finset.mem_image.mpr,
      refine ⟨px, hpx, rfl⟩,
    },
    {
      intro hx,
      replace hx := finset.mem_coe.mp hx,
      rcases finset.mem_image.mp hx with ⟨px, hpx, rfl⟩,
      refine ⟨px, hpx, rfl⟩,
    },
end

lemma set_range_eq_finset_range {α β : Type} [fintype α] (f : α → β) :
set.range f = finset.image f finset.univ :=
begin
  rw [←set.image_univ, ←finset.coe_univ],
  apply finset_image_eq_set_image,
end

lemma finset_exists_subset_of_subset_image {α β: Type}
{s : finset α} {t : finset β} {f : α → β} (h : t ⊆ finset.image f s) :
∃ u : finset α, u ⊆ s ∧ finset.image f u = t :=
begin
  replace h := finset.val_le_iff.mpr h,
  simp only [finset.image, multiset.to_finset_val _] at h,
  replace h := le_trans h (multiset.dedup_le _),
  rcases multiset_exists_of_le_map h with ⟨m, hm, htval⟩,
  refine ⟨m.to_finset, _, _⟩,
  {
    intros x hx,
    simp only [multiset.mem_to_finset] at hx,
    exact (multiset.subset_of_le hm) hx,
  },
  {
    simp only [finset.image],
    apply finset.val_inj.mp,
    simp only [multiset.to_finset_val _],
    rw [←htval, multiset.dedup_map_dedup_eq],
    rw [htval],
    apply multiset.nodup.dedup,
    apply finset.nodup,
  }
end


lemma ex_finset_argmax {α : Type} (f : α → ℝ) {s : finset α} (hs : s.nonempty) :
∃ a ∈ s, ∀ b ∈ s, f a ≥ f b :=
begin
  have hsval : s.val ≠ 0,
  {
    intro h,
    rcases hs with ⟨x, hx⟩,
    simpa only [finset.mem_def, h] using hx,
  },
  rcases ex_multiset_argmax f hsval with ⟨a, ha, hp⟩,
  exact ⟨a, ha, hp⟩,
end