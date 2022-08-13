import data.fintype.basic order.filter.at_top_bot

lemma subseq_ex_frequent_val_of_finite_range
{β : Type} [fintype β]
(s : ℕ → β) :
∃ (b : β), ∀ n : ℕ, ∃ m : ℕ, m ≥ n ∧ s m = b :=
begin
  by_contra,
  push_neg at h,
  choose ns hns using h,
  let n := finset.univ.sup ns,
  have : n ≥ ns (s n) := finset.le_sup (finset.mem_univ (s n)),
  replace := hns (s n) n this,
  exact this rfl,
end

lemma ex_const_subseq_of_finite_range
{β: Type} [fintype β]
(s : ℕ → β) :
∃ (b : β) (φ : ℕ → ℕ),
strict_mono φ ∧
∀ n : ℕ, s (φ n) = b :=
begin
  rcases subseq_ex_frequent_val_of_finite_range s
    with ⟨b, hb⟩,
  refine ⟨b, _⟩,
  convert filter.extraction_of_frequently_at_top' _,
  rotate,
  {exact λ n, s n = b},
  rotate,
  {refl},
  intro n,
  rcases hb n.succ with ⟨m, hge, heq⟩,
  exact ⟨m, (nat.lt_of_succ_le hge), heq⟩,
end

lemma ex_const_mem_subseq_of_setvalued_seq
{β : Type} [fintype β]
{s : ℕ → finset β}
(hs : ∀ n : ℕ, (s n).nonempty) :
∃ (b : β) (φ : ℕ → ℕ),
strict_mono φ ∧
∀ n : ℕ, b ∈ s (φ n) :=
begin
  choose s' hs' using hs,
  rcases ex_const_subseq_of_finite_range s'
    with ⟨b, φ, hmon, heq⟩,
  refine ⟨b, φ, hmon, _⟩,
  intro n,
  rw [←heq n],
  exact hs' (φ n),
end
