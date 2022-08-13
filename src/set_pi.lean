import data.set.basic analysis.inner_product_space.basic

open_locale pointwise

variables {V : Type} [inner_product_space ℝ V]

lemma set_image_sub' {α : Type} {t : set α} (f : α → V) (v : V):
(f - function.const _ v) '' t = f '' t - {v} :=
begin
  ext,
  simp only [set.mem_sub, set.mem_image_eq, pi.sub_apply],
  split,
  all_goals {
    rintro,
    cases_matching* [_ ∨ _, _ ∧ _, _ = _, Exists _],
    tauto,
  },
end

lemma set_image_translate {α : Type} {t : set α} (f : α → V) (v : V) :
(λ x, f x + v) '' t = f '' t + {v} :=
begin
  ext,
  simp only [set.mem_add, set.mem_image_eq, pi.add_apply],
  split,
  all_goals {
    rintro,
    cases_matching* [_ ∨ _, _ ∧ _, _ = _, Exists _],
    tauto,
  },
end


lemma set_image_smul' {α : Type} {t : set α} {a : ℝ} (f : α → V) :
(a • f) '' t = a • (f '' t) :=
begin
  have : a • f = (λ x, a • x) ∘ f,
  {
    funext,
    simp only [pi.smul_apply],
  },
  rw [this],
  rw [set.image_comp _ f t],
  ext, split,
  all_goals {
    intro hx,
    rcases (set.mem_image _ _ _).mp hx with ⟨px, hpx, rfl⟩,
    refine (set.mem_image _ _ _).mpr ⟨px, hpx, rfl⟩,
  },
end

lemma set_mem_sub_eq {α : Type} [has_sub α] {s t : set α} {a : α} :
a ∈ s - t = ∃ (x y : α), x ∈ s ∧ y ∈ t ∧ x - y = a :=
begin
  ext,
  exact set.mem_sub,
end

lemma set_vsub_eq_sub {s t : set V} :
s -ᵥ t = s - t := rfl