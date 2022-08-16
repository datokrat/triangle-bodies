import data.real.basic

lemma div_le_div_of_le_right {a b c : ℝ}
(h : a ≤ b) (hc : c ≥ 0) : a / c ≤ b / c :=
begin
  rw [←sub_nonneg, ←sub_div],
  rw [←sub_nonneg] at h,
  apply div_nonneg,
  all_goals {assumption},
end

lemma ge_sub_abs (a b : ℝ) :
a ≥ b - |a - b| :=
begin
  simp only [ge_iff_le],
  rw [←sub_nonneg, sub_sub_eq_add_sub, add_sub_right_comm, add_comm],
  rw [←neg_sub, abs_neg, ←sub_eq_add_neg, sub_nonneg],
  simp only [le_abs_self],
end

lemma le_add_abs (a b : ℝ) :
a ≤ b + |a - b| :=
begin
  rw [←sub_nonneg, add_sub_right_comm, ←neg_sub],
  rw [←sub_eq_neg_add, sub_nonneg],
  simp only [le_abs_self],
end

lemma dividend_pos {a b : ℝ} :
a / b > 0 → b ≥ 0 → a > 0 :=
begin
  intros h₁ h₂,
  simp only [gt_iff_lt, div_pos_iff] at h₁,
  cases h₁,
  all_goals {linarith},
end

lemma double_pos {a : ℝ} (h : a > 0) : 2 * a > 0 :=
begin
  simp only [gt_iff_lt, zero_lt_mul_left, zero_lt_bit0, zero_lt_one],
  exact h,
end

lemma double_ne_zero {a : ℝ} (h : a ≠ 0) : 2 * a ≠ 0 :=
begin
  simp only [mul_ne_zero_iff],
  simp only [ne.def, bit0_eq_zero, one_ne_zero, not_false_iff, true_and],
  exact h,
end