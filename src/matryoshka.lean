import convex convex_body linalg measure touching_cone brunn_minkowski
  microid criticality
  analysis.convex.basic
  data.multiset.basic
  measure_theory.measure.measure_space
  topology.basic
  analysis.inner_product_space.pi_L2

open_locale pointwise
open_locale ennreal -- for ∞ notation
open_locale topological_space -- for 𝓝 notation

-- needed to get decidable_eq for sets!
open classical
local attribute [instance] prop_decidable

section definitions

variables (V : Type)
[inner_product_space ℝ V] [finite_dimensional ℝ V]


lemma ex_maximal_multiset {α : Type} {p : multiset α → Prop}
{C D : multiset α}
(hDC : D ≤ C) (h : p D) :
∃ F : multiset α, F ≤ C ∧ p F ∧
∀ G : multiset α, F ≤ G → G ≤ C → p G → F = G := sorry

lemma ex_minimal_multiset {α : Type} {p : multiset α → Prop}
{C D : multiset α}
(hDC : D ≤ C) (h : p D) :
∃ F : multiset α, F ≤ C ∧ p F ∧
∀ G : multiset α, G ≤ F → p G → F = G := sorry

end definitions

section preparation_lemmas

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def map_generator {k : ℕ} (G : microid_generator_space V k)
(E : submodule ℝ V) : microid_generator_space E k := sorry

def project_microid_measure {k : ℕ} (E : submodule ℝ V) (μ : microid_measure V k) :
microid_measure E k := sorry

lemma microid_orthogonal_projection {k : ℕ} {E : submodule ℝ V} {u : V}
(μ : microid_measure V k) (uE : u ∈ E) :
project_set E (microid_of_measure μ).val = (microid_of_measure
(project_microid_measure E μ)).val := sorry

noncomputable def TS_microid_measure {k : ℕ} (u : metric.sphere (0 : V) 1) (μ : microid_measure V k) :
submodule ℝ V :=
TS (microid_of_measure μ).val u.val

def dirac_microid_measure {k : ℕ}
(P : microid_generator_space V k) : microid_measure V k := sorry

end preparation_lemmas


section default_reduction

variables {V : Type} [inner_product_space ℝ V] [finite_dimensional ℝ V]

def microid_pair (k : ℕ)
(u : metric.sphere (0 : V) 1) :=
(Σ μ : microid_measure V k,
{P : microid_generator_space V k // is_default_polytope μ u P})

def pair_to_default_body {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : convex_body V :=
polytope_to_convex_body (polytope_of_microid_generator pair.2.1)

def pair_to_measure {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair: microid_pair k u) : microid_measure V k := pair.1

def pair_to_microid {k : ℕ}
{u : metric.sphere (0 : V) 1} :
microid_pair k u → convex_body V :=
microid_of_measure ∘ pair_to_measure

def pair_to_default_measure {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : microid_measure V k :=
dirac_microid_measure pair.2.1

noncomputable def pair_to_TS {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V :=
TS (microid_of_measure (pair_to_measure pair)).val u

lemma proj_microid_of_measure {k : ℕ}
(E : submodule ℝ V)
(μ : microid_measure V k) :
proj_body E (microid_of_measure μ) = microid_of_measure (project_microid_measure E μ) :=
sorry

def reduce_pair {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : microid_pair k u :=
⟨pair_to_default_measure pair, ⟨pair.2.1, sorry⟩⟩

lemma reduced_microid_subset_TS {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
(pair_to_microid (reduce_pair pair)).val ⊆ pair_to_TS (reduce_pair pair) := sorry

lemma reduced_microid_eq_default_body {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
(pair_to_microid (reduce_pair pair)) = pair_to_default_body pair := sorry

lemma span_reduced_microid_eq_TS {k : ℕ}
{u : metric.sphere (0 : V) 1} :
span_of_convex_body ∘ pair_to_microid ∘ (reduce_pair : microid_pair k u → microid_pair k u) =
pair_to_TS ∘ (reduce_pair : microid_pair k u → microid_pair k u) := sorry

noncomputable def pair_to_default_space {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V :=
TS (pair_to_default_body pair).val u.val

lemma default_space_eq_TS_of_reduced {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
pair_to_default_space (reduce_pair pair) = pair_to_TS (reduce_pair pair) :=
sorry

lemma TS_reduce_eq_default_space {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) :
pair_to_TS (reduce_pair pair) = pair_to_default_space pair :=
sorry

noncomputable def pair_to_space_pair {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V × submodule ℝ V :=
⟨pair_to_TS pair, pair_to_default_space pair⟩

lemma pair_to_space_pair_def {k : ℕ}
{u : metric.sphere (0 : V) 1} :
@pair_to_space_pair V _ _ k u = λ pair, ⟨pair_to_TS pair, pair_to_default_space pair⟩ :=
sorry

noncomputable def paircol_span {k : ℕ}
{u : metric.sphere (0 : V) 1}
(D : multiset (microid_pair k u)) : submodule ℝ V :=
(D.map pair_to_default_space).sum

lemma exists_pair_multiset {k : ℕ}
(μs : multiset (microid_measure V k))
(u : metric.sphere (0 : V) 1)
(hTS : semicritical_spaces (μs.map (TS_microid_measure u))) :
∃ C : multiset (microid_pair k u),
C.map pair_to_measure = μs := sorry

theorem matryoshka_reduction {k : ℕ}
{u : metric.sphere (0 : V) 1}
{D F : multiset (microid_pair k u)}
(hdim : dim V = F.card + 1) :
u ∈ msupport (bm.area ((D.map pair_to_default_body) + (F - D).map pair_to_microid)) →
u ∈ msupport (bm.area (F.map pair_to_microid))
:=
sorry

end default_reduction

variables {V : Type}
[inner_product_space ℝ V] [finite_dimensional ℝ V]

lemma sum_multiset_le
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

lemma le_sum_multiset_of_mem
{C : multiset (submodule ℝ V)}
{E : submodule ℝ V}
(h : E ∈ C) :
E ≤ C.sum := sorry

lemma semicritical_spaces_factorization
(C D : multiset (submodule ℝ V))
{E : submodule ℝ V}
(hC : dim E = C.card ∧ multiset_all (λ W, W ≤ E) C)
(hCD : semicritical_spaces (C + D)) :
semicritical_spaces (D.map (λ W, W.map (proj Eᗮ))) := sorry

lemma microid_proj_eq_proj_microid {k : ℕ}
(μ : microid_measure V k)
(E : submodule ℝ V) :
microid_of_measure (project_microid_measure E μ) = proj_body E (microid_of_measure μ) :=
sorry

lemma TS_microid_proj_eq_proj_TS_microid {k : ℕ}
(μ : microid_measure V k)
(E : submodule ℝ V)
(u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) :
TS_microid_measure (uncoe_sph E u uE) (project_microid_measure E μ) =
(TS_microid_measure u μ).map (proj E) :=
begin
  simp only [TS_microid_measure, uncoe_sph],
  rw [TS_orthogonal_projection _ uE, microid_proj_eq_proj_microid],
  simp only [proj_body, subtype.val_eq_coe],
  refl,
end

lemma TS_default_body_eq_TS_default_measure (k : ℕ)
(u : metric.sphere (0 : V) 1) (x : microid_pair k u) :
TS (pair_to_default_body x).val u.val = TS_microid_measure u (pair_to_default_measure x) :=
sorry

section blabb

lemma u_mem_sum_TS_orth
{k : ℕ}
{u : metric.sphere (0 : V) 1}
{E : submodule ℝ V}
(A : multiset (microid_pair k u))
(h : E = (A.map pair_to_TS).sum) :
u.val ∈ Eᗮ := sorry

lemma semicritical_subprojection
{k : ℕ}
{u : metric.sphere (0 : V) 1}
(A B : multiset (microid_pair k u))
(E : submodule ℝ V)
(SP : multiset (microid_measure Eᗮ k))
(hAE : E = (A.map pair_to_TS).sum)
(hA1 : multiset_all (λ x, pair_to_default_space x = pair_to_TS x) A)
(hA2 : dim E = A.card)
(hB : semicritical_spaces ((A + B).map pair_to_TS))
(hSP : SP = B.map (project_microid_measure Eᗮ ∘ pair_to_measure)):
semicritical_spaces
(SP.map (TS_microid_measure (uncoe_sph Eᗮ u (u_mem_sum_TS_orth A hAE)))) := sorry

end blabb

lemma coe_uncoe_sph {E : submodule ℝ V}
(u : metric.sphere (0 : V) 1)
(uE : u.val ∈ E) :
coe_sph E (uncoe_sph E u uE) = u := sorry

--set_option pp.implicit true
theorem matryoshka_principle {k : ℕ}
(n₀ : ℕ)
(n : ℕ)
(hn : n ≤ n₀)
(μs : multiset (microid_measure V k))
(u : metric.sphere (0 : V) 1)
--(hdim1 : n ≥ 1)
(hdim2 : dim V = n + 1)
(hdim3 : μs.card = n)
(hTS : semicritical_spaces (μs.map (TS_microid_measure u))) :
u ∈ msupport (bm.area (μs.map microid_of_measure)) :=
begin
  unfreezingI {
    induction n₀ with n₀ ih generalizing n μs V,
    {
      have : μs = ∅ := sorry,
      rw [this],
      simp only [multiset.empty_eq_zero, multiset.map_zero, bm.area_empty],
    },
    {
      rcases exists_pair_multiset μs u hTS with
        ⟨C, rfl⟩,
      let D := C.map pair_to_space_pair,
      let uperp := vector_orth u.val,
      have :=
      begin
        clear ih,
        refine semicritical_switching D uperp _ _ _ _,
        {
          simpa only [multiset.map_map] using hTS,
        },
        {
          have dim_uperp : dim uperp = n,
          {
            suffices h : dim uperp + 1 = dim V,
            {
              rw [hdim2] at h,
              exact nat.add_right_cancel h,
            },
            {
              have : dim (submodule.span ℝ ({u} : set V)) = 1,
              {
                apply finrank_span_singleton,
                have := metric.mem_sphere.mp u.prop,
                have z_ne_o: 1 ≠ (0 : ℝ) := zero_ne_one.symm,
                rw [←this] at z_ne_o,
                apply dist_ne_zero.mp z_ne_o,
              },
              rw [←this],
              rw [nat.add_comm],
              refine dim_add_dim_orthogonal _,
            },
          },
          symmetry,
          simpa only [dim_uperp, multiset.card_map] using hdim3,
        },
        {
          clear hn hdim2 hdim3 hTS,
          intros x xD,
          rcases multiset.mem_map.mp xD with ⟨c, ⟨cC, rfl⟩⟩,
          simp only [pair_to_space_pair],
          split,
          {apply TS_le_uperp},
          {
            simp only [pair_to_default_space, pair_to_default_body, submodule.span_le],
            apply TS_le_uperp,
/-          simp only [polytope_to_convex_body],
            have is_default_poly := c.snd.2,
            exact is_default_poly.1, --simp only [is_default_polytope] at is_default_poly, -/
          },
        },
        {
          intros x xD,
          rcases multiset.mem_map.mp xD with ⟨c, ⟨cC, rfl⟩⟩,
          simp only [pair_to_space_pair, pair_to_default_space,
            pair_to_default_body, polytope_to_convex_body],
          have is_default_poly := c.snd.2,
          exact is_default_poly.2.1,
        },
      end,
      rcases this with ⟨A, B, h⟩,
      rcases h with ⟨hAB, hBD, h1, h2, h3⟩,
      rcases multiset_exists_of_le_map hBD with ⟨B', ⟨hB'C, rfl⟩⟩,
      rcases multiset_exists_of_le_map hAB with ⟨A', ⟨hA'B', rfl⟩⟩,
      /- let F := (B' - A').map pair_to_default_measure + (C - B').map pair_to_measure,
      let G := A'.map pair_to_default_measure,
      let E : submodule ℝ V := (A'.map pair_to_default_space).sum,
      have uE : u.val ∈ Eᗮ,
      {
        suffices h : E ≤ uperp,
        {
          simp only [submodule.mem_orthogonal],
          rintro x xE,
          apply inner_left_of_mem_orthogonal_singleton,
          exact h xE,
        },
        {
          refine sum_multiset_le _,
          rintro W hW,
          simp only [pair_to_default_space, multiset.mem_map] at hW,
          rcases hW with ⟨a, hA, rfl⟩,
          apply TS_le_uperp,
        },
      }, -/
      /- let pF := F.map (project_microid_measure Eᗮ),
      let n' := pF.card,
      have hn' : n' ≤ n₀,
      {
        simp only [n', pF, F, multiset.card_map, multiset.card_add
          --, multiset.card_add, multiset.card_sub, hA'B', hB'C
        ],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
        simp only [add_tsub_cancel_left],
        simp only [multiset.card_map, multiset.card_add] at hdim3,
        calc t.card + tt.card = n - A'.card : _
      ...  ≤ n - 1 : _
      ...  ≤ n₀ : _,
        {
          rw [←hdim3],
          admit,
        },
        {
          apply nat.sub_le_sub_left n,
          apply nat.succ_le_of_lt,
          simpa only [multiset.card_map] using h3,
        },
        {
          norm_num,
          assumption,
        },
      },
      have EA' : dim E = A'.card,
      {
        apply le_antisymm,
        {admit},
        {
          simp only [multiset.map_map, pair_to_space_pair] at h1,
          rw [←multiset.card_map pair_to_default_space],
          --simp only [pair_to_default_space] at E,
          refine h1 _ _,
          refine le_trans _ (multiset.le_add_right _ _),
          simp only [function.comp_app],
          exact multiset.map_le_map hA'B',
        }
      },
      have hdim2' : dim Eᗮ = n' + 1,
      {
        apply le_antisymm,
        {
          suffices dimE : dim E ≥ n - n',
          {
            simp only [ge_iff_le, tsub_le_iff_right, eq_tsub_of_add_eq hdim2.symm] at dimE,
            rw [←dim_add_dim_orthogonal E, nat.add_assoc] at dimE,
            norm_num at dimE,
            exact dimE,
          },
          {
            rw [EA'],
            norm_num,
            simp only [hdim3.symm, multiset.card_map],
            simp only [pF, F, n', multiset.card_map, multiset.card_add],

            rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
            rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
            simp only [add_tsub_cancel_left, multiset.card_add],
            simp only [add_assoc],
          },
        },
        {
          suffices dimE : dim E ≤ n - n',
          {
            simp only [ge_iff_le, tsub_le_iff_right, eq_tsub_of_add_eq hdim2.symm] at dimE,
            rw [←dim_add_dim_orthogonal E, tsub_tsub] at dimE,
            admit,
          },
          {
            rw [multiset.map_map, pair_to_space_pair_def, multiset.card_map] at h2,
            rw [h2],
            rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
            rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
            simp only [add_tsub_cancel_left,
                       multiset.card_map, n', pF, F,
                       multiset.card_add,
                       hdim3.symm],
            generalizes [A'.card = A'c, t.card = tc, tt.card = ttc],
            rw [nat.add_assoc],
            simp only [add_tsub_cancel_right],
          },
        },
      },
      have hdim3' : pF.card = n' := rfl,
      let u' := uncoe_sph Eᗮ u uE, -/
      let A := A'.map reduce_pair,
      let B := (B' - A').map reduce_pair + (C - B'),
      let E := (A.map pair_to_TS).sum,
      let SP := B.map (project_microid_measure Eᗮ ∘ pair_to_measure),
      have sc_AB : semicritical_spaces ((A + B).map pair_to_TS),
      {
        have hA : A.map pair_to_TS = A'.map pair_to_default_space,
        {simp only [multiset.map_map, function.comp_app, TS_reduce_eq_default_space]},
        have hB : B.map pair_to_TS = (B' - A').map pair_to_default_space + (C - B').map pair_to_TS,
        {
          simp only [B, multiset.map_map, multiset.map_add, function.comp_app,
            TS_reduce_eq_default_space],
        },
        have hAB : (A + B).map pair_to_TS = B'.map pair_to_default_space + (C - B').map pair_to_TS,
        {
          rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
          rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
          simp only [A, B, add_tsub_cancel_left, multiset.map_map, multiset.map_add,
            function.comp_app, TS_reduce_eq_default_space, add_assoc],
        },
        rw [hAB],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
        simp only [add_tsub_cancel_left] at hAB ⊢,
        simp only [D, pair_to_space_pair_def] at h1,
        simpa only [multiset.map_add, multiset.map_map, add_tsub_cancel_left,
          function.comp_app] using h1,
      },
      have dimE : dim E = A.card,
      {
        rw [multiset.card_map] at h2 ⊢,
        rw [←h2],
        suffices h : E = ((A'.map pair_to_space_pair).map prod.snd).sum,
        {rw [h]},
        {
          simp only [multiset.map_map, E, pair_to_space_pair_def,
            function.comp_app, TS_reduce_eq_default_space],
        },
      },
      have sc_sp :=
      begin
        refine semicritical_subprojection A B E SP rfl _ dimE sc_AB rfl,
        {
          intros x hx,
          rcases multiset.mem_map.mp hx with ⟨y, hy, rfl⟩,
          apply default_space_eq_TS_of_reduced,
        },
      end,
      have cardSP : A.card + SP.card = n,
      {
        simp only [multiset.card_map, map_add],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
        simp only [add_tsub_cancel_left],
        simpa only [multiset.card_map, multiset.card_add, add_assoc] using hdim3,
      },
      have dimEp : dim Eᗮ = SP.card + 1,
      {
        have rn := dim_add_dim_orthogonal E,
        rw [hdim2, ←cardSP, dimE, add_assoc] at rn,
        zify at rn ⊢,
        exact add_left_cancel rn,
      },
      have cardSPle : SP.card ≤ n₀,
      {
        have cardAgt : A.card > 0 := by simpa only [multiset.card_map] using h3,
        rw [←cardSP] at hn,
        apply nat.le_of_lt_succ,
        refine nat.lt_of_lt_of_le _ hn,
        simpa only [lt_add_iff_pos_left] using cardAgt,
      },
      /- have Fsc : semicritical_spaces (pF.map (TS_microid_measure u')),
      {
        simp only [multiset.map_map, function.comp_app],
        simp only [u', TS_microid_proj_eq_proj_TS_microid _ Eᗮ u uE],
        let A := A'.map pair_to_default_space,
        let Z := (B' - A').map pair_to_default_space + (C - B').map pair_to_TS,
        have := semicritical_spaces_factorization
          A Z ⟨(_ : dim E = A.card), _⟩ _,
        {
          have : Z.map (λ W, W.map (proj Eᗮ)) = F.map (λ μ, (TS_microid_measure u μ).map (proj Eᗮ)),
          {
            simp only [Z, pair_to_default_space, pair_to_TS, multiset.map_add, multiset.map_map],
            rw [TS_default_body_eq_TS_default_measure k u],
          }
        }
      }, -/
      have finp := ih SP.card cardSPle SP _ dimEp rfl sc_sp,
      clear ih hTS hn hAB hBD h2 h3 h1 sc_sp,

      have hE : E ≤ ⊤ := le_top,
      let Am := A.map pair_to_microid,
      let Bm := B.map pair_to_microid,
      have vc : bm.is_vol_coll Am E,
      {
        split,
        {simpa only [multiset.card_map, Am] using dimE},
        {
          simp only [Am, multiset.map_map],
          intros K hK,
          rcases multiset.mem_map.mp hK with ⟨x, hx, rfl⟩,
          simp only [E],
          have : convex_body_subset (pair_to_TS (reduce_pair x)) ((pair_to_microid ∘ reduce_pair) x) :=
          begin
            apply reduced_microid_subset_TS,
          end,
          refine subset_trans this _,
          apply set_like.coe_subset_coe.mpr,
          refine le_sum_multiset_of_mem _,
          apply multiset.mem_map.mpr,
          refine ⟨reduce_pair x, _, rfl⟩,
          apply multiset.mem_map.mpr,
          exact ⟨x, hx, rfl⟩,
        },
      },
      have ac : bm.is_area_coll (Am + Bm) ⊤,
      {
        split,
        {
          change finite_dimensional.finrank ℝ (⊤ : submodule ℝ V) = (Am + Bm).card + 1,
          rw [finrank_top],
          change dim V = (Am + Bm).card + 1,
          rw [hdim2],
          simp only [multiset.card_add, multiset.card_map, add_left_inj],
          rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
          rcases multiset.le_iff_exists_add.mp hB'C with ⟨tt, rfl⟩,
          rw [add_tsub_cancel_left],
          rw [add_tsub_cancel_left],
          rw [←add_assoc],
          symmetry,
          simp only [multiset.card_map, multiset.card_add] at hdim3,
          assumption,
        },
        {
          intros K hK,
          simp only [convex_body_subset, submodule.top_coe, set.subset_univ],
        },
      },
      have sc : semicritical_spaces (Am.map span_of_convex_body),
      {
        simp only [multiset.map_map, Am, A],
        rw [span_reduced_microid_eq_TS, ←multiset.map_map],
        have : A.map pair_to_TS ≤ (A + B).map pair_to_TS,
        {simp only [multiset.map_add, le_add_iff_nonneg_right, zero_le]},
        exact semicritical_of_le this sc_AB,
      },
      have heq := bm.factorize_area vc ac hE sc,
      have tmp : multiset.map microid_of_measure SP = proj_coll Eᗮ Bm,
      {
        simp only [SP, Bm, proj_coll, multiset.map_map, pair_to_microid],
        simp only [function.comp_app],
        simp only [proj_microid_of_measure Eᗮ], -- rw does not work because of lambda!
      },
      have finp' := set.mem_image_of_mem (coe_sph Eᗮ) finp,
      rw [tmp, ←heq, coe_uncoe_sph] at finp',

      have : Am + Bm = B'.map pair_to_default_body + (C - B').map pair_to_microid,
      {
        simp only [Am, Bm, A, B, multiset.map_add, multiset.map_map],
        rw [←add_assoc],
        congr,
        rw [←multiset.map_add],
        simp only [function.comp_app, reduced_microid_eq_default_body],
        rcases multiset.le_iff_exists_add.mp hA'B' with ⟨t, rfl⟩,
        simp only [add_tsub_cancel_left],
      },
      rw [this] at finp',
      have : dim V = C.card + 1,
      {
        symmetry,
        simpa only [multiset.card_map, hdim2, add_left_inj] using hdim3,
      },
      have := matryoshka_reduction this finp',
      simpa only [multiset.map_map, pair_to_microid] using this,
    }
  }
end