import convex convex_body linalg measure touching_cone brunn_minkowski criticality
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

def polytope :=
{ P : set V // is_polytope P }

abbreviation microid_generator_space (k : ℕ) := metric.ball (0 : pi_Lp 2 (function.const (fin k) V)) 1

noncomputable instance borel_measurable_space_microid_generator_space (k : ℕ) :=
borel
(microid_generator_space V k)

instance borel_space_microid_generator_space (k : ℕ) :
borel_space (microid_generator_space V k) :=
⟨rfl⟩

abbreviation microid_measure (k : ℕ) :=
measure_theory.finite_measure (microid_generator_space V k)


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

def polytope_of_microid_generator {k : ℕ} (G : microid_generator_space V k) :
polytope V := sorry

def microid_of_measure {k : ℕ} (μ : microid_measure V k) :
convex_body V := sorry

-- only used for c > 0
def cuspy_cone (x : V) (u : V) (c : ℝ) :=
{ y : V | ⟪x - y, u⟫_ℝ ≥ c * ∥ y - x ∥ }

def is_cuspy (A : set V) (u : V) (c : ℝ) :=
∃ x ∈ A, A ⊆ cuspy_cone x u c

lemma cuspy_iff_TS_zero (K : convex_body V) (u : V) :
TS K.val = 0 ↔ ∃ c > 0, is_cuspy K.val u c := sorry

lemma cuspy_generators_of_cuspy {k : ℕ} {μ : microid_measure V k} {u : V} {c > 0}
(h : is_cuspy (microid_of_measure μ).val u c) :
∀ G ∈ msupport μ, is_cuspy (polytope_of_microid_generator G).val u c := sorry

def polytope_to_convex_body
(P : polytope V) : convex_body V :=
⟨P.val, sorry⟩

def is_default_polytope {k : ℕ} (μ : microid_measure V k) (u : metric.sphere (0 : V) 1)
(P : microid_generator_space V k) :=
(polytope_of_microid_generator P).val ⊆ vector_orth u.val ∧
TS (polytope_of_microid_generator P).val u ≠ 0 ∧
(∀ C : multiset (convex_body V),
C.card = dim V - 2 →
u ∈ msupport (bm.area ((polytope_to_convex_body (polytope_of_microid_generator P)) ::ₘ C)) →
u ∈ msupport (bm.area (microid_of_measure μ ::ₘ C)))

-- uses pruning lemma
lemma exists_default_polytope_of_TS_nonzero {k : ℕ} {μ : microid_measure V k}
(h : TS (microid_of_measure μ).val ≠ 0) (u : metric.sphere (0 : V) 1) :
∃ P : microid_generator_space V k, is_default_polytope μ u P := sorry

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

noncomputable def pair_to_default_space {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V :=
TS (pair_to_default_body pair).val u.val

noncomputable def pair_to_TS {k : ℕ}
{u : metric.sphere (0 : V) 1}
(pair : microid_pair k u) : submodule ℝ V :=
TS (microid_of_measure (pair_to_measure pair)).val u

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
  {simp},
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
      simp [hW],
    },
  },
end

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
{A B : multiset (microid_pair k u)}
{E : submodule ℝ V}
(hAE : E = (A.map pair_to_TS).sum)
(hA1 : multiset_all (λ x, pair_to_default_space x = pair_to_TS x) A)
(hA2 : dim E = A.card)
(hB : semicritical_spaces ((A + B).map pair_to_TS)) :
semicritical_spaces
(B.map (TS_microid_measure (uncoe_sph Eᗮ u (u_mem_sum_TS_orth A hAE)) ∘ project_microid_measure Eᗮ ∘ pair_to_measure)) := sorry

end blabb

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
    {admit},
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
          have dim_uperp : dim uperp = n := sorry,
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
      let F := (B' - A').map pair_to_default_measure + (C - B').map pair_to_measure,
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
      },
      let pF := F.map (project_microid_measure Eᗮ),
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
      let u' := uncoe_sph Eᗮ u uE,
      have Fsc : semicritical_spaces (pF.map (TS_microid_measure u')),
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
      },
      have finp := ih n' hn' pF u' hdim2' hdim3' Fsc,
      clear ih,

      have hE : E ≤ ⊤ := le_top,
      let F' := F.map microid_of_measure,
      let H' := A'.map pair_to_default_body,
      have dimE : bm.is_vol_coll H' E := sorry,
      have dimV : bm.is_area_coll (H' + F') ⊤ := sorry,
      have H'sc : semicritical_spaces (H'.map span_of_convex_body) := sorry,
      have heq := bm.factorize_area dimE dimV hE H'sc,
      have tmp : multiset.map microid_of_measure pF = proj_coll Eᗮ F' := sorry,
      have finp' := set.mem_image_of_mem (coe_sph Eᗮ) finp,
      rw [tmp, ←heq] at finp',

      have uu' : coe_sph Eᗮ u' = u := sorry,
      have : H' + F' = B'.map pair_to_default_body + (C - B').map pair_to_microid := sorry,
      rw [this, uu'] at finp',
      have := matryoshka_reduction (sorry : dim V = C.card + 1) finp',
      simp only [multiset.map_map],
      simp only [pair_to_microid] at this,
      assumption,
    }
  }
end