import tactic.lint
import tactic.ext
import tactic.congr

open tactic
setup_tactic_parser

namespace tactic

meta def paul_convert (sym : parse (with_desc "←" (tk "<-")?)) (r : parse texpr)
  (n : parse (tk "using" *> small_nat)?) : tactic unit :=
do tgt ← target,
  u ← infer_type tgt,
  r ← i_to_expr ``(%%r : (_ : %%u)),
  src ← infer_type r,
  src ← simp_lemmas.mk.dsimplify [] src {fail_if_unchanged := ff},
  v ← to_expr (if sym.is_some then ``(%%src = %%tgt) else ``(%%tgt = %%src)) tt ff >>= mk_meta_var,
  (if sym.is_some then mk_eq_mp v r else mk_eq_mpr v r) >>= tactic.exact,
  gs ← get_goals,
  set_goals [v],
  --try (tactic.congr' n),
  gs' ← get_goals,
  set_goals $ gs' ++ gs

meta def paul (r : parse texpr) : tactic unit :=
do {
  e ← i_to_expr ``(%%r),
  tgt ← target,
  -- u ← infer_type tgt,
  v ← infer_type e,
  w ← to_expr ``(%%v = %%tgt),
  mk_eq_mp w e >>= tactic.exact,
  gs ← get_goals,
  set_goals $ w :: gs
}

end tactic