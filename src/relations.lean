import tactic
import tactic.slim_check

mk_simp_attribute props ""
variables {α : Type*}
@[props] def is_reflexive (r : α → α → Prop) : Prop := ∀ a, r a a
@[props] def is_irreflexive (r : α → α → Prop) : Prop := ∀ a, ¬ r a a
@[props] def is_symmetric (r : α → α → Prop) : Prop := ∀ a b, r a b → r b a
@[props] def is_transitive (r : α → α → Prop) : Prop := ∀ a b c, r a b → r b c → r a c
@[props] def is_asymmetric (r : α → α → Prop) : Prop := ∀ a b, r a b → ¬ r b a
@[props] def is_total' (r : α → α → Prop) : Prop := ∀ a b, r a b ∨ r b a
@[props] def is_antisymmetric (r : α → α → Prop) : Prop := ∀ a b, r a b → r b a → a = b
@[props] def is_partial_equivalence (r : α → α → Prop) : Prop := is_symmetric r ∧ is_transitive r
@[props] def is_trichotomous' (r : α → α → Prop) : Prop := ∀ a b, r a b ∨ a = b ∨ r b a
@[props] def is_preorder' (r : α → α → Prop) : Prop := is_reflexive r ∧ is_transitive r
@[props] def is_total_preorder' (r : α → α → Prop) : Prop := is_transitive r ∧ is_total' r
@[props] def is_partial_order' (r : α → α → Prop) : Prop := is_preorder' r ∧ is_antisymmetric r
@[props] def is_linear_order' (r : α → α → Prop) : Prop := is_partial_order' r ∧ is_total' r
@[props] def is_equivalence (r : α → α → Prop) : Prop := is_preorder' r ∧ is_symmetric r
@[props] def is_strict_order' (r : α → α → Prop) : Prop := is_irreflexive r ∧ is_transitive r
-- def is_strict_weak_order' (r : α → α → Prop) : Prop := is_strict_order' r ∧ is_incomp_trans' r
-- def is_strict_total_order' (r : α → α → Prop) : Prop := is_trichotomous' r ∧ is_strict_weak_order' r

open tactic expr sum

meta def props : list (name × string) :=
[(`is_reflexive, "reflexive"),
 (`is_irreflexive, "irreflexive"),
 (`is_symmetric, "symmetric"),
 (`is_transitive, "transitive"),
 (`is_asymmetric, "asymmetric"),
 (`is_total', "total"),
 (`is_antisymmetric, "antisymmetric"),
 (`is_trichotomous', "trichotomous")]

meta def omega_that_fails_on_false : tactic unit :=
done <|> all_goals' (target >>= λ tgt, guard (tgt.const_name ≠ `false) >> interactive.omega [])

meta def try_slim_check (cfg : slim_check.slim_check_cfg) :
  tactic (option string) := do
result ← try_or_report_error (interactive.slim_check {quiet := tt, ..cfg}),
inr n ← return result | return none,
when (n.starts_with "Failed to create a") failed,
return (some n)

meta def finds_slim_check_example (cfg : slim_check.slim_check_cfg := {}) : tactic unit := do
n ← try_slim_check cfg,
guard n.is_some

meta def test_init : tactic unit := do
  t ← target,
  let ⟨f, args⟩ := t.get_app_fn_args,
  let prop_name := f.const_name,
  let rel_name := args.ilast.const_name,
  dsimp_target none [prop_name, rel_name] {fail_if_unchanged := ff}

meta def test_init_main (t : expr) (R : name) : tactic expr := do
  t.dsimp {} ff [`props] [simp_arg_type.expr $ expr.const R []]

meta def test_main (t : expr) (cfg : slim_check.slim_check_cfg := {}) : tactic (ℕ ⊕ string) := do
-- trace t,
  let not_t := const `not [] t,
  retrieve (tactic.assert `this t >> focus1 (tidy >> omega_that_fails_on_false >> done) >> return (inl 0)) <|>
  retrieve (tactic.assert `this not_t >> focus1 (tidy >> omega_that_fails_on_false >> done) >> return (inl 1)) <|>
  retrieve (do tactic.assert `this t, some error ← focus1 (try_slim_check cfg), return (inr error)) <|>
  return (inl 2)

meta def test_core (cfg : slim_check.slim_check_cfg := {}) : tactic (ℕ ⊕ string) := do
  test_init,
  t ← target,
  r ← test_main t cfg,
  when (r = inl 0) (get_local `this >>= exact),
  return r

meta def test (cfg : slim_check.slim_check_cfg := {}) : tactic unit := do
  result ← test_core cfg,
  when (result = inl 0) (trace "succeeded!"),
  when (result = inl 1) (trace "proved the negation!"),
  when (result.is_right) (trace "found a counterexample!" >> trace result.get_right.iget),
  when (result = inl 2) (trace "couldn't make progress."),
  skip

meta def test_all (R : name) (cfg : slim_check.slim_check_cfg := {}) : tactic unit :=
props.mmap' $ λ ⟨prop_nm, prop_str⟩, retrieve $ do {
  -- let t : expr := (const rel [level.zero]) (const `nat []) (const R []),
  rel ← mk_const R,
  prop ← mk_const prop_nm,
  t ← to_expr ``(%%prop %%rel),
  t ← test_init_main t R,
  result ← test_main t cfg,
  -- trace result,
  when (result = inl 0) (trace!"{R} is     {prop_str}!"),
  when (result = inl 1) (trace!"{R} is not {prop_str}!"),
  when (result.is_right) (trace!"{R} is not {prop_str}!"),
  when (result = inl 2) (trace!"Cannot resolve whether {R} is {prop_str}.") }


@[user_attribute] meta def test_attr : user_attribute :=
{ name := `test,
  descr := "Automatically tests whether a relation `ℕ → ℕ → Prop` satisfies some properties.",
  after_set := some $
    λ R _ _, do test_all R }

-- def dummy : false ↔ 0 = 1 := by simp


@[test]
def R (n m : ℕ) : Prop :=
n < m ∨ n > 10

example : is_transitive R :=
by { test; sorry }
