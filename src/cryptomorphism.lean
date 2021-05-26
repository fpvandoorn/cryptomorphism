import tactic
/-!
A start on detecting cryptomorphic structures.

Proposed algorithm when the data fields are the same:
* Look at the bijection of the data fields where the structures have the most axioms in common
* Try to prove the remaining axioms of each structure from the axioms of the other field.


To do:
Support `extends` keyword (with and without `old_structure_cmd` option)
-/


open tactic native
universe variable u

namespace list
variables {α β γ δ ε ζ : Type*}
def zip_with3 (f : α → β → γ → δ) : list α → list β → list γ → list δ
| (x::xs) (y::ys) (z::zs) := f x y z :: zip_with3 xs ys zs
| _       _       _       := []

def zip_with4 (f : α → β → γ → δ → ε) : list α → list β → list γ → list δ → list ε
| (x::xs) (y::ys) (z::zs) (u::us) := f x y z u :: zip_with4 xs ys zs us
| _       _       _       _       := []

def zip_with5 (f : α → β → γ → δ → ε → ζ) : list α → list β → list γ → list δ → list ε → list ζ
| (x::xs) (y::ys) (z::zs) (u::us) (v::vs) := f x y z u v :: zip_with5 xs ys zs us vs
| _       _       _       _       _       := []

end list

meta instance : inhabited declaration :=
⟨declaration.ax name.anonymous [] (expr.sort level.zero)⟩

@[derive inhabited]
meta structure field_data : Type :=
(local_constant : expr)
(type : expr)
(depends : name_set)
(is_prop : bool)

open format
meta instance : has_to_format field_data :=
⟨λ ⟨a, b, c, d⟩, group (nest 1 (to_fmt "⟨"  ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++ to_fmt d ++ to_fmt "⟩"))⟩
meta instance : has_to_tactic_format field_data :=
⟨λ ⟨a, b, c, d⟩, (λ x, group (nest 1 (to_fmt "⟨"  ++ to_fmt a ++ to_fmt "," ++ line ++ x ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++ to_fmt d ++ to_fmt "⟩"))) <$> pp b⟩

namespace name

/-- Update the last component of a name -/
def update_suffix (f : string → string) : name → name
| (mk_string s n) := mk_string (f s) n
| n := n

end name
namespace expr

/-- Replace `nm args` for `nm` in `nms` by the expression in the `name_map`. -/
meta def replace_const (e : expr) (nms : name_map expr) (args : list expr) : expr :=
e.replace $ λ subterm n,
  let data := nms.find subterm.get_app_fn.const_name in
  if data.is_some && (subterm.get_app_args = args) then data.iget else none

/-- Returns the pretty names of all local constants in an expression. -/
meta def list_local_const_pretty_names (e : expr) : name_set :=
e.fold mk_name_set
  (λ e' _ es, if e'.is_local_constant then es.insert e'.local_pp_name else es)

end expr

namespace name_set
/-- Erase a list of names from a name_set -/
meta def erase_list (ns : name_set) (nms : list name) : name_set :=
nms.foldl name_set.erase ns

end name_set

/-- `is_in e l` tests whether `e` is definitionally equal to an expression in `l`. -/
meta def is_in : expr → list expr → tactic bool
| e []         := return ff
| e (t :: ts) := (is_def_eq e t >> return tt) <|> is_in e ts

/-- like `assert h t`, but without swapping goals. -/
meta def add_to_context (h : name) (t : expr) : tactic expr :=
do assert_core h t, swap, e ← intro h, return e

-- /-- Get field data, with types of fields instantiated by `args` -/
-- meta def get_field_data (nm : name) (args : list expr) : tactic $ list field_data := retrieve $ do
--   e ← get_env,
--   fields ← e.structure_fields_full nm,
--   axiom_fields ← fields.mmap $ λ nm, mk_const nm >>= is_proof,
--   types ← fields.mmap $ λ nm, (e.get nm).to_option.iget.type.drop_pis args,
--   let depends := types.map $ λ tp, tp.list_names_with_prefix nm,
--   return $ fields.zip_with4 field_data.mk types depends axiom_fields

/-- Add fields to context, and returns data -/
meta def add_fields_to_context (nm : name) (pref : name) (args : list expr) :
  tactic $ list field_data := do
  e ← get_env,
  d ← e.get nm,
  guard $ e.is_structure nm,
  e_str ← mk_app nm args,
  cls ← add_to_context pref e_str,
  [(_, field_exprs)] ← cases cls,
  fields ← return $ field_exprs.map expr.local_pp_name,
  axiom_fields ← field_exprs.mmap is_proof,
  types ← field_exprs.mmap infer_type,
  let depends := types.map $ λ tp, tp.list_local_const_pretty_names,
  return $ field_exprs.zip_with4 field_data.mk types depends axiom_fields

-- for testing
meta def trivial_mapping (fields1 fields2 : list field_data) : tactic $ list (name × expr) := do
  let data_fields := fields1.filter $ λ info, !info.is_prop,
  mapping ← data_fields.mmap $ λ info, prod.mk info.local_constant.local_uniq_name <$>
    get_local (info.local_constant.local_pp_name.update_suffix $ λ s, "h2" ++ s.popn 2) <|> fail "Not all data fields occur in the second class.",
  return mapping

-- todo
meta def all_mappings (fields1 fields2 : list field_data) : tactic $ list $ list (name × expr) := do
 let data_fields1 := fields1.filter $ λ info, !info.is_prop,
 let data_fields2 := fields2.filter $ λ info, !info.is_prop,
 failed


/-- Find which axioms in fields1 also occur in fields2 under the renaming `mapping`. -/
meta def matching_axioms (fields1 fields2 : list field_data) (mapping : list (name × expr)) :
  tactic $ list field_data := do
  let prop_fields := fields1.filter $ λ info, info.is_prop,
  let types2 : list expr := fields2.filter_map $ λ info, if info.is_prop then info.type else none,
  matches ← prop_fields.mfilter $ λ info, is_in (info.type.instantiate_locals mapping) types2,
  return matches

/-- The tactic we use to automatically prove axioms. -/
meta def current_automation : tactic unit :=
tidy >> (done <|> tactic.interactive.finish [] none)

/-- Tries to prove `e` in the local context, returns tt if successful. -/
meta def try_to_prove (e : expr) : tactic bool := retrieve $ do
  assert `h e,
  succeeds $ focus1 $ current_automation >> done

/-- Tests whether nm1 is a subclass of nm1. Currently the data fields must have the same name for
this tactic to work. -/
meta def is_subclass (nm1 nm2 : name) (show_state := ff) : tactic unit :=
  (if show_state then id else retrieve : tactic unit → tactic unit) $ do
  M ← add_to_context `M (expr.sort $ (level.param `u).succ),
  info1 ← add_fields_to_context nm1 `h1 [M],
  info2 ← add_fields_to_context nm2 `h2 [M],
  mapping ← trivial_mapping info1 info2,
  n ← matching_axioms info1 info2 mapping,
  let n_uniqs := n.map $ λ info, info.local_constant.local_uniq_name,
  let todo := info1.filter $ λ info, info.is_prop ∧ info.local_constant.local_uniq_name ∉ n_uniqs,
  if todo.length = 0 then
  trace!"{nm1} is a trivial subclass of {nm2}: {nm2} has all the fields that {nm1} has." else do
  -- trace $ todo.map $ λ info, info.local_constant.local_pp_name,
  cannot_prove ← todo.mfilter $ λ info, bnot <$> try_to_prove (info.type.instantiate_locals mapping),
  -- trace $ cannot_prove.map $ λ info, info.local_constant.local_pp_name,
  if cannot_prove.length = 0 then
  trace!"{nm1} is a subclass of {nm2}: {nm2} has all the data fields of {nm1}, and all the axioms of {nm1} can be proven from the axioms of {nm2}."
  else
  trace!"Cannot prove the following axioms of {nm1} from the axioms of {nm2}:
{cannot_prove.map $ λ info, info.local_constant.local_pp_name.update_suffix $ λ s, s.popn 3}."

-- run_cmd retrieve $ do
--   e ← get_env,
--   M ← add_to_context `M (expr.sort $ (level.param `u).succ),
--   let nm := `comm_monoid1,
--   info1 ← add_fields_to_context `comm_monoid1 `h1 [M],
--   info2 ← add_fields_to_context `comm_monoid2 `h2 [M],
--   map ← trivial_mapping info1 info2,
--   n ← matching_axioms info1 info2 map,
--   trace n.length,
--   trace map,
--   -- d ← get_decl nm,
--   -- guard $ e.is_structure nm,
--   -- (args, _) ← open_pis d.type,
--   -- e_str ← mk_app nm args,
--   -- cls ← add_to_context `h e_str,
--   -- let args := args ++ [cls],
--   -- field_info ← get_field_data nm args,
--   -- guard $ field_info.all $ λ info, info.is_prop || info.depends.empty, -- no dependent data fields
--   -- data_locals ← field_info.mmap $ λ info, cond info.is_prop (return none) $
--   --   (λ x, some (info.field_name, x)) <$> add_to_context info.field_name.last info.type, -- use assertv?
--   -- let data_replacements : name_map expr :=
--   --   rb_map.of_list data_locals.reduce_option,
--   -- let reduced_types := field_info.filter_map $ λ info, cond info.is_prop
--   --   (some $ (info.field_name, info.type.replace_const data_replacements args)) none,
--   -- reduced_types.mmap (λ x, type_check x.2), -- sanity check
--   -- axiom_locals ← reduced_types.mmap $ λ e, add_to_context e.1.last e.2,
--   -- trace reduced_types,
--   -- -- trace $ types,
--   -- trace_state,
--   -- trace field_info,
--   -- trace data_locals,
--   -- trace axiom_locals,
--   -- cases cls,
--   -- trace_state,
--   -- trace $ types.map expr.to_string,
--   -- trace depends,
--   skip

/-! We define two notions of commutative monoids, the first is right-unital and the second is both left-unital and right-unital. -/

class comm_monoid1 (M : Type*) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(one : M)
(mul_one : ∀ x, mul x one = x)

class comm_monoid2 (M : Type*) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(one : M)
(mul_one : ∀ x, mul x one = x)
(one_mul : ∀ x, mul one x = x)

run_cmd is_subclass `comm_monoid1 `comm_monoid2
/- Output: comm_monoid1 is a trivial subclass of comm_monoid2: comm_monoid2 has all the fields that comm_monoid1 has. -/

run_cmd is_subclass `comm_monoid2 `comm_monoid1
/- Output: comm_monoid2 is a subclass of comm_monoid1: comm_monoid1 has all the data fields of comm_monoid2, and all the axioms of comm_monoid2 can be proven from the axioms of comm_monoid1. -/


/-! As a sanity check: we cannot prove commutativity on an arbitrary monoid. -/

class my_monoid (M : Type*) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(one : M)
(mul_one : ∀ x, mul x one = x)

run_cmd is_subclass `comm_monoid1 `my_monoid
/- Output: Cannot prove the following axioms of comm_monoid1 from the axioms of my_monoid:
[mul_comm]. -/
