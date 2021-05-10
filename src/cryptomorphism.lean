import tactic
/-!
A start on detecting cryptomorphic structures.

Proposed algorithm when the data fields are the same:
* Look at the bijection of the data fields where the structures have the most axioms in common
* Try to prove the remaining axioms of each structure from the axioms of the other field.


To do:
Support `extends` keyword (with and without `old_structure_cmd` option)
-/


open tactic

namespace list
variables {α β γ δ ε : Type*}
def zip_with3 (f : α → β → γ → δ) : list α → list β → list γ → list δ
| (x::xs) (y::ys) (z::zs) := f x y z :: zip_with3 xs ys zs
| _       _       _       := []

def zip_with4 (f : α → β → γ → δ → ε) : list α → list β → list γ → list δ → list ε
| (x::xs) (y::ys) (z::zs) (u::us) := f x y z u :: zip_with4 xs ys zs us
| _       _       _       _       := []

end list

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

#print comm_monoid1
#print comm_monoid2

meta instance : inhabited declaration :=
⟨declaration.ax name.anonymous [] (expr.sort level.zero)⟩

meta structure field_data : Type :=
(field_name : name)
(type : expr)
(depends : name_set)
(is_prop : bool)

open format
meta instance : has_to_format field_data :=
⟨λ ⟨a, b, c, d⟩, group (nest 1 (to_fmt "⟨"  ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++ to_fmt d ++ to_fmt "⟩"))⟩
meta instance : has_to_tactic_format field_data :=
⟨λ ⟨a, b, c, d⟩, (λ x, group (nest 1 (to_fmt "⟨"  ++ to_fmt a ++ to_fmt "," ++ line ++ x ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++ to_fmt d ++ to_fmt "⟩"))) <$> pp b⟩

/-- Get field data, with types of fields instantiated by `args` -/
meta def get_field_data (nm : name) (args : list expr) : tactic $ list field_data := retrieve $ do
  e ← get_env,
  fields ← e.structure_fields_full nm,
  axiom_fields ← fields.mmap $ λ nm, mk_const nm >>= is_proof,
  types ← fields.mmap $ λ nm, (e.get nm).to_option.iget.type.drop_pis args,
  let depends := types.map $ λ tp, tp.list_names_with_prefix nm,
  return $ fields.zip_with4 field_data.mk types depends axiom_fields

#print name_map
/-- Replace `nm args` for `nm` in `nms` by the expression in the `name_map`. -/
meta def expr.replace_const (e : expr) (nms : name_map expr) (args : list expr) : expr :=
e.replace $ λ subterm n,
  let data := nms.find subterm.get_app_fn.const_name in
  if data.is_some && (subterm.get_app_args = args) then data.iget else none

/-- like `assert h t`, but without swapping goals. -/
meta def add_to_context (h : name) (t : expr) : tactic expr :=
do assert_core h t, swap, e ← intro h, return e
#print list.reduce_option

meta def matching_axioms (data_fields : list (name × name)) (axiom_fields1 : _) : tactic ℕ :=
_


run_cmd retrieve $ do
  e ← get_env,
  let nm := `comm_monoid1,
  d ← get_decl nm,
  guard $ e.is_structure nm,
  (args, _) ← open_pis d.type,
  e_str ← mk_app nm args,
  cls ← add_to_context `h e_str,
  let args := args ++ [cls],
  field_info ← get_field_data nm args,
  guard $ field_info.all $ λ info, info.is_prop || info.depends.empty, -- no dependent data fields
  data_locals ← field_info.mmap $ λ info, cond info.is_prop (return none) $
    (λ x, some (info.field_name, x)) <$> add_to_context info.field_name.last info.type, -- use assertv?
  let data_replacements : name_map expr :=
    native.rb_map.of_list data_locals.reduce_option,
  let reduced_types := field_info.filter_map $ λ info, cond info.is_prop
    (some $ (info.field_name, info.type.replace_const data_replacements args)) none,
  reduced_types.mmap (λ x, type_check x.2), -- sanity check
  axiom_locals ← reduced_types.mmap $ λ e, add_to_context e.1.last e.2,
  trace reduced_types,
  -- trace $ types,
  trace_state,
  -- trace field_info,
  trace data_locals,
  trace axiom_locals,
  cases cls,
  trace_state,
  -- trace $ types.map expr.to_string,
  -- trace depends,
  skip




#print expr.instantiate_local
meta def matching_axioms (data_fields : list (name × name)) (axiom_fields1 : _) : tactic ℕ :=
_