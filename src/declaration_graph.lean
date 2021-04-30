import tactic
import all
/-!
Some functions for getting a graph of all classes/structures in mathlib.
-/

open tactic declaration environment native

namespace string
/-- `take s n` returns the first `n` characters of `s`. -/
meta def take (s : string) (n : ℕ) : string :=
(s.mk_iterator.nextn n).prev_to_string
end string

namespace native.rb_map

/-- `update m k f d` updates the value in `m` with key `k`.
  If the key exists with value `x`, the new value is `f x`.
  If the key doesn't exist, the new value is `d`. -/
protected meta def update {key data} (m : rb_map key data) (k : key)
  (f : data → data) (default : data) : rb_map key data :=
match (rb_map.find m k) with
| none     := rb_map.insert m k default
| (some x) := rb_map.insert (rb_map.erase m k) k (f x)
end

/-- Like filter, but where the function can also depend on the key. -/
meta def filter' {key data} [has_lt key] [decidable_rel ((<) : key → key → Prop)]
  (m : rb_map key data) (f : key → data → bool) : rb_map key data :=
fold m (mk key data) $ λa b m', if f a b then insert m' a b else m'

/-- Map the keys of a rb_map. Assumes that the function on keys is injective -/
meta def map_key {key key' data} [has_lt key'] [decidable_rel ((<) : key' → key' → Prop)]
  (m : rb_map key data) (f : key → key') : rb_map key' data :=
fold m (mk key' data) $ λa b m', m'.insert (f a) b

/-- `m.succ k` adds one to the value at `k`. Sets it to 1 if the key doesn't exist. -/
protected meta def succ {key data} [has_one data] [has_add data] (m : rb_map key data) (k : key) :
  rb_map key data :=
m.update k (+ 1) 1

/-- Map the keys of a rb_map. Adds the data of the keys that are mapped to the same new key. -/
meta def map_key_add {key key' data} [has_lt key'] [decidable_rel ((<) : key' → key' → Prop)]
  [has_add data] (m : rb_map key data) (f : key → key') : rb_map key' data :=
fold m (mk key' data) $ λa b m', m'.update (f a) (+ b) b

end native.rb_map

/-- Counts the number of declarations of each file. -/
meta def decls_per_file : tactic (rb_map string ℕ) := do
  e ← get_env,
  return $ e.fold (rb_map.mk string ℕ)
    (λ d m, if ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e then
        m.succ (e.decl_olean d.to_name).iget else m)

/-- Counts the number of declaration in each top-level directory of mathlib. -/
meta def top_level_mathlib : tactic (rb_map string ℕ) := do
  m ← decls_per_file,
  ml ← get_mathlib_dir,
  let n := ml.length,
  let m := m.filter' $ λ s _, ml.is_prefix_of s,
  let m := m.map_key_add $ λ s, let s' := s.popn n in s'.take $
  (s'.1.find_indexes $ (= '\\')).head,
  return m

namespace expr
end expr

meta def list_items (e : expr) : list name :=
e.fold [] $ λ e _ cs, if e.is_constant then cs.insert e.const_name else cs

meta def pos_line (p : option pos) : string :=
match p with
| some x := to_string x.line
| _      := ""
end

meta def print_class (env : environment) (decl : declaration)
  (print_args := tt) : tactic unit := do
(l, tgt) ← return decl.type.pi_binders,
let nm := decl.to_name,
olean_file ← env.decl_olean nm,
let s := ":\n  File: " ++ olean_file ++ "\n  Line: " ++
              pos_line (env.decl_pos nm),
trace $ to_string nm ++ s,
trace "  Type: class",
when print_args $ l.tail.mmap' (λ arg, do
  let arg_nm := arg.type.erase_annotations.get_app_fn.const_name.to_string,
  trace $ "arg_of_" ++ nm.to_string ++ "_" ++ arg_nm ++ s,
  trace "  Type: instance",
  trace $ "  Source: " ++ nm.to_string,
  trace $ "  Target: " ++ arg_nm)

meta def print_instance (env : environment) (decl : declaration)
  (print_args := tt) : tactic unit := do
(l, tgt) ← return decl.type.pi_binders,
let nm := decl.to_name,
olean_file ← env.decl_olean nm,
let s := ":\n  File: " ++ olean_file ++ "\n  Line: " ++
              pos_line (env.decl_pos nm),
trace $ to_string nm ++ s,
trace "  Type: class",
when print_args $ l.tail.mmap' (λ arg, do
  let arg_nm := arg.type.erase_annotations.get_app_fn.const_name.to_string,
  trace $ "arg_of_" ++ nm.to_string ++ "_" ++ arg_nm ++ s,
  trace "  Type: instance",
  trace $ "  Source: " ++ nm.to_string,
  trace $ "  Target: " ++ arg_nm)

/- prints information about `decl` if it is an instance or a class. If `print_args` is true, it also prints
  arguments of the class as "instances" (like `topological_monoid -> monoid`).
  If `only_classes` is true, only prints classes -/
meta def print_item_yaml (env : environment) (decl : declaration)
  (print_args := tt)
  (only_classes := ff) : tactic unit :=
let name := decl.to_name in
do
    when (env.decl_olean name).is_some $ do
      olean_file ← env.decl_olean name,
      let s := ":\n  File: " ++ olean_file ++ "\n  Line: " ++
              pos_line (env.decl_pos name),
      tactic.has_attribute `instance name >> guard (¬ only_classes) >> (do
            (l, tgt) ← return decl.type.pi_binders,
            guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
            guard (tgt.get_app_args.head.is_var && l.ilast.type.get_app_args.head.is_var),
            let src := to_string l.ilast.type.erase_annotations.get_app_fn.const_name,
            let tgt := to_string tgt.erase_annotations.get_app_fn.const_name,
            guard (src = tgt),
            trace $ to_string decl.to_name ++ s,
            trace "  Type: instance",
            trace $ "  Source: " ++ src,
            trace $ "  Target: " ++ tgt) <|>
      tactic.has_attribute `class name >> (do
            (l, tgt) ← return decl.type.pi_binders,
            guard (l.tail.all $ λ b, b.info = binder_info.inst_implicit),
            print_class env decl print_args) <|>
      skip

/-- prints information about unary classes and forgetful instances in the environment.
  It only prints instances and classes that have at most 1 argument that is not a type-class argument (within square brackets), and the instances can only be forgetful instances (where the conclusion is a class applied to a variable) -/
meta def print_content (print_args := tt) (only_classes := ff) : tactic unit :=
do curr_env ← get_env,
   (curr_env.fold list.nil list.cons).mmap' (λ d, print_item_yaml curr_env d print_args only_classes)

meta def test : tactic unit :=
do curr_env ← get_env,
   d ← get_decl `topological_monoid,
   trace (to_string d.to_name),
   print_item_yaml curr_env d

-- run_cmd test
-- run_cmd print_content ff ff-- ff tt

#print continuous
#print module