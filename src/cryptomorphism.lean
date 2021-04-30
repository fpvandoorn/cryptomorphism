import tactic
/-!
A start on detecting cryptomorphic structures.
-/


open tactic

run_cmd do
  e ← get_env,
  let nm := `group,
  d ← get_decl nm,
  guard $ e.is_structure nm,
  -- let constr := e.constructors_of nm,
  -- trace constr,
  trace $ e.structure_fields nm,
  skip