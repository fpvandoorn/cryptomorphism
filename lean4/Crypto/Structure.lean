import Lean
import Crypto.Util
open Lean Elab Tactic Meta

/-- `isIn e l` tests whether `e` is definitionally equal to an expression in `l`. -/
def isIn (e : Expr) (es : Array Expr) : MetaM Bool :=
es.foldrM (λ e' b => do b || (← isDefEq e e')) false

def AddToContext (lctx : LocalContext) (h : Name) (t : Expr) : MetaM (LocalContext × FVarId) := do
  let nm ← mkFreshFVarId
  let new_lctx := lctx.addDecl (mkLocalDeclEx 0 nm h t BinderInfo.default)
  return (new_lctx, nm)

#check getMVarType
#check assignExprMVar
#check liftMetaMAtMain
#check getMainGoal
#check withMainContext
#check evalGeneralize
#check Parser.Tactic.generalize
-- #check Parser.Tactic.have
structure FieldData where
(fvar : Expr)
(type : Expr)
(depends : NameSet)
(isProp : Bool)

#print String
#print Format
open Std.Format

instance : ToFormat NameSet :=
⟨λ x => fmt x.toList⟩

instance : ToFormat FieldData :=
⟨λ ⟨a, b, c, d⟩ => group (nest 1 (fmt "⟨"  ++ fmt a ++ fmt "," ++ line ++ fmt b ++ fmt "," ++ line ++ fmt c ++ fmt "," ++ line ++ fmt d ++ fmt "⟩"))⟩

-- /-- Add fields to context, and returns data -/
-- def AddFieldsToContext (lctx : LocalContext) (nm : Name) (pref : Name) (args : Array Expr) :
--   MetaM (LocalContext × Array FieldData) := do
--   let goal ← mkFreshMVarId -- no
--   let e ← getEnv
--   let d ← e.find? nm
-- --   guard (isStructureLike e nm)
--   let e_str ← mkAppN (mkConst nm) args
--   let (lctx, cls) ← AddToContext lctx pref e_str
--   IO.println s!"local context: {lctx.decls.toArray}"
--   let sg ← cases goal cls
--   IO.println s!"after cases: {sg.map λ x => x.ctorName}"
--   return (lctx, #[])
-- --   let ctors ← cases goal cls
-- --   let fieldExprs := (ctors.map $ λ x => x.fields).get! 0
-- --   let fields := fieldExprs.map Expr.fvarId!
-- --   let axiom_fields ← fieldExprs.mapM isProof
-- --   let types ← fieldExprs.mapM inferType
-- --   let depends := types.map λ tp => tp.ListFvarIds
-- --   return (fieldExprs.zipWith4 FieldData.mk types depends axiom_fields)

-- /-- Add fields to context, and returns data -/
-- def AddFieldsToContext (nm : Name) (pref : Name) (args : Array Expr) :
--   TacticM (Array FieldData) := do
--   let e ← getEnv
--   let d ← e.find? nm
-- --   guard (isStructureLike e nm)
--   let e_str ← mkAppN (mkConst nm) args
--   let (lctx, cls) ← AddToContext lctx pref e_str
--   IO.println s!"local context: {lctx.decls.toArray}"
--   let sg ← cases (← getMainGoal) cls
--   IO.println s!"after cases: {sg.map λ x => x.ctorName}"
--   return (lctx, #[])
--   let ctors ← cases goal cls
--   let fieldExprs := (ctors.map $ λ x => x.fields).get! 0
--   let fields := fieldExprs.map Expr.fvarId!
--   let axiom_fields ← fieldExprs.mapM isProof
--   let types ← fieldExprs.mapM inferType
--   let depends := types.map λ tp => tp.ListFvarIds
--   return (fieldExprs.zipWith4 FieldData.mk types depends axiom_fields)

-- for testing
def trivialMapping (lctx : LocalContext) (fields1 fields2 : Array FieldData) :
  MetaM $ Array Expr × Array Expr := do
  let data_fields := fields1.filter $ λ info => !info.isProp
  let map1 ← data_fields.map λ info => info.fvar
  let map2 ← data_fields.map λ info => lctx.get! (info.fvar.fvarId!.updateSuffix $ λ s => "h2" ++ s) |>.toExpr
  return (map1, map2)

-- todo
def allMappings (fields1 fields2 : Array FieldData) : MetaM $ List $ List (FVarId × Expr) := do
 let data_fields1 := fields1.filter $ λ info => !info.isProp
 let data_fields2 := fields2.filter $ λ info => !info.isProp
 throwError "todo"


/-- Find which axioms in fields1 also occur in fields2 under the renaming `mapping`. -/
def matchingAxioms (fields1 fields2 : Array FieldData) (map1 map2 : Array Expr) :
  MetaM $ Array FieldData := do
  let propFields := fields1.filter λ info => info.isProp
  let types2 : Array Expr := fields2.filterMap λ info => if info.isProp then info.type else none
  let same ← propFields.filterM λ info => isIn (info.type.replaceFVars map1 map2) types2
  return same

/-- The tactic we use to automatically prove axioms. -/
def current_automation : MetaM Unit :=
return () -- tidy >> (done <|> tactic.interactive.finish [] none)

-- /-- Tries to prove `e` in the local context, returns tt if successful. -/
-- def try_to_prove (e : Expr) : MetaM Bool := --retrieve $
-- do
--   assert `h e,
--   succeeds $ focus1 $ current_automation >> done

/-- Tests whether nm1 is a subclass of nm1. Currently the data fields must have the same Name for
this tactic to work. -/
-- def is_subclass (nm1 nm2 : Name) (show_state := false) : MetaM Unit := do
--   let lctx := LocalContext.mkEmpty ()
--   let (lctx, M) ← AddToContext lctx `M (mkSort $ mkLevelSucc $ mkLevelParam `u)
--   let (lctx, info1) ← AddFieldsToContext lctx nm1 `h1 #[mkFVar M]
--   let (lctx, info2) ← AddFieldsToContext lctx nm2 `h2 #[mkFVar M]
--   --IO.println s!"{lctx.decls.toList}"
--   let (map1, map2) ← trivialMapping lctx info1 info2
--   let n ← matchingAxioms info1 info2 map1 map2
--   let n_uniqs := n.map λ info => info.fvar.fvarId!
--   let todo := info1.filter λ info => info.isProp && !n_uniqs.contains info.fvar.fvarId!
--   if todo.isEmpty then
--   IO.println s!"{nm1} is a trivial subclass of {nm2}: {nm2} has all the fields that {nm1} has." else do
--   -- trace $ todo.map $ λ info => info.fvar.local_pp_name,
--   -- let cannot_prove ← todo.filterM λ info => bnot <$> try_to_prove (info.type.instantiate_locals mapping),
--   let cannotProve := todo
--   -- trace $ cannot_prove.map $ λ info => info.fvar.local_pp_name,
--   if cannotProve.isEmpty then
--   IO.println s!"{nm1} is a subclass of {nm2}: {nm2} has all the data fields of {nm1}, and all the axioms of {nm1} can be proven from the axioms of {nm2}."
--   else
--   IO.println s!"Cannot prove the following axioms of {nm1} from the axioms of {nm2}:
--   {cannotProve.map $ λ info => info.fvar.fvarId!}."

-- run_cmd retrieve $ do
--   e ← get_env,
--   M ← AddToContext `M (Expr.sort $ (level.param `u).succ),
--   let nm := `comm_monoid1,
--   info1 ← AddFieldsToContext `comm_monoid1 `h1 [M],
--   info2 ← AddFieldsToContext `comm_monoid2 `h2 [M],
--   map ← trivialMapping info1 info2,
--   n ← matchingAxioms info1 info2 map,
--   trace n.length,
--   trace map,
--   -- d ← get_decl nm,
--   -- guard $ e.is_structure nm,
--   -- (args, _) ← open_pis d.type,
--   -- e_str ← mk_app nm args,
--   -- cls ← AddToContext `h e_str,
--   -- let args := args ++ [cls],
--   -- field_info ← get_FieldData nm args,
--   -- guard $ field_info.all $ λ info => info.isProp || info.depends.empty, -- no dependent data fields
--   -- data_locals ← field_info.mapM $ λ info => cond info.isProp (return none) $
--   --   (λ x, some (info.field_name, x)) <$> AddToContext info.field_name.last info.type, -- use assertv?
--   -- let data_replacements : name_map Expr :=
--   --   rb_map.of_List data_locals.reduce_option,
--   -- let reduced_types := field_info.filter_map $ λ info => cond info.isProp
--   --   (some $ (info.field_name, info.type.replace_const data_replacements args)) none,
--   -- reduced_types.mapM (λ x, type_check x.2), -- sanity check
--   -- axiom_locals ← reduced_types.mapM $ λ e, AddToContext e.1.last e.2,
--   -- trace reduced_types,
--   -- -- trace $ types,
--   -- trace_state,
--   -- trace field_info,
--   -- trace data_locals,
--   -- trace axiom_locals,
--   -- cases cls,
--   -- trace_state,
--   -- trace $ types.map Expr.to_string,
--   -- trace depends,
--   skip

/-! We define two notions of commutative monoids, the first is right-unital and the second is both left-unital and right-unital. -/

class comm_monoid1 (M : Type _) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(one : M)
(mul_one : ∀ x, mul x one = x)

#eval (do
  let env ← getEnv
  let f := getStructureFields env `comm_monoid1
  IO.println s!"{f}" : MetaM Unit)
#print mkMVar
#print mkFreshExprSyntheticOpaqueMVar
#print Meta.assert

/--
  Convert the given goal `Ctx |- target` into `Ctx, name : type |- target` and `Ctx |- type`.
  It assumes `val` has type `type`.
  Similar to `assert`, but uses a metavariable for `val`. -/
def assertm (mvarId : MVarId) (name : Name) (type : Expr) : MetaM (FVarId × MVarId × MVarId) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `assert
    let tag    ← getMVarTag mvarId
    let target ← getMVarType mvarId
    let newType := mkForall name BinderInfo.default type target
    let newMVarFn ← mkFreshExprSyntheticOpaqueMVar newType tag
    let newMVarB ← mkFreshExprSyntheticOpaqueMVar type tag
    assignExprMVar mvarId (mkApp newMVarFn newMVarB)
    let (newFVarId, newMVarId) ← intro1P newMVarFn.mvarId!
    pure (newFVarId, newMVarId, newMVarB.mvarId!)

  /--
Convert the given goal `Ctx |- target` into `Ctx, name : type |- target`.
It assumes `val` has type `type` -/
def asserti (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) : MetaM (FVarId × MVarId) :=
do
let m ← assert mvarId name type val
intro1P m

instance : Inhabited CasesSubgoal :=
⟨arbitrary, Name.anonymous⟩

def strucTacticM (mvarId : MVarId) : MetaM (MVarId × MVarId × Array FieldData) := do
  let nm := `comm_monoid1
  let e ← getEnv
  let d ← e.find? nm
  let tt ← isStructureLike e nm
  let u := mkLevelParam `u
  let (M, mvarId) ← asserti mvarId `M (mkSort (mkLevelSucc u)) (mkConst `PUnit [mkLevelSucc u])
  let eStr ← mkAppN (mkConst nm [u]) #[mkFVar M]
  let (h, mvarId, m2) ← assertm mvarId `h eStr
  let l ← cases mvarId h
  let info := l.get! 0
  let mvarId := info.mvarId
  withMVarContext mvarId do
  IO.println s!"ctorName: {info.ctorName}"
  IO.println s!"fields: {(← info.fields.mapM λ e => LocalDecl.userName <$> getLocalDecl e.fvarId!)}"
  IO.println s!"mvarId: {info.mvarId}"
  let fieldExprs := info.fields
  let fields := fieldExprs.map Expr.fvarId!
  let axiom_fields ← fieldExprs.mapM isProof
  let types ← fieldExprs.mapM inferType
  let depends := types.map λ tp => tp.ListFvarIds
  let fieldData := fieldExprs.zipWith4 FieldData.mk types depends axiom_fields
  IO.println f!"field data: {fieldData}"
  -- return (fieldExprs.zipWith4 FieldData.mk types depends axiom_fields)
  return (mvarId, m2, fieldData)


syntax (name := assert) "assert " ident (" : " term) (" := " term)? : tactic
@[tactic assert] def evalAssert : Tactic := fun stx =>
  match stx with
  | `(tactic| assert $h : $ty $[:= $val]?) => do
    withMainContext do
      let mvarId ← getMainGoal
      let eTy ← elabTerm ty none
      match val with
      | none   => do
        let (h, m1, m2) ← assertm mvarId h.getId eTy
        let l ← getUnsolvedGoals
        setGoals (m1::m2::l)
      | some v => do
        let eV ← elabTerm v eTy
        let (hs, m) ← assertHypotheses mvarId #[⟨h.getId, eTy, eV⟩]
        let l ← getUnsolvedGoals
        setGoals (m::l)
  | _ => throwUnsupportedSyntax

syntax (name := struc) "struc" : tactic
@[tactic «struc»] def evalStruc : Tactic := fun stx => do
  match stx with
  | `(tactic| struc) => withMainContext do
    let mvarId ← getMainGoal
    let (m1, m2, data) ← strucTacticM mvarId
    let l ← getUnsolvedGoals
    setGoals (m1::m2::l)
  | _ => throwUnsupportedSyntax

-- set_option pp.all true
def foo : Unit := by
  struc
  exact ()




class comm_monoid2 (M : Type _) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(one : M)
(mul_one : ∀ x, mul x one = x)
(one_mul : ∀ x, mul one x = x)

-- #eval is_subclass `comm_monoid1 `comm_monoid2
/- Output: comm_monoid1 is a trivial subclass of comm_monoid2: comm_monoid2 has all the fields that comm_monoid1 has. -/

-- #eval is_subclass `comm_monoid2 `comm_monoid1
/- Output: comm_monoid2 is a subclass of comm_monoid1: comm_monoid1 has all the data fields of comm_monoid2, and all the axioms of comm_monoid2 can be proven from the axioms of comm_monoid1. -/


/-! As a sanity check: we cannot prove commutativity on an arbitrary monoid. -/

class my_monoid (M : Type _) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(one : M)
(mul_one : ∀ x, mul x one = x)

-- #eval is_subclass `comm_monoid1 `my_monoid
/- Output: Cannot prove the following axioms of comm_monoid1 from the axioms of my_monoid:
[mul_comm]. -/
