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
(decl : LocalDecl)
(fvar : Expr)
(type : Expr)
(depends : NameSet)
(isProp : Bool)

open Std.Format

instance : ToFormat NameSet :=
⟨λ x => fmt x.toList⟩

instance : ToFormat FieldData :=
⟨λ ⟨a, b, c, d, e⟩ => group (nest 1 (fmt "⟨"  ++ fmt a ++ fmt "," ++ line ++ fmt b ++ fmt "," ++ line
++ fmt c ++ fmt "," ++ line ++ fmt d ++ fmt "," ++ line ++ fmt e ++ fmt "⟩"))⟩

namespace FieldData

def name (fields : FieldData) : Name :=
fields.decl.userName.head!

end FieldData

namespace Meta

def ppFieldData (x : FieldData) : MetaM Format :=
do return group (nest 1 (fmt "⟨"  ++
fmt x.name ++ fmt "," ++ line ++
fmt (← ppExpr x.fvar) ++ fmt "," ++ line ++
fmt (← ppExpr x.type) ++ fmt "," ++ line ++
fmt (← x.depends.toList.mapM λ e => ppExpr (mkFVar e)) ++ fmt "," ++ line ++
fmt x.isProp ++ fmt "⟩"))

def AddFieldsToContext (mvarId : MVarId) (nm : Name) (us : List Level) (args : Array Expr) :
  MetaM (MVarId × MVarId × Array FieldData) := do
  let e ← getEnv
  let d ← e.find? nm
  let tt ← isStructureLike e nm
  let eStr ← mkAppN (mkConst nm us) args
  let (h, mvarId, m2) ← assertm mvarId `h eStr
  let l ← cases mvarId h
  let info := l.get! 0
  let mvarId := info.mvarId
  withMVarContext mvarId do
  let lctx ← getLCtx
  let fieldExprs := info.fields
  let fields := fieldExprs.map Expr.fvarId!
  let ldecls := fields.map λ e => lctx.fvarIdToDecl.find! e
  let axiom_fields ← fieldExprs.mapM isProof
  let types ← fieldExprs.mapM inferType
  let depends := types.map λ tp => tp.ListFvarIds
  let fieldData := ldecls.zipWith5 FieldData.mk fieldExprs types depends axiom_fields
  -- IO.println f!"field data: {← fieldData.mapM ppFieldData}"
  return (mvarId, m2, fieldData)
#print Array.foldr
-- for testing
def trivialMapping (lctx : LocalContext) (fields1 fields2 : Array FieldData) :
  MetaM $ Array Expr × Array Expr := do
  let dataFields := fields1.filter λ info => !info.isProp
  let map1 ← dataFields.map λ info => info.fvar
  let map2 ← dataFields.map λ info => fields2.findSome! λ info' =>
    if info.name == info'.name then some info'.fvar else none
  -- let map2 := map2.map λ info? => info?.getD arbitrary
  --(info.fvar.fvarId!.updateSuffix λ s => "h2" ++ s) |>.toExpr
  return (map1, map2)

-- todo
def allMappings (fields1 fields2 : Array FieldData) : MetaM $ List $ List (FVarId × Expr) := do
 let dataFields1 := fields1.filter λ info => !info.isProp
 let dataFields2 := fields2.filter λ info => !info.isProp
 throwError "todo"


/-- Find which axioms in fields1 also occur in fields2 under the renaming `mapping`. -/
def matchingAxioms (fields1 fields2 : Array FieldData) (map1 map2 : Array Expr) :
  MetaM $ Array FieldData := do
  let propFields := fields1.filter λ info => info.isProp
  let types2 : Array Expr := fields2.filterMap λ info => if info.isProp then info.type else none
  let same ← propFields.filterM λ info => isIn (info.type.replaceFVars map1 map2) types2
  return same

def mkSimpContext (simpOnly := false) : MetaM Simp.Context := do
  return {
    config      := {}
    simpLemmas  := if simpOnly then {} else (← getSimpLemmas)
    congrLemmas := (← getCongrLemmas)
  }

/-- The tactic we use to automatically prove axioms. -/
def currentAutomation (mvarId : MVarId) : MetaM Unit := do
match (← simpTarget mvarId (← mkSimpContext false)) with -- does this work?
| some x => return () --IO.println "failure!"
| none => return ()  -- IO.println "success!"

#print elabSimpConfig
#print replaceMainGoal

--return () -- tidy >> (done <|> tactic.interactive.finish [] none)

/-- Tries to prove `e` in the local context, returns tt if successful. -/
def tryToProve (mvarId : MVarId) (e : Expr) : MetaM Bool := withoutModifyingState do
  let (fvar, mvarId, m2) ← assertm mvarId `h e
  try
    currentAutomation m2
    -- IO.println s!"is assigned: {← isExprMVarAssigned m2}"
    let some e ← getExprMVarAssignment? m2 | return false
    let e ← instantiateMVars e
    if (← e.hasExprMVar) then return false else return true
  catch err =>
    return false


/-- Tests whether nm1 is a subclass of nm1. Currently the data fields must have the same Name for
this tactic to work. -/
def isSubclass (mvarId : MVarId) (nm1 nm2 : Name) (show_state := false) :
  MetaM (MVarId × MVarId × MVarId) := do
  let u := mkLevelParam `u
  let (M, mvarId) ← asserti mvarId `M (mkSort (mkLevelSucc u)) (mkConst `PUnit [mkLevelSucc u])
  let (mvarId, m1, fields1) ← AddFieldsToContext mvarId nm1 [u] #[mkFVar M]
  let (mvarId, m2, fields2) ← AddFieldsToContext mvarId nm2 [u] #[mkFVar M]
  withMVarContext mvarId do
  let (map1, map2) ← trivialMapping (← getLCtx) fields1 fields2
  -- IO.println f!"map 1: {← map1.mapM Meta.ppExpr}"
  -- IO.println f!"map 2: {← map2.mapM Meta.ppExpr}"
  let matching ← matchingAxioms fields1 fields2 map1 map2
  let matchingUniqs := matching.map λ info => info.fvar.fvarId!
  let todo := fields1.filter λ info => info.isProp && !matchingUniqs.contains info.fvar.fvarId!
  if todo.isEmpty then
    IO.println s!"{nm1} is a trivial subclass of {nm2}: {nm2} has all the fields that {nm1} has."
  else do
    -- trace $ todo.map λ info => info.fvar.local_pp_name,
    -- let cannot_prove ← todo.filterM λ info => bnot <$> try_to_prove (info.type.instantiate_locals mapping),
    let cannotProve ← todo.filterM λ info =>
      not <$> tryToProve mvarId (info.type.replaceFVars map1 map2)
    -- trace $ cannot_prove.map λ info => info.fvar.local_pp_name,
    if cannotProve.isEmpty then
    IO.println s!"{nm1} is a subclass of {nm2}: {nm2} has all the data fields of {nm1}, and all the axioms of {nm1} can be proven from the axioms of {nm2}."
    else
    IO.println s!"Cannot prove the following axioms of {nm1} from the axioms of {nm2}:
    {← cannotProve.mapM λ info : FieldData => ppExpr info.fvar}."
  return (mvarId, m1, m2)

end Meta
open Meta

-- def strucTacticM (mvarId : MVarId) : MetaM (MVarId × MVarId × Array FieldData) := do
--   let nm := `comm_monoid1
--   let e ← getEnv
--   let d ← e.find? nm
--   let tt ← isStructureLike e nm
--   let u := mkLevelParam `u
--   let (M, mvarId) ← asserti mvarId `M (mkSort (mkLevelSucc u)) (mkConst `PUnit [mkLevelSucc u])
--   let eStr ← mkAppN (mkConst nm [u]) #[mkFVar M]
--   let (h, mvarId, m2) ← assertm mvarId `h eStr
--   let l ← cases mvarId h
--   let info := l.get! 0
--   let mvarId := info.mvarId
--   withMVarContext mvarId do
--   let lctx ← getLCtx
--   let fieldExprs := info.fields
--   let fields := fieldExprs.map Expr.fvarId!
--   let ldecls := fields.map λ e => lctx.fvarIdToDecl.find! e
--   let axiom_fields ← fieldExprs.mapM isProof
--   let types ← fieldExprs.mapM inferType
--   let depends := types.map λ tp => tp.ListFvarIds
--   let fieldData := ldecls.zipWith5 FieldData.mk fieldExprs types depends axiom_fields
--   IO.println f!"field data: {← fieldData.mapM ppFieldData}"
--   return (mvarId, m2, fieldData)


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

-- syntax (name := struc) "struc" : tactic
-- @[tactic «struc»] def evalStruc : Tactic := fun stx => do
--   match stx with
--   | `(tactic| struc) => withMainContext do
--     let mvarId ← getMainGoal
--     let (m1, m2, data) ← strucTacticM mvarId
--     let l ← getUnsolvedGoals
--     setGoals (m1::m2::l)
--   | _ => throwUnsupportedSyntax

syntax (name := isSubclass) "isSubclass " ident ident : tactic
@[tactic «isSubclass»] def evalIsSubclass : Tactic := fun stx => do
  match stx with
  | `(tactic| isSubclass $nm1 $nm2) => withMainContext do
    let mvarId ← getMainGoal
    let (mvarId, m1, m2) ← Meta.isSubclass mvarId nm1.getId nm2.getId
    let l ← getUnsolvedGoals
    setGoals (mvarId::m1::m2::l)
  | _ => throwUnsupportedSyntax

/-! We define two notions of commutative monoids, the first is right-unital and the second is both left-unital and right-unital. -/

class comm_monoid1 (M : Type _) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(one : M)
(mul_one : ∀ x, mul x one = x)

class comm_monoid2 (M : Type _) :=
(one : M)
(mul : M → M → M)
(mul_one : ∀ x, mul x one = x)
(one_mul_one : mul one one = one)
(one_mul : ∀ x, mul one x = x)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)


-- example : Unit := by
--   struc
--   exact ()
--   admit

example : Unit := by
  isSubclass comm_monoid1 comm_monoid2
  isSubclass comm_monoid2 comm_monoid1
  exact ()
  admit
  admit
  admit
  admit

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
