import Lean
import Crypto.Util

open Lean Elab Tactic Meta

namespace Crypto

/-- `isIn e l` tests whether `e` is definitionally equal to an expression in `l`. -/
def isIn (e : Expr) (es : Array Expr) : MetaM Bool :=
es.foldrM (init := false) λ e' b => do b || (← isDefEq e e')

-- #check getMVarType
-- #check assignExprMVar
-- #check liftMetaMAtMain
-- #check getMainGoal
-- #check withMainContext
-- #check evalGeneralize
-- #check Parser.Tactic.generalize

/- the data we record for each field -/
structure FieldData where
(decl : LocalDecl)
(fvar : Expr)
(type : Expr)
(depends : NameSet)
(isProp : Bool)
deriving Inhabited

/- additionally an expression that gives us the translation to another field -/
structure FieldMapping extends FieldData where
(tgt : Option Expr)

structure Context where
(target : Array FieldData)

structure State where
(mapping : Array FieldMapping)

open Std.Format

instance : ToFormat NameSet :=
⟨λ x => format x.toList⟩

instance : ToFormat FieldData :=
⟨λ ⟨a, b, c, d, e⟩ => group (nest 1 (format "⟨"  ++ format a ++ format "," ++ line ++ format b ++
format "," ++ line ++ format c ++ format "," ++ line ++ format d ++ format "," ++ line ++ format e
++ format "⟩"))⟩

namespace FieldData

def name (fields : FieldData) : Name :=
fields.decl.userName.head!

def toFieldMapping (fields : FieldData) : FieldMapping :=
{ toFieldData := fields, tgt := none }

end FieldData

namespace FieldMapping
def update (field : FieldMapping) (newM : Option Expr) : FieldMapping :=
if field.tgt.isNone then { field with tgt := newM } else field

def updateM (field : FieldMapping) (tac : MetaM (Option Expr)) : MetaM FieldMapping :=
if field.tgt.isNone then do
  let tgt ← tac
  return { field with tgt := tgt }
else
  return field

end FieldMapping

def ppFieldData (x : FieldData) : MetaM Format :=
do return group (nest 1 (format "⟨"  ++
format x.name ++ format "," ++ line ++
format (← ppExpr x.fvar) ++ format "," ++ line ++
format (← ppExpr x.type) ++ format "," ++ line ++
format (← x.depends.toList.mapM λ e => ppExpr (mkFVar e)) ++ format "," ++ line ++
format x.isProp ++ format "⟩"))

/-- make a field mapping with no connections. -/
def mkState (fields1 : Array FieldData) : State :=
{ mapping := fields1.map λ info => { toFieldData := info, tgt := none } }

namespace State

def done (st : State) : Bool :=
st.mapping.all (·.tgt.isSome)

def update (st : State) (f : FieldData → Option Expr) : State :=
{ mapping := st.mapping.map λ info => info.update (f info.toFieldData) }

def updateM (st : State) (f : FieldData → MetaM (Option Expr)) : MetaM State := do
  let fieldMapping ← st.mapping.mapM λ info => info.updateM (f info.toFieldData)
  return { mapping := fieldMapping }

def getDataMapping (st : State) : Array (Expr × Expr) :=
st.mapping.filterMap λ map => match map.tgt with
  | none => none
  | some e => if map.isProp then none else some (map.fvar, e)

def getMapping (st : State) : Array (Expr × Expr) :=
st.mapping.filterMap λ map => match map.tgt with
  | none => none
  | some e => some (map.fvar, e)

def missing (st : State) : Array FieldData :=
st.mapping.filterMap λ info => if info.tgt.isNone then some info.toFieldData else none

def missingData (st : State) : Array FieldData :=
st.mapping.filterMap λ info =>
  if info.tgt.isNone && !info.isProp then some info.toFieldData else none

end State

namespace Meta

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
  return (mvarId, m2, fieldData)

/-- map the data fields to data fields of the same name. -/
def trivialMapping (lctx : LocalContext) (st : State) (ctx : Context) : State :=
st.update $ λ info =>
  if info.isProp then none else
    ctx.target.findSome? λ info' => if info.name == info'.name then some info'.fvar else none

/-- map the data fields to data fields with the same type, if a unique such data field exists. -/
def uniqueMapping (lctx : LocalContext) (st : State) (ctx : Context) : MetaM State :=
st.updateM $ λ info => if info.isProp then return none else do
  let sources ← st.mapping.filterM λ info' => isDefEq info.type info'.type
  let targets ← ctx.target.filterM λ info' => isDefEq info.type info'.type
  return (if sources.size = 1 ∧ targets.size = 1 then some (targets.get! 0).fvar else none)

-- todo
def allMappings (fields1 fields2 : Array FieldData) : MetaM $ List $ List (FVarId × Expr) := do
 let dataFields1 := fields1.filter λ info => !info.isProp
 let dataFields2 := fields2.filter λ info => !info.isProp
 throwError "todo"

/-- Find which axioms in fields1 also occur in fields2 under the renaming `mapping`. -/
def matchingAxioms (st : State) (ctx : Context) : MetaM State := do
  -- let propFields := fields1.filter λ info => info.isProp
  let types2 : Array Expr := ctx.target.filterMap λ info => if info.isProp then info.type else none
  let fieldMapping ←
    st.mapping.mapM λ info => info.updateM $ do {
      -- types2.findM? λ e' => do b || (← isDefEq e e')

--todo:
      if (← isIn (info.type.instantiateFVars st.getDataMapping) types2) then
        return (some arbitrary) else return none }
  return { mapping := fieldMapping }

/-- some copy-pasted simp code -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

/-- some mostly copy-pasted simp code -/
def mkSimpContext (simpOnly := false) (starArg := true) : MetaM Simp.Context := do
  let ctx : Simp.Context :=
  { config      := {}
    simpLemmas  := if simpOnly then {} else (← getSimpLemmas)
    congrLemmas := (← getCongrLemmas) }
  if !starArg then
    return ctx
  else
    let hs ← getPropHyps
    let mut ctx := ctx
    for h in hs do
      let localDecl ← getLocalDecl h
      let fvarId := localDecl.fvarId
      let proof  := localDecl.toExpr
      let id     ← mkFreshUserName `h
      let simpLemmas ← ctx.simpLemmas.add #[] proof (name? := id)
      ctx := { ctx with simpLemmas }
    return ctx

/-- The tactic we use to automatically prove axioms. -/
def currentAutomation (mvarId : MVarId) : MetaM Unit := do
let newgoal ← simpTarget mvarId (← mkSimpContext false)

-- match (← simpTarget mvarId (← mkSimpContext false)) with
-- | some x => IO.println "failure!"
-- | none => IO.println "success!"

/-- Tries to prove `e` in the local context, returns tt if successful. -/
def tryToProve (mvarId : MVarId) (tac : MVarId → MetaM Unit) (e : Expr) : MetaM (Option Expr) :=
withoutModifyingState do
  let (fvar, mvarId, m2) ← assertm mvarId `h e
  try
    tac m2
    -- IO.println s!"is assigned: {← isExprMVarAssigned m2}"
    let some e ← getExprMVarAssignment? m2 | return none
    let e ← instantiateMVars e
    if (← e.hasExprMVar) then return none else return some e
  catch err =>
    return none

/-- Tests whether nm1 is a subclass of nm1. Currently the data fields must have the same Name for
this tactic to work. -/
def isSubclass (mvarId : MVarId) (nm1 nm2 : Name) (show_state := false) (trace := true) :
  MetaM (MVarId × MVarId × MVarId × State) := do
  let u := mkLevelParam `u
  let (M, mvarId) ← asserti mvarId `M (mkSort (mkLevelSucc u)) (mkConst `PUnit [mkLevelSucc u])
  let (mvarId, m1, fields1) ← AddFieldsToContext mvarId nm1 [u] #[mkFVar M]
  let (mvarId, m2, fields2) ← AddFieldsToContext mvarId nm2 [u] #[mkFVar M]
  -- let mapping := fields1.map (·.toFieldMapping)
  withMVarContext mvarId do
  let st := mkState fields1
  let ctx : Context := ⟨fields2⟩
  let st ← uniqueMapping (← getLCtx) st ctx
  let st ← trivialMapping (← getLCtx) st ctx
  let st ← matchingAxioms st ctx
  let st ← st.updateM λ info =>
    tryToProve mvarId currentAutomation (info.type.instantiateFVars st.getDataMapping)
  if st.done then
    IO.println s!"{nm1} is a subclass of {nm2}"
  else
    IO.println s!"Cannot construct the following fields of {nm1} from {nm2}:
    {← st.missing.mapM λ info : FieldData => ppExpr info.fvar}."
  return (mvarId, m1, m2, st)

end Meta

syntax (name := guardHyp) "guardHyp " (" : " term)? : tactic
@[tactic guardHyp] def evalGuardHyp : Lean.Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| guardHyp $[: $ty]?) => do
    return ()
  | _ => throwUnsupportedSyntax

def isSubclassTac (nm1 nm2 : Name) : TacticM Unit := withMainContext do
let mvarId ← getMainGoal
let (mvarId, m1, m2, result) ← Meta.isSubclass mvarId nm1 nm2
let l ← getUnsolvedGoals
setGoals (mvarId::m1::m2::l)

syntax (name := isSubclass) "isSubclass " ident ident : tactic
syntax (name := isSubclassE) "isSubclass! " ident ident : tactic
@[tactic «isSubclass»] def evalIsSubclass : Tactic := fun stx =>
  match stx with
  | `(tactic| isSubclass $nm1 $nm2) => withoutModifyingState $ isSubclassTac nm1.getId nm2.getId
  | _ => throwUnsupportedSyntax
@[tactic «isSubclassE»] def evalIsSubclassE : Tactic := fun stx =>
  match stx with
  | `(tactic| isSubclass! $nm1 $nm2) => isSubclassTac nm1.getId nm2.getId
  | _ => throwUnsupportedSyntax


end Crypto

/-!
We define some notions of commutative monoids,
* the first is right-unital
* the second is right-unital, and then has a superfluous axiom `1 * 1 = 1`
* the third is both left-unital and right-unital.
* the fourth is with a implicit unit
* the fifth is denoted additively
-/

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
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)

class comm_monoid3 (M : Type _) :=
(one : M)
(mul : M → M → M)
(mul_one : ∀ x, mul x one = x)
(one_mul : ∀ x, mul one x = x)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)

class comm_monoid4 (M : Type _) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(exists_one : ∃ one, ∀ x, mul x one = x)

class comm_monoid5 (M : Type _) :=
(add : M → M → M)
(add_assoc : ∀ x y z, add (add x y) z = add x (add y z))
(add_comm : ∀ x y, add x y = add y x)
(zero : M)
(add_zero : ∀ x, add x zero = x)

example : Unit := by
  isSubclass comm_monoid1 comm_monoid2 -- subclass
  isSubclass comm_monoid2 comm_monoid1 -- subclass
  isSubclass comm_monoid1 comm_monoid3 -- subclass
  isSubclass comm_monoid3 comm_monoid1 -- missing: one_mul
  isSubclass comm_monoid1 comm_monoid5 -- subclass
  isSubclass comm_monoid5 comm_monoid1 -- subclass
  isSubclass comm_monoid4 comm_monoid1 -- missing: exists_one
  isSubclass comm_monoid1 comm_monoid4 -- missing: one, mul_one
  exact ()

/-! As a sanity check: we cannot prove commutativity on an arbitrary monoid. -/

class my_monoid (M : Type _) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(one : M)
(mul_one : ∀ x, mul x one = x)

example : Unit := by
  isSubclass my_monoid comm_monoid1 -- subclass
  isSubclass comm_monoid1 my_monoid -- missing (as expected): mul_comm
  exact ()

/-! If two data fields have the same type, we try to get the one with the same name.
In the future we could look at which choice will make more axioms overlap. -/

class my_almost_ring (M : Type _) :=
(add : M → M → M)
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(one : M)
(mul_one : ∀ x, mul x one = x)

example : Unit := by
  isSubclass comm_monoid1 my_almost_ring -- subclass
  isSubclass my_almost_ring comm_monoid1 -- missing (as expected): add
  exact ()