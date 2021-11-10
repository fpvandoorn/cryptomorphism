import Lean
import Crypto.Util

open Lean Elab Tactic Meta

namespace Crypto

/-- Return true iff `constName` is the a non-recursive inductive datatype without indices
  that has only one constructor. If `includeProp` is false, we also check that the datatype is
  not `Prop` or `Sort*` -/
def isVeryStructureLike (env : Environment) (constName : Name) (includeProp := true) : Bool :=
  match env.find? constName with
  | some d@(ConstantInfo.inductInfo { isRec := false, ctors := [ctor], numIndices := 0, .. }) =>
    includeProp || d.toConstantVal.type.getForallBody.level!.isASucc
  | _ => false

/-- Good names for new hypotheses when casing on a variable with name `nm` and type `constName`. -/
def giveNames (env : Environment) (constName nm : Name) : Array Name :=
  match getStructureInfo? env constName with
  | some p => p.fieldNames.map λ s => nm.appendAfter ("_" ++ s.toString)
  | _ => if constName == `Exists then #[nm.appendAfter "_val", nm.appendAfter "_prop"] else #[]


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
deriving Inhabited

structure Context where
(target : Array FieldData)
deriving Inhabited

structure State where
(mapping : Array FieldMapping)
deriving Inhabited

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
format (← Meta.ppExpr x.fvar) ++ format "," ++ line ++
format (← Meta.ppExpr x.type) ++ format "," ++ line ++
format (← x.depends.toList.mapM λ e => Meta.ppExpr (mkFVar ⟨e⟩)) ++ format "," ++ line ++
format x.isProp ++ format "⟩"))

/-- make a field mapping with no connections. -/
def mkState (fields1 : Array FieldData) : State :=
{ mapping := fields1.map (·.toFieldMapping) }

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

def traceMapping (st : State) : MetaM (Array Format) :=
st.mapping.mapM λ info : FieldMapping =>
  if info.tgt.isSome then Meta.ppExpr info.tgt.get! else return Format.nil


end State

namespace Meta

def fieldDataofCaseGoals (l : Array CasesSubgoal) : MetaM (MVarId × Array FieldData) := do
  let casegoal := l.get! 0
  let mvarId := casegoal.mvarId
  withMVarContext mvarId do
  let lctx ← getLCtx
  let fieldExprs := casegoal.fields
  let fields := fieldExprs.map Expr.fvarId!
  let ldecls := fields.map λ e => lctx.fvarIdToDecl.find! e
  let axiom_fields ← fieldExprs.mapM isProof
  let types ← fieldExprs.mapM inferType
  let depends := types.map λ tp => tp.ListFvarIds
  let fieldData := ldecls.zipWith5 FieldData.mk fieldExprs types depends axiom_fields
  return (mvarId, fieldData)

def updateFieldData (l : Array CasesSubgoal) (fields : Array FieldData) :
  MetaM (Array FieldData) := do
  let casegoal := l.get! 0
  let mvarId := casegoal.mvarId
  let fieldData ← withMVarContext mvarId $ fields.mapM λ info =>
    match casegoal.subst.find? info.fvar.fvarId! with
    | (some e) => do
      let lctx ← getLCtx
      let id := e.fvarId!
      let ldecl := lctx.fvarIdToDecl.find! id
      let t ← inferType e
      let depends := NameSet.empty -- todo
      return ⟨ldecl, e, t, depends, info.isProp⟩
    | none => return info
  return fieldData

def AddFieldsToContext (mvarId : MVarId) (nm : Name) (us : List Level) (args : Array Expr) :
  MetaM (MVarId × MVarId × Array FieldData) := do
  let env ← getEnv
  let d ← env.find? nm
  let true ← isStructureLike env nm
  let eStr ← mkAppN (mkConst nm us) args
  let (h, mvarId, m2) ← assertm mvarId `h eStr
  let l ← cases mvarId h
  let (mvarId, fieldData) ← fieldDataofCaseGoals l
  return (mvarId, m2, fieldData)

/-- map the data fields to data fields of the same name. -/
def trivialMapping (st : State) (ctx : Context) : State :=
st.update $ λ info =>
  if info.isProp then none else
    ctx.target.findSome? λ info' => if info.name == info'.name then some info'.fvar else none

/-- map the data fields to data fields with the same type, if a unique such data field exists. -/
def uniqueMapping (st : State) (ctx : Context) : MetaM State :=
st.updateM $ λ info => if info.isProp then return none else do
  let sources ← st.mapping.filterM λ info' => isDefEq info.type info'.type
  let targets ← ctx.target.filterM λ info' => isDefEq info.type info'.type
  return (if sources.size = 1 ∧ targets.size = 1 then some (targets.get! 0).fvar else none)

set_option pp.all true
partial def caseOnStructures (mvarId : MVarId) (st : Array FieldData) (ctx : Context)
  (includeProp := true) :
  MetaM (MVarId × Array FieldData) := do
  let env ← getEnv
  let info? := st.find? λ info =>
    info.type.getAppFn.constName?.any (isVeryStructureLike env · includeProp)
  match info? with
  | some info => do
    let rest := st.filter λ info' => info'.fvar.fvarId! != info.fvar.fvarId!
    let str := info.type.getAppFn.constName!
    -- todo: there seems to be a bug with the given names when transitively extending structures. Do we need to skip fields?
    -- IO.println (giveNames env str info.name)
    let l ← cases mvarId info.fvar.fvarId! #[⟨false, (giveNames env str info.name).toList⟩]
    let (mvarId, fieldData) ← fieldDataofCaseGoals l
    let rest ← updateFieldData l rest
    caseOnStructures mvarId (rest ++ fieldData) ctx includeProp
  | none =>
    return (mvarId, st)


/-- Find which axioms of the first structure that occur in the second structure. -/
def matchingAxioms (st : State) (ctx : Context) : MetaM State := do
  let targetTypes : Array (Expr × Expr) := ctx.target.filterMap λ info =>
    if info.isProp then (info.fvar, info.type) else none
  st.updateM λ info => do
    let e := info.type.instantiateFVars st.getDataMapping
    match (← targetTypes.findM? λ (e', t) => isDefEq e t) with
    | some (e, t) => return (some e)
    | none => return none

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

/-- Tries to prove `e` in the local context, returns the proof if successful. -/
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
def isSubclass (mvarId : MVarId) (nm1 nm2 : Name) (trace := false) :
  MetaM (MVarId × MVarId × MVarId × State) := do
  let u := mkLevelParam `u
  let (M, mvarId) ← asserti mvarId `M (mkSort (mkLevelSucc u)) (mkConst `PUnit [mkLevelSucc u])
  let (mvarId, m2, fields2) ← AddFieldsToContext mvarId nm2 [u] #[mkFVar M]
  let (mvarId, fields2) ← caseOnStructures mvarId fields2 ⟨#[]⟩ false
  let ctx : Context := ⟨fields2⟩
  if trace then IO.println s!"cases on fields class 2: {← ctx.target.map (·.name)}"
  let (mvarId, m1, fields1) ← AddFieldsToContext mvarId nm1 [u] #[mkFVar M]
  let (mvarId, fields1) ← caseOnStructures mvarId fields1 ctx
  let st := mkState fields1
  withMVarContext mvarId do
  let st ← uniqueMapping st ctx
  let st := trivialMapping st ctx
  if trace then IO.println s!"map of data: {← st.traceMapping}"
  let (mvarId, fields2) ← caseOnStructures mvarId fields2 ⟨#[]⟩ -- is this dangerous?
  let ctx : Context := ⟨fields2⟩
  withMVarContext mvarId do
  let ctx : Context := ⟨fields2⟩
  let st ← matchingAxioms st ctx
  let st ← st.updateM λ info => if !info.isProp then return none else
    tryToProve mvarId currentAutomation (info.type.instantiateFVars st.getDataMapping)
  if trace then IO.println s!"map: {← st.traceMapping}"
  return (mvarId, m1, m2, st)

end Meta

syntax (name := guardHyp) "guardHyp " (" : " term)? : tactic
@[tactic guardHyp] def evalGuardHyp : Lean.Elab.Tactic.Tactic := fun stx =>
  match stx with
  | `(tactic| guardHyp $[: $ty]?) => do
    return ()
  | _ => throwUnsupportedSyntax

def isSubclassTac (nm1 nm2 : Name) (trace := false) : TacticM Unit := withMainContext do
let mvarId ← getMainGoal
let (mvarId, m1, m2, st) ← Meta.isSubclass mvarId nm1 nm2 trace
if st.done then IO.println s!"{nm1} is a subclass of {nm2}"
else IO.println s!"Cannot construct the following fields of {nm1} from {nm2}:
{st.missing.map (·.name)}."
let l ← getUnsolvedGoals
setGoals (mvarId::m1::m2::l)

def cryptomorphicTac (nm1 nm2 : Name) (trace := false) : TacticM Unit := withMainContext do
let mvarId ← getMainGoal
let (mvarId, m1, m2, st1) ← Meta.isSubclass mvarId nm1 nm2 trace
let (mvarId, m3, m4, st2) ← Meta.isSubclass mvarId nm2 nm1 trace
if st1.done && st2.done then IO.println s!"{nm1} and {nm2} are cryptomorphic"
else do
  IO.println s!"Cannot prove that {nm1} and {nm2} are cryptomorphic"
  if !st1.done then
    IO.println s!"{nm2} → {nm1}: cannot construct {st1.missing.map (·.name)}"
  if !st2.done then
    IO.println s!"{nm1} → {nm2}: Cannot construct {st2.missing.map (·.name)}"
let l ← getUnsolvedGoals
setGoals (mvarId::m1::m2::m3::m4::l)

syntax (name := isSubclass) "isSubclass " ident ident : tactic
syntax (name := isSubclassE) "isSubclass! " ident ident : tactic
@[tactic «isSubclass»] def evalIsSubclass : Tactic := fun stx =>
  match stx with
  | `(tactic| isSubclass $nm1 $nm2) => withoutModifyingState $ isSubclassTac nm1.getId nm2.getId
  | _ => throwUnsupportedSyntax
@[tactic «isSubclassE»] def evalIsSubclassE : Tactic := fun stx =>
  match stx with
  | `(tactic| isSubclass! $nm1 $nm2) => isSubclassTac nm1.getId nm2.getId true
  | _ => throwUnsupportedSyntax


syntax (name := cryptomorphic) "cryptomorphic " ident ident : tactic
@[tactic «cryptomorphic»] def evalCryptomorphic : Tactic := fun stx =>
  match stx with
  | `(tactic| cryptomorphic $nm1 $nm2) => withoutModifyingState $ cryptomorphicTac nm1.getId nm2.getId
  | _ => throwUnsupportedSyntax

end Crypto
open Crypto

/-!
## Demo and tests

We define some notions of commutative Monoids,
(1) right-unital
(2) right-unital, and then has a superfluous axiom `1 * 1 = 1`
(3) both left-unital and right-unital.
(4) denoted additively
(5) with a unit given by an existential quantifier (`∃ one, ...`)
(6) by extending a `Monoid` structure.
-/

class Zero (α : Type u) where
  zero : α

instance [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

class One (α : Type u) where
  one : α

instance [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

class CommMonoid1 (M : Type _) extends Mul M, One M :=
(mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z))
(mul_comm : ∀ x y : M, x * y = y * x)
(mul_one : ∀ x : M, x * 1 = x)

class CommMonoid2 (M : Type _) extends Mul M, One M :=
(mul_one : ∀ x : M, x * 1 = x)
(one_mul_one : 1 * 1 = 1)
(mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z))
(mul_comm : ∀ x y : M, x * y = y * x)

class CommMonoid3 (M : Type _) extends Mul M, One M :=
(one_mul : ∀ x : M, 1 * x = x)
(mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z))
(mul_comm : ∀ x y : M, x * y = y * x)

class CommMonoid4 (M : Type _) extends Add M, Zero M :=
(add_assoc : ∀ x y z : M, (x + y) + z = x + (y + z))
(add_comm : ∀ x y : M, x + y = y + x)
(add_zero : ∀ x : M, x + 0 = x)

class CommMonoid5 (M : Type _) extends Mul M :=
(mul_axioms : (∀ x y z : M, (x * y) * z = x * (y * z)) ∧ (∀ x y : M, x * y = y * x))
(exists_one : ∃ one : M, ∀ x : M, x * one = x)

class Monoid (M : Type _) extends Mul M, One M :=
(mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z))
(mul_one : ∀ x : M, x * 1 = x)

class CommMonoid6 (M : Type _) extends Monoid M :=
(mul_comm : ∀ x y : M, x * y = y * x)

open CommMonoid1

-- example (M : Type _) [CommMonoid1 M] (x : M) : 1 * x = 1 := by
--   simp [mul_comm]



example : True := by
  cryptomorphic CommMonoid1 CommMonoid2 -- yes
  cryptomorphic CommMonoid1 CommMonoid3 -- mul_one, one_mul [need better automation]
  cryptomorphic CommMonoid1 CommMonoid4 -- yes
  cryptomorphic CommMonoid1 CommMonoid5 -- one, mul_one [need support for existentials]
  cryptomorphic CommMonoid1 CommMonoid6 -- yes
  trivial

/-! As a sanity check: we cannot prove commutativity on an arbitrary Monoid. -/

class MyMonoid (M : Type _) extends Mul M :=
(mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z))
(one : M)
(mul_one : ∀ x : M, x * one = x)

example : True := by
  cryptomorphic MyMonoid CommMonoid1 -- missing (expected): mul_comm
  trivial

/-!
If two data fields have the same type, we try to get the one with the same name.
In the future we could look at which choice will make more axioms overlap.
-/

class MyAlmostRing (M : Type _) extends Mul M :=
(add : M → M → M)
(mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z))
(mul_comm : ∀ x y : M, x * y = y * x)
(one : M)
(mul_one : ∀ x : M, x * one = x)

example : True := by
  cryptomorphic CommMonoid1 MyAlmostRing -- missing (expected): add
  trivial

/-! Test which "fields" are missing when inside nested structures. -/

class CommMonoidBundled1 (M : Type _) extends Mul M :=
(mul_assoc : ∀ x y z : M, (x * y) * z = x * (y * z))
(mul_comm : ∀ x y : M, x * y = y * x)
(one_axioms : ∃ one : M, (∀ x : M, x * one = x) ∧ (∀ x : M, x * x = one))

class CommMonoidBundled2 (M : Type _) :=
(data : (M → M → M) × M)
(mul_assoc : ∀ x y z : M, data.1 (data.1 x y) z = data.1 x (data.1 y z))
(mul_comm : ∀ x y : M, data.1 x y = data.1 y x)
(mul_one : ∀ x : M, data.1 x data.2 = x)


example : True := by
  cryptomorphic CommMonoidBundled1 CommMonoid1 -- missing (expected): one_axioms_prop_right
  -- missing: one, one_mul [need support for existentials]
  cryptomorphic CommMonoidBundled2 CommMonoid1 -- yesss
  trivial