import Lean.Expr
import Lean.Meta.Tactic
import Lean.LocalContext

namespace List
universe u v w x y z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ε : Type y} {ζ : Type z}

def zipWith3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
| x::xs, y::ys, z::zs => f x y z :: zipWith3 f xs ys zs
| _,     _,     _     => []

def zipWith4 (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
| x::xs, y::ys, z::zs, u::us => f x y z u :: zipWith4 f xs ys zs us
| _,     _,     _,     _     => []

def zipWith5 (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
| x::xs, y::ys, z::zs, u::us, v::vs => f x y z u v :: zipWith5 f xs ys zs us vs
| _,     _,     _,     _,     _     => []

end List

namespace Array
universe u v w x y z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ε : Type y} {ζ : Type z}

def zipWith3 (f : α → β → γ → δ) : Array α → Array β → Array γ → Array δ
| as, bs, cs => zipWith (zipWith as bs f) cs id

def zipWith4 (f : α → β → γ → δ → ε) : Array α → Array β → Array γ → Array δ → Array ε
| as, bs, cs, ds => zipWith (zipWith (zipWith as bs f) cs id) ds id

def zipWith5 (f : α → β → γ → δ → ε → ζ) : Array α → Array β → Array γ → Array δ → Array ε → Array ζ
| as, bs, cs, ds, es => zipWith (zipWith (zipWith (zipWith as bs f) cs id) ds id) es id

end Array

open Lean
structure FieldData where
(fvar : Expr)
(type : Expr)
(depends : NameSet)
(isProp : Bool)



namespace Lean
namespace Name

def updateSuffix (f : String → String) : Name → Name
| str n s _ => mkStr n (f s)
| n         => n

end Name

namespace Expr

/-- Warning: very slow performance! -/
def foldAtomicAux {α : Type u} : Expr → (Expr → Nat → α → α) → Nat → α → α
| app fn e d,      f, l, x => foldAtomicAux e f l $ foldAtomicAux fn f l x
| lam v t e d,     f, l, x => foldAtomicAux e f (l+1) $ foldAtomicAux t f l x
| forallE v t e d, f, l, x => foldAtomicAux e f (l+1) $ foldAtomicAux t f l x
| letE v t a e d,  f, l, x =>
    foldAtomicAux e f (l+1) $ foldAtomicAux a f l $ foldAtomicAux t f l x
| mdata m e d,     f, l, x => foldAtomicAux e f l x
| proj n k e d,    f, l, x => foldAtomicAux e f l x
| e,               f, l, x => f e l x

/-- `foldAtomic e x f` folds `f` over all atomic subexpressions of `e`.
  The `Nat` passed to `f` is the binder depth.

Warning: very slow performance! -/
def foldAtomic {α : Type u} : Expr → α → (Expr → Nat → α → α) → α
| e, x, f => foldAtomicAux e f 0 x

/-- Warning: very slow performance! -/
def foldAux {α : Type u} : Expr → (Expr → Nat → α → α) → Nat → α → α
| b@(app fn e d),      f, l, x => foldAux e f l $ foldAux fn f l $ f b l x
| b@(lam v t e d),     f, l, x => foldAux e f (l+1) $ foldAux t f l $ f b l x
| b@(forallE v t e d), f, l, x => foldAux e f (l+1) $ foldAux t f l $ f b l x
| b@(letE v t a e d),  f, l, x => foldAux e f (l+1) $ foldAux a f l $ foldAux t f l $ f b l x
| b@(mdata m e d),     f, l, x => foldAux e f l $ f b l x
| b@(proj n k e d),    f, l, x => foldAux e f l $ f b l x
| e,                   f, l, x => f e l x

/-- `fold e x f` folds `f` over all subexpressions of `e`. The `nat` passed to `f`
  is the binder depth.

Warning: very slow performance! -/
def fold {α : Type u} : Expr → α → (Expr → Nat → α → α) → α
| e, x, f => foldAux e f 0 x

/-- Warning: very slow performance! -/
def foldSomeAux {α : Type u} : Expr → (Expr → Nat → α → Option α) → Nat → α → α
| b@(app fn e d),      f, l, x => (f b l x).getD $ foldSomeAux e f l $ foldSomeAux fn f l x
| b@(lam v t e d),     f, l, x => (f b l x).getD $ foldSomeAux e f (l+1) $ foldSomeAux t f l x
| b@(forallE v t e d), f, l, x => (f b l x).getD $ foldSomeAux e f (l+1) $ foldSomeAux t f l x
| b@(letE v t a e d),  f, l, x =>
  (f b l x).getD $ foldSomeAux e f (l+1) $ foldSomeAux a f l $ foldSomeAux t f l x
| b@(mdata m e d),     f, l, x => (f b l x).getD $ foldSomeAux e f l x
| b@(proj n k e d),    f, l, x => (f b l x).getD $ foldSomeAux e f l x
| e,                   f, l, x => (f e l x).getD x

/-- `fold e x f` folds `f` over all subexpressions of `e`.
  If `f` returns `none` then the subexpressions of `f` are traversed.
  The `Nat` passed to `f` is the binder depth.

Warning: very slow performance! -/
def foldSome {α : Type u} : Expr → α → (Expr → Nat → α → Option α) → α
  | e, x, f => foldSomeAux e f 0 x

/-- Replace `nm args` for `nm` in `nms` by the expression in the `NameMap`. -/
def replaceConst (e : Expr) (nms : NameMap Expr) (args : Array Expr) : Expr :=
e.replace $ λ subterm =>
  let data := nms.find? subterm.getAppFn.constName!
  if data.isSome && subterm.getAppArgs == args then data.get! else none

/-- Returns the pretty Names of all local constants in an expression. -/
def ListFvarIds (e : Expr) : NameSet :=
e.foldAtomic NameSet.empty $ λ e' _ es => if e'.isFVar then es.insert e'.fvarId! else es

end Expr

namespace NameSet

/-- Erase a Name from a NameSet -/
@[inline] def erase (t : NameSet) (a : Name) : NameSet :=
Std.RBTree.erase t a

/-- Erase a List of names from a NameSet -/
def eraseList (ns : NameSet) (nms : List Name) : NameSet :=
nms.foldl NameSet.erase ns

end NameSet
end Lean

open Lean.Meta
/-- `isIn e l` tests whether `e` is definitionally equal to an expression in `l`. -/
def isIn (e : Expr) (es : Array Expr) : MetaM Bool :=
es.foldrM (λ e' b => do b || (← isDefEq e e')) false

#check @HAndThen.hAndThen
#check @Bind.bind
#check Lean.Meta.isDefEq
#check @SeqRight.seqRight
#check assert
#check Lean.MetaM
#check Expr
#check sorryAx

def AddToContext (lctx : LocalContext) (h : Name) (t : Expr) : MetaM (LocalContext × FVarId) := do
  let nm ← mkFreshFVarId
  let new_lctx := lctx.addDecl (mkLocalDeclEx 0 nm h t BinderInfo.default)
  return (new_lctx, nm)

#check @getEnv
#check Lean.Environment
#check Array
#check Array.zipWith
/-- Add fields to context, and returns data -/
def AddFieldsToContext (lctx : LocalContext) (nm : Name) (pref : Name) (args : Array Expr) :
  MetaM (LocalContext × Array FieldData) := do
  let goal ← mkFreshMVarId -- no
  let e ← getEnv
  let d ← e.find? nm
--   guard (isStructureLike e nm)
  let e_str ← mkAppN (mkConst nm) args
  let (lctx, cls) ← AddToContext lctx pref e_str
  return (lctx, #[])
--   let ctors ← cases goal cls
--   let fieldExprs := (ctors.map $ λ x => x.fields).get! 0
--   let fields := fieldExprs.map Expr.fvarId!
--   let axiom_fields ← fieldExprs.mapM isProof
--   let types ← fieldExprs.mapM inferType
--   let depends := types.map λ tp => tp.ListFvarIds
--   return (fieldExprs.zipWith4 FieldData.mk types depends axiom_fields)

#check Lean.LocalContext.getFVar!
open Lean.LocalContext

#check Std.PersistentHashMap
#check String
#check LocalDecl
-- for testing
def trivialMapping (lctx : LocalContext) (fields1 fields2 : Array FieldData) : MetaM $ Array FVarId × Array LocalDecl := do
  let data_fields := fields1.filter $ λ info => !info.isProp
  let map1 ← data_fields.map λ info => info.fvar.fvarId!
  let map2 ← data_fields.map λ info => lctx.get! (info.fvar.fvarId!.updateSuffix $ λ s => "h2" ++ s)
  return (map1, map2)

#check @Lean.throwError
-- todo
def allMappings (fields1 fields2 : Array FieldData) : MetaM $ List $ List (FVarId × Expr) := do
 let data_fields1 := fields1.filter $ λ info => !info.isProp
 let data_fields2 := fields2.filter $ λ info => !info.isProp
 throwError "todo"


/-- Find which axioms in fields1 also occur in fields2 under the renaming `mapping`. -/
def matchingAxioms (fields1 fields2 : Array FieldData) (mapping : Array (FVarId × LocalDecl)) :
  MetaM $ Array FieldData := do
  let propFields := fields1.filter λ info => info.isProp
  let types2 : Array Expr := fields2.filterMap λ info => if info.isProp then info.type else none
  let same ← propFields.filterM λ info => isIn (info.type.replaceFVars _ _) types2
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
def is_subclass (nm1 nm2 : Name) (show_state := false) : MetaM Unit := do
  --(if show_state then id else retrieve : MetaM Unit → MetaM Unit) $
  let lctx := LocalContext.mkEmpty ()
  let (lctx, M) ← AddToContext lctx `M (mkSort $ mkLevelSucc $ mkLevelParam `u)
  let (lctx, info1) ← AddFieldsToContext lctx nm1 `h1 #[mkFVar M]
  let (lctx, info2) ← AddFieldsToContext lctx nm2 `h2 #[mkFVar M]
  let mapping ← trivialMapping lctx info1 info2
  let n ← matchingAxioms info1 info2 mapping
  let n_uniqs := n.map λ info => info.fvar.fvarId!
  let todo := info1.filter λ info => info.isProp && !n_uniqs.contains info.fvar.fvarId!
  if todo.isEmpty then
  IO.println s!"{nm1} is a trivial subclass of {nm2}: {nm2} has all the fields that {nm1} has." else do
  -- trace $ todo.map $ λ info => info.fvar.local_pp_name,
  -- let cannot_prove ← todo.filterM λ info => bnot <$> try_to_prove (info.type.instantiate_locals mapping),
  let cannotProve := todo
  -- trace $ cannot_prove.map $ λ info => info.fvar.local_pp_name,
  if cannotProve.isEmpty then
  IO.println s!"{nm1} is a subclass of {nm2}: {nm2} has all the data fields of {nm1}, and all the axioms of {nm1} can be proven from the axioms of {nm2}."
  else
  IO.println s!"Cannot prove the following axioms of {nm1} from the axioms of {nm2}:
  {cannotProve.map $ λ info => info.fvar.fvarId!}."

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

class comm_monoid2 (M : Type _) :=
(mul : M → M → M)
(mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z))
(mul_comm : ∀ x y, mul x y = mul y x)
(one : M)
(mul_one : ∀ x, mul x one = x)
(one_mul : ∀ x, mul one x = x)

#eval is_subclass `comm_monoid1 `comm_monoid2
/- Output: comm_monoid1 is a trivial subclass of comm_monoid2: comm_monoid2 has all the fields that comm_monoid1 has. -/

#eval is_subclass `comm_monoid2 `comm_monoid1
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
