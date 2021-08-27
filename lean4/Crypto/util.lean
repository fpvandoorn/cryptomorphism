import Lean

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

namespace Lean

namespace BinderInfo
protected def «open» : BinderInfo → Char
| default        => '('
| implicit       => '{'
| strictImplicit => '⦃'
| instImplicit   => '['
| auxDecl        => '('

protected def close : BinderInfo → Char
| default        => ')'
| implicit       => '}'
| strictImplicit => '⦄'
| instImplicit   => ']'
| auxDecl        => ')'

end BinderInfo


namespace LocalDecl
instance : ToString LocalDecl :=
⟨λ d => match d with
  | cdecl i f n t bi => s!"{bi.open}{n} : {t}{bi.close}"
  | ldecl i f n t v b => s!"({n} : {t} := {v})"⟩

end LocalDecl

namespace Name

def updateSuffix (f : String → String) : Name → Name
| str n s _ => mkStr n (f s)
| n         => n

def head! : Name → String
| str anonymous s _ => s
| str n s _         => head! n
| num anonymous s _ => toString s
| num n s _         => head! n
| anonymous         => panic! "Name.anonymous doesn't have a head"


end Name

namespace Level

/-- Is a level equal to a succ, when all (meta)variables are instantiated with 0? -/
def isASucc : Level → Bool
| succ _ _   => true
| max u v _  => isASucc u || isASucc v
| imax u v _ => isASucc v
| _          => false

end Level

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

/-- Replace occurrences of the free variables `fvars` in `e` with `vs` -/
def instantiateFVars (e : Expr) (fvars : Array (Expr × Expr)) : Expr :=
e.replaceFVars (fvars.map (·.fst)) $ fvars.map (·.snd)

def level! : Expr → Level
| sort u _ => u
| _        => arbitrary

end Expr

namespace NameSet

/-- Erase a Name from a NameSet -/
@[inline] def erase (t : NameSet) (a : Name) : NameSet :=
Std.RBTree.erase t a

/-- Erase a List of names from a NameSet -/
def eraseList (ns : NameSet) (nms : List Name) : NameSet :=
nms.foldl NameSet.erase ns

end NameSet

namespace Meta

instance : Inhabited CasesSubgoal :=
⟨arbitrary, Name.anonymous⟩

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

end Meta

end Lean
