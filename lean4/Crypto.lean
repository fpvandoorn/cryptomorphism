import Lean.Expr

namespace List
universes u v w x y z

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

open Lean
structure FieldData where
(local_constant : Expr)
(type : Expr)
(depends : NameSet)
(is_prop : Bool)



namespace Lean
namespace Name

def updateSuffix (f : String → String) : Name → Name
| str n s _ => mkStr n (f s)
| n         => n

end Name

namespace Expr

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
  The `Nat` passed to `f` is the binder depth.  -/
def foldAtomic {α : Type u} : Expr → α → (Expr → Nat → α → α) → α
| e, x, f => foldAtomicAux e f 0 x

def foldAux {α : Type u} : Expr → (Expr → Nat → α → α) → Nat → α → α
| b@(app fn e d),      f, l, x => foldAux e f l $ foldAux fn f l $ f b l x
| b@(lam v t e d),     f, l, x => foldAux e f (l+1) $ foldAux t f l $ f b l x
| b@(forallE v t e d), f, l, x => foldAux e f (l+1) $ foldAux t f l $ f b l x
| b@(letE v t a e d),  f, l, x => foldAux e f (l+1) $ foldAux a f l $ foldAux t f l $ f b l x
| b@(mdata m e d),     f, l, x => foldAux e f l $ f b l x
| b@(proj n k e d),    f, l, x => foldAux e f l $ f b l x
| e,                   f, l, x => f e l x

/-- `fold e x f` folds `f` over all subexpressions of `e`. The `nat` passed to `f`
  is the binder depth.  -/
def fold {α : Type u} : Expr → α → (Expr → Nat → α → α) → α
| e, x, f => foldAux e f 0 x

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
  The `Nat` passed to `f` is the binder depth.  -/
def foldSome {α : Type u} : Expr → α → (Expr → Nat → α → Option α) → α
  | e, x, f => foldSomeAux e f 0 x

def replaceAux : (Expr → Nat → Option Expr) → Nat → Expr → Expr
| f, l, b@(app fn e d)      => (f b l).getD $ app (replaceAux f l fn) (replaceAux f l e) d
| f, l, b@(lam v t e d)     => (f b l).getD $ lam v (replaceAux f l t) (replaceAux f l e) d
| f, l, b@(forallE v t e d) => (f b l).getD $ forallE v (replaceAux f l t) (replaceAux f l e) d
| f, l, b@(letE v t a e d)  => (f b l).getD $ letE v (replaceAux f l t) (replaceAux f l a) (replaceAux f l e) d
| f, l, b@(mdata m e d)     => (f b l).getD $ mdata m (replaceAux f l e) d
| f, l, b@(proj n k e d)    => (f b l).getD $ proj n k (replaceAux f l e) d
| f, l, e                   => (f e l).getD e

/-- `replace e f`:
 traverse over an expr `e` with a function `f` which can decide to replace subexpressions or not.
 For each subexpression `s` in the expression tree, `f s n` is called where `n` is how many binders are present above the given subexpression `s`.
 If `f s n` returns `none`, the children of `s` will be traversed.
 Otherwise if `some s'` is returned, `s'` will replace `s` and this subexpression will not be traversed further.
 -/
def replace : Expr → (Expr → Nat → Option Expr) → Expr
| e, f => e.replaceAux f 0

-- /-- Replace `nm args` for `nm` in `nms` by the Expression in the `NameMap`. -/
-- def replaceConst (e : Expr) (nms : NameMap Expr) (args : List Expr) : Expr :=
-- e.replace $ λ subterm n =>
--   let data := nms.findSubterm.getAppFn.constName
--   if data.isSome && (subterm.getAppArgs = args) then data.iget else none

/-- Returns the pretty Names of all local constants in an Expression. -/
def ListLocalConstPrettyNames (e : Expr) : NameSet :=
e.foldAtomic NameSet.empty $ λ e' _ es => if e'.isFVar then es.insert e'.fvarId! else es

end Expr

namespace NameSet

/-- Erase a name from a NameSet -/
@[inline] def erase (t : NameSet) (a : Name) : NameSet :=
Std.RBTree.erase t a

/-- Erase a list of names from a NameSet -/
def eraseList (ns : NameSet) (nms : List Name) : NameSet :=
nms.foldl NameSet.erase ns

end NameSet
end Lean