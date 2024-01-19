import LeanColls.Data.List

open Std

namespace Pauline

def Ident := String
deriving DecidableEq, Hashable, Repr

inductive SCon
| int (n : Int)
| str (s : String)
deriving Repr

inductive Typ
| int | string
| exn
| prod (ts : List Typ)
| arr (dom cod : Typ)
| tyvar (id : Ident)
| tycon (name : Ident) (args : List Typ)
deriving BEq, Repr

inductive Pat
| wild
| bind (name : Ident)
| scon (sc : SCon)
| tuple (ps : List Pat)
| typed (p : Pat) (ty : Typ)
| layer (name : Ident) (ty : Option Typ) (p : Pat)
deriving Repr

instance : CoeHead Pat (List Pat) := ⟨([·])⟩

mutual
inductive Exp
| scon (sc : SCon)
| var (name : Ident)
| tuple (es : List Exp)
| raise (e : Exp)
| let_in (d : Dec) (e : Exp)
| app (fn : Exp) (arg : Exp)
| typed (e : Exp) (ty : Typ)
| ite (b : Exp) (t : Exp) (f : Exp)
| case (e : Exp) (clauses : List (Pat × Exp))
| lam (p : Pat) (body : Exp)
deriving Repr, Inhabited

inductive Dec
| val (p : Pat) (exp : Exp)
| valrec (p : Pat) (expPat : Pat) (expBody : Exp)
| «fun» (name : Ident) (pats : List.Nonempty Pat) (ret : Option Typ) (body : Exp)
deriving Repr
end

structure Prog where
  decls : List Dec
deriving Repr


instance : OfNat Exp n where
  ofNat := .scon (.int n)

instance : Coe Nat Exp where
  coe n := .scon (.int n)
