import LeanColls.Data.List

open Std

namespace Pauline

def Ident := String
deriving DecidableEq, Hashable, Repr, ToString, Inhabited

inductive SCon
| int (n : Int)
| bool (b : Bool) -- temp
| str (s : String)
deriving Repr, DecidableEq

inductive Typ
| int | string | bool
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
| extern (name : String) (exe : List SCon → Exp) -- a built in function/op
deriving Inhabited

inductive Dec
| val (p : Pat) (exp : Exp)
| valrec (p : Pat) (expPat : Pat) (expBody : Exp)
| «fun» (name : Ident) (pats : List.Nonempty Pat) (ret : Option Typ) (body : Exp)
end

structure Prog where
  decls : List Dec


instance : OfNat Exp n where
  ofNat := .scon (.int n)

instance : Coe Nat Exp where
  coe n := .scon (.int n)

def SCon.toString : SCon → String
  | .int n => s!"{n}"
  | .bool b => s!"{b}"
  | .str s => s!"\"{s}\""
instance : ToString SCon := ⟨SCon.toString⟩
instance : Repr SCon := ⟨(fun scon _ => scon.toString)⟩

partial def Typ.toString : Typ → String
  | .int        => "int"
  | .bool       => "bool"
  | .string     => "string"
  | .exn        => "exn"
  | .prod ts    => s!"({", ".intercalate (ts.map toString)})"
  | .arr fn arg => s!"{toString fn} -> {toString arg}"
  | .tyvar id   => s!"'{id}"
  | .tycon name args => s!"({", ".intercalate (args.map toString)}) {name}"
instance : ToString Typ := ⟨Typ.toString⟩
instance : ToString (Option Typ) where
  toString | none   => ""
           | some τ => s!": {τ}"
instance : Repr Typ := ⟨(fun τ _ => τ.toString)⟩

partial def Pat.toString : Pat → String
  | .wild      => "_"
  | .bind name => name
  | .scon sc   => SCon.toString sc
  | .tuple ps  => s!"({", ".intercalate (ps.map toString)})"
  | .typed p τ => s!"{toString p} : {τ}"
  | .layer name .none p     => s!"{name} as {toString p}"
  | .layer name (.some τ) p => s!"({name} : {τ}) as {toString p}"
instance : ToString Pat := ⟨Pat.toString⟩
instance : ToString (List Pat) :=
  ⟨fun ps => s!"({", ".intercalate (ps.map toString)})"⟩
instance : Repr Pat := ⟨(fun p _ => p.toString)⟩

mutual
partial def Exp.toString : Exp → String
  | .scon sc    => s!"({sc})"
  | .var name   => name
  | .tuple es   => s!"({", ".intercalate (es.map Exp.toString)})"
  | .raise e    => s!"raise {e.toString}"
  | .let_in d e => s!"let {d.toString} in {e.toString}"
  | .app fn arg => s!"{fn.toString} {arg.toString}"
  | .typed e τ  => s!"{e.toString} : {τ}"
  | .ite b t f  => s!"if {b.toString} then {t.toString} else {f.toString}"
  | .case e cl  =>
    let cl_str :=
      " | ".intercalate (cl.map (fun (p, e) => s!"{p} => {e.toString}"))
    s!"case {e.toString} of {cl_str}"
  | .lam p body => s!"fn {p} => {body.toString}"
  | .extern f _ => s!"fn ? => extern_{f}"

partial def Dec.toString : Dec → String
  | .val p e => s!"val {p} = {e.toString}"
  | .valrec p ep body => s!"val rec {p} = fn {ep} => {body.toString}"
  | .fun name ps ret? body =>
    s!"fun {name} {ps.val} {ret?} = {body.toString}"
end
instance : ToString Exp := ⟨Exp.toString⟩
instance : ToString Dec := ⟨Dec.toString⟩
instance : Repr Exp     := ⟨(fun e _ => e.toString)⟩
instance : Repr Dec     := ⟨(fun d _ => d.toString)⟩

def Prog.toString : Prog → String
  | ⟨decls⟩ => "\n\n".intercalate (decls.map Dec.toString)
instance : ToString Prog := ⟨Prog.toString⟩
instance : Repr Prog     := ⟨(fun p _ => p.toString)⟩
