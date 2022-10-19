import Std

import Pauline.Syntax

open Std

namespace Pauline

structure Env where
  varEnv  : AssocList Ident Typ

def Env.insertVal (i : Ident) (ty : Typ) : Env → Env
| ⟨varEnv⟩ => varEnv.erase i |>.cons i ty |> (⟨·⟩)

structure Context where
  tyNames : List Ident
  tyVars  : List Ident
  env : Env

def Context.empty : Context := {
  tyNames := []
  tyVars := []
  env := ⟨.nil⟩
}

def Context.updateEnv (f : Env → Env) : Context → Context
| ⟨tyNames, tyVars, env⟩ => { tyNames, tyVars, env := f env }

def typEq (_ : Context) : Typ → Typ → Bool := BEq.beq

def typeSCon : SCon → Typ
| .int _ => .int
| .str _ => .string


mutual
inductive PatHasType : Context → Pat → Typ → Env → Prop
| wildTy
  : PatHasType C .wild τ C.env
| bindTy {name}
  : PatHasType C (.bind name) τ (C.env.insertVal name τ)
| sconTy {sc}
  : PatHasType C (.scon sc) (typeSCon sc) C.env
| tupleTy {ps} (hs : ListPatHasType C ps τs E)
  : PatHasType C (.tuple ps) (.prod τs) E
| typedTy {p τ} (h : PatHasType C p τ E)
  : PatHasType C (.typed p τ) τ E
| layerSomeTy
  (h : PatHasType (C.updateEnv (·.insertVal name τ)) p τ E)
  : PatHasType C (.layer name (some τ) p) τ E
| layerNoneTy
  (h : PatHasType (C.updateEnv (·.insertVal name τ)) p τ E)
  : PatHasType C (.layer name none p) τ E

inductive ListPatHasType : Context → List Pat → List Typ → Env → Prop
| nil : ListPatHasType C [] [] C.env
| cons {p τ ps τs}
  (h_head : PatHasType C p τ E)
  (h_tail : ListPatHasType {C with env := E} ps τs E')
  : ListPatHasType C (p :: ps) (τ :: τs) E'


inductive HasType : Context → Exp → Typ → Prop
| sconTy {sc}
  : HasType C (.scon sc) (typeSCon sc)
| varTy {name τ} (h : C.env.varEnv.find? name = some τ)
  : HasType C (.var name) τ
| tupleTy {es τs} (h : ListHasTypes C es τs)
  : HasType C (.tuple es) (.prod τs)
| raiseTy {e} (h_exn : HasType C e .exn)
  : HasType C (.raise e) τ
| letInTy {d e C'} (h_d : DecHasType C d C') (h_e : HasType C' e τ)
  : HasType C (.let_in d e) τ
| lambdaTy
  (pTy : PatHasType C p τ E)
  (bodyTy : HasType {C with env := E} body τ')
  : HasType C (.lam p body) (.arr τ τ')

inductive ListHasTypes : Context → List Exp → List Typ → Prop
| nil : ListHasTypes C [] []
| cons {e τ es τs} (h_head : HasType C e τ) (h_tail : ListHasTypes C es τs)
  : ListHasTypes C (e :: es) (τ :: τs)

inductive DecHasType : Context → Dec → Context → Prop
| valTy
  (pTy : PatHasType C p τ E)
  (eTy : HasType C e τ)
  : DecHasType C (.val p e) {C with env := E}
| valrecTy
  (pTy : PatHasType C p (.arr τ τ') E)
  (p'Ty : PatHasType C p τ E')
  (eTy : HasType {C with env := E'} e τ')
  : DecHasType C (.valrec p p' e) {C with env := E}
| funTy
  : DecHasType C (
      .valrec (.bind name) p
        (List.foldr (.lam · ·) e ps)
    ) C'
  → DecHasType C (.«fun» name (.ofList (p::ps)) ret e) C'
end

inductive ProgHasType : Context → Prog → Context → Prop
| nil : ProgHasType C ⟨[]⟩ C
| cons : DecHasType C D C' → ProgHasType C' ⟨DS⟩ C'' → ProgHasType C ⟨D::DS⟩ C''
