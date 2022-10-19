import Std
import Pauline.Statics

open Std

namespace Pauline

def isVal : Exp → Bool
| .scon _
| .lam _ _
| .tuple [] => true
| .tuple (e :: es) => isVal e ∧ isVal (.tuple es)
| .typed _ _
| .case _ _
| .ite _ _ _
| .app _ _
| .let_in _ _
| .var _
| .raise _ => false

structure State where
  values : HashMap Ident { e // isVal e }

def Pat.bindsIdent (i : Ident) : Pat → Bool
| wild            => false
| bind i'         => i = i'
| scon _          => false
| tuple []        => false
| tuple (x::xs)   => x.bindsIdent i || (tuple xs).bindsIdent i
| typed p _       => p.bindsIdent i
| layer name _ p  => i = name || p.bindsIdent i

mutual
variable (e : Exp) (x : Ident)
def subst : Exp → Exp
| .scon x     => .scon x
| .lam p body => if p.bindsIdent x then .lam p body else .lam p (subst body)
| .tuple es => .tuple <| substList es
| .typed e' t => .typed (subst e') t
| .case e' ms => .case (subst e') (substMatches ms)
| .ite i t e' => .ite (subst i) (subst t) (subst e')
| .app f e' => .app (subst f) (subst e')
| .let_in _ _ => panic! "unimplemented"
| .var i => if x = i then e else .var i
| .raise e' => .raise (subst e')

def substList : List Exp → List Exp
| [] => []
| e'::es => subst e' :: substList es

def substMatches : List (Pat × Exp) → List (Pat × Exp)
| [] => []
| (p,e')::ms => (if p.bindsIdent x then (p,e') else (p, subst e')) :: substMatches ms
end

inductive StepExp : State × Exp → State × Exp → Prop
| tupleNilStep
  : StepExp (s, .tuple []) (s, .tuple [])
| tupleConsStep {e es}
  (h_e : StepExp (s,e) (s',e')) (h_es : StepExp (s', .tuple es) (s'', .tuple es'))
  : StepExp (s, .tuple (e :: es)) (s'', .tuple (e' :: es'))
| typedStep
  : StepExp (s, .typed e t) (s, e)
| varStep (h : s.values.find? i = some e)
  : StepExp (s, .var i) (s, e)
| appStepL (hf : StepExp (s, f) (s', f'))
  : StepExp (s, .app f e) (s', .app f' e)
| appStepR (hf : isVal f) (he : StepExp (s, e) (s', e'))
  : StepExp (s, .app f e) (s', .app f e')
| appStep (he : isVal e) (he' : e' = sorry)
  : StepExp (s, .app (.lam p body) e) (s, e')

def StepsNExp : Nat → State × Exp → State × Exp → Prop
| 0 => λ (s, e) (s'', e'') => s = s'' ∧ e = e''
| 1 => StepExp
| n+1 => λ (s, e) (s'', e'') =>
  ∃ e' s', StepsNExp n (s,e) (s', e') ∧ StepExp (s', e') (s'', e'')

def StepsExp : State × Exp → State × Exp → Prop := (∃ n, StepsNExp n · ·)

theorem StepsExp.trans (h1 : StepsExp x y) (h2 : StepsExp y z)
  : StepsExp x z
  := by
  match x, y, z with
  | (s,e), (s',e'), (s'',e'') =>
  match h1, h2 with
  | ⟨n1,h1'⟩, ⟨n2,h2'⟩ =>
  clear h1 h2
  refine ⟨n1+n2, ?_⟩
  match n2 with
  | 0 => 
    simp [StepsNExp] at h2' ⊢
    match h2' with
    | ⟨rfl, rfl⟩ =>
    assumption
  | n2+1 =>
  induction n2 generalizing s'' e'' with
  | zero =>
    simp [StepsNExp] at h2' ⊢
    cases n1 <;> simp [StepsNExp]
    cases h1'
    subst_vars; assumption
    exact ⟨e',s',h1',h2'⟩
  | succ n2 ih =>
    match h2' with
    | ⟨e_, s_, h2, h3⟩ =>
    refine ⟨e_, s_, ?_, h3⟩
    clear h3
    apply ih
    assumption

instance : Trans StepExp StepExp StepsExp where
  trans h1 h2 := StepsExp.trans ⟨1,h1⟩ ⟨1,h2⟩

instance : Trans StepExp StepsExp StepsExp where
  trans h1 h2 := StepsExp.trans ⟨1,h1⟩ h2

instance : Trans StepsExp StepExp StepsExp where
  trans h1 h2 := StepsExp.trans h1 ⟨1,h2⟩

instance : Trans StepsExp StepsExp StepsExp where
  trans h1 h2 := h1.trans h2
