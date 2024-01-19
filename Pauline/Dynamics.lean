import Std
import Pauline.Statics

open Std

namespace Pauline

def isVal : Exp → Bool
| .scon _
| .lam _ _
| .extern _ _
| .tuple []        => true
| .tuple (e :: es) => isVal e ∧ isVal (.tuple es)
| .typed _ _
| .var _
| .case _ _
| .ite _ _ _
| .app _ _
| .let_in _ _
| .raise _ => false

def Exn.bind   : Exp  := .var "Bind"
def Exn.match  : Exp  := .var "Match"
def Exn.div    : Exp  := .var "Div"

def Extern.add : Exp :=
  .extern "+" (fun | [.int x, .int y] => .scon (.int (x + y))
                   | _ => panic! "Extern TC Failure" )
def Extern.sub : Exp :=
  .extern "-" (fun | [.int x, .int y] => .scon (.int (x - y))
                   | _ => panic! "Extern TC Failure" )
def Extern.mul : Exp :=
  .extern "*" (fun | [.int x, .int y] => .scon (.int (x * y))
                   | _ => panic! "Extern TC Failure" )
def Extern.div : Exp :=
  .extern "div" (fun | [.int x, .int y] => .scon (.int (x / y))
                     | _ => panic! "Extern TC Failure" )
def Extern.eq : Exp :=
  .extern "=" (fun | [.int x, .int y] => .scon (.bool (x = y))
                   | _ => panic! "Extern TC Failure" )
def Extern.neq : Exp :=
  .extern "<>" (fun | [.int x, .int y] => .scon (.bool (x ≠ y))
                    | _ => panic! "Extern TC Failure" )
def Extern.lt : Exp :=
  .extern "<" (fun | [.int x, .int y] => .scon (.bool (x < y))
                   | _ => panic! "Extern TC Failure" )
def Extern.gt : Exp :=
  .extern ">" (fun | [.int x, .int y] => .scon (.bool (x > y))
                   | _ => panic! "Extern TC Failure" )
def Extern.le : Exp :=
  .extern "<=" (fun | [.int x, .int y] => .scon (.bool (x ≤ y))
                    | _ => panic! "Extern TC Failure" )
def Extern.ge : Exp :=
  .extern "<=" (fun | [.int x, .int y] => .scon (.bool (x ≥ y))
                    | _ => panic! "Extern TC Failure" )

structure State where
  values : HashMap Ident { e // isVal e }

instance : Inhabited State where
  default :=
    ⟨ HashMap.empty
      |>.insert "+"   ⟨Extern.add, by decide⟩
      |>.insert "-"   ⟨Extern.sub, by decide⟩
      |>.insert "*"   ⟨Extern.mul, by decide⟩
      |>.insert "div" ⟨Extern.div, by decide⟩
      |>.insert "="   ⟨Extern.eq , by decide⟩
      |>.insert "<>"  ⟨Extern.neq, by decide⟩
      |>.insert "<"   ⟨Extern.lt , by decide⟩
      |>.insert ">"   ⟨Extern.gt , by decide⟩
      |>.insert "<="  ⟨Extern.le , by decide⟩
      |>.insert ">="  ⟨Extern.ge , by decide⟩
    ⟩

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
| .extern name f => .extern name f

def substList : List Exp → List Exp
| [] => []
| e'::es => subst e' :: substList es

def substMatches : List (Pat × Exp) → List (Pat × Exp)
| [] => []
| (p,e')::ms => (if p.bindsIdent x then (p,e') else (p, subst e')) :: substMatches ms
end

partial def substPat (body : Exp) : { e // isVal e } → Pat → Exp
  | _, .wild => body
  | ⟨.typed e _, _⟩, p => substPat body ⟨e, sorry⟩ p
  | e, .typed p _ => substPat body e p
  | e, .bind name => subst e.val name body
  | ⟨.scon e_sc, _⟩, .scon p_sc =>
    if e_sc = p_sc then body else .raise Exn.bind
  | ⟨.tuple [], _⟩, .tuple [] => body
  | ⟨.tuple (e::es), _⟩, .tuple (p::ps) =>
    let res := substPat body ⟨e, sorry⟩ p
    match substPat body ⟨.tuple es, sorry⟩ (.tuple ps) with
    | .tuple res_rest => .tuple (res :: res_rest)
    | _ => .raise Exn.bind
  | _, .tuple _ => .raise Exn.bind
  | e, .layer name _ p => substPat (subst e.val name body) e p
  | _, _ => .raise Exn.bind

def callExtern (f : List SCon → Exp) : { e // isVal e } → Exp
  | ⟨.scon sc, _⟩ => f [sc]
  | ⟨.tuple [], _⟩ => f []
  | ⟨.tuple es, _⟩ => f (extractSCon es)
  | _ => panic! s!"Invalid extern call"
where extractSCon : List Exp → List SCon
  | [] => []
  | (.scon sc) :: es => sc :: extractSCon es
  | (.tuple vs) :: es => extractSCon vs ++ extractSCon es
  | _ => []

inductive StepExp : State × Exp → State × Exp → Prop
| tupleNilStep
  : StepExp (s, .tuple []) (s, .tuple [])
| tupleHdStep (he : StepExp (s, e) (s', e'))
  : StepExp (s, .tuple (e::es)) (s', .tuple (e'::es))
| tupleTlStep (he : isVal e) (hes : StepExp (s, .tuple es) (s', .tuple es'))
  : StepExp (s, .tuple (e::es)) (s', .tuple (e::es'))
-- | tupleConsStep {e es}
  -- (h_e : StepExp (s,e) (s',e')) (h_es : StepExp (s', .tuple es) (s'', .tuple es'))
  -- : StepExp (s, .tuple (e :: es)) (s'', .tuple (e' :: es'))
| typedStep
  : StepExp (s, .typed e t) (s, e)
| varStep (h : s.values.find? i = some e)
  : StepExp (s, .var i) (s, e.val)
| appStepL (hf : StepExp (s, f) (s', f'))
  : StepExp (s, .app f e) (s', .app f' e)
| appStepR (hf : isVal f) (he : StepExp (s, e) (s', e'))
  : StepExp (s, .app f e) (s', .app f e')
| appStep (he : isVal e) (he' : e' = substPat body ⟨e, he⟩ p)
  : StepExp (s, .app (.lam p body) e) (s, e')
| raiseStep (he : StepExp (s, e) (s', e'))
  : StepExp (s, .raise e) (s', .raise e')
| externStep (he : isVal e) (he' : e' = callExtern f ⟨e, he⟩)
  : StepExp (s, .app (.extern name f) e) (s, e')
| iteStepB {b b' t f : Exp} (hb : StepExp (s, b) (s', b'))
  : StepExp (s, .ite b t f) (s', .ite b' t f)
| iteStepT (hb : b = .scon (.bool true))
  : StepExp (s, .ite b t f) (s, t)
| iteStepF (hb : b = .scon (.bool false))
  : StepExp (s, .ite b t f) (s, f)

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

inductive StepRes (init : State × Exp)
  | val   : isVal init.2 → StepRes init
  | var   : Ident → StepRes init -- free variable
  | raise : Ident → StepRes init
  | step  : (s : State) → (e : Exp) → StepExp init (s, e) → StepRes init

def StepRes.toString : StepRes init → String
  | .val _ => "val"
  | .var x => s!"free-var: {x}"
  | .raise x => s!"raise {x}"
  | .step _s' e' _h => s!"stepped: {e'}"
instance : ToString (StepRes init) := ⟨StepRes.toString⟩

def step (s : State) (exp : Exp) : StepRes (s, exp) :=
  match hexp : exp with
  | .scon sc  => .val (by simp [isVal])
  | .var x    =>
    match h : s.values.find? x with
    | some e => .step s e.val (.varStep h)
    | none   => .var x
  | .tuple [] => .val (by simp [isVal])
  | .tuple (e :: es) =>
    match step s e with
    | .val he =>
      match step s (.tuple es) with
      | .val hes => .val (by simp [isVal]; exact ⟨he, hes⟩)
      | .var x => .var x
      | .raise exn => .raise exn
      | .step s' (.tuple es') hes =>
        .step s' (.tuple (e::es')) (.tupleTlStep he hes)
    | .var x => .var x
    | .raise exn => .raise exn
    | .step s' e' he => .step s' (.tuple (e'::es)) (.tupleHdStep he)
  | .raise e =>
    match step s e with
    | .var x => .var x
    | .raise exn => .raise exn
    | .step s' e' h => .step s' (.raise e') (.raiseStep h)
    | _ => .raise "INVALID"
  | .let_in _ _ => .raise "FAIL: Implement"
  | .app f e =>
    match step s f with
    | .step s' f' h => .step s' (.app f' e) (.appStepL h)
    | .raise exn    => .raise exn
    | .var x        => .var x
    | .val hf        =>
      match step s e with
      | .step s' e' he => .step s' (.app f e') (.appStepR hf he)
      | .raise exn     => .raise exn
      | .var x         => .var x
      | .val he =>
          match f with
          | .lam p body =>
            .step s (substPat body ⟨e, he⟩ p) (.appStep he rfl)
          | .extern _ exe =>
            .step s (callExtern exe ⟨e, he⟩) (.externStep he rfl)
          | _ => .raise s!"FAIL: SOMETHING WENT WRONG {Exp.app f e}"
  | .typed e τ => .step s e .typedStep
  | .ite b t f =>
    match b with
    | .scon (.bool true)  => .step s t (.iteStepT rfl)
    | .scon (.bool false) => .step s f (.iteStepF rfl)
    | _ =>
      match step s b with
      | .step s' b' h => .step s' (.ite b' t f) (.iteStepB sorry)
      | .var x => .var x
      | .raise exn => .raise exn
      | _ => .raise s!"FAIL: SOMETHING WENT WRONG ITE {b}"
  | .case e cl => .raise "FAIL: Implement"
  | .lam p body => .val (by simp [isVal])
  | .extern _ exe => .val (by simp [isVal])

inductive EvalRes (init : State × Exp)
| val : (e : {e // isVal e}) → StepsExp init (s, e.val) → EvalRes init
| var : Ident → StepsExp init (s, e) → EvalRes init
| raise : Ident → EvalRes init
deriving Inhabited

def EvalRes.toString : EvalRes init → String
  | .val e _ => s!"val {e.val}"
  | .var (e:=e) x _ => s!"free-var: {x} in {e}"
  | .raise x => s!"raise {x}"
instance : ToString (EvalRes init) := ⟨EvalRes.toString⟩

partial def eval_acc (s : State) (e : Exp) (acc : StepsExp init (s, e))
    : EvalRes init  :=
  match step s e with
  | .step s' e' h => eval_acc s' e' (trans acc h)
  | .val h => .val ⟨e, h⟩ acc
  | .var x => .var x acc
  | .raise exn => .raise exn

def eval (s : State) (e : Exp) : EvalRes (s, e) :=
  eval_acc s e (⟨0, by simp [StepsNExp]⟩)
