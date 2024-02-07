import Std
import Pauline.Dynamics

open Std

/- This is poorly implemented, probably should be rewritten -/
namespace Pauline

open Dynamic

partial def eval_pat (s : State) : Pat → Exp → Option State
  | p, .var x            => do eval_pat s p (← s.find x)
  | p, .app _ _          => none
  | p, .let_in _ _       => none
  | p, .typed e _        => eval_pat s p e
  | p, .raise e          => none
  | p, .ite _ _ _        => none
  | p, .case _ _         => none
  | .wild, _             => s
  | .bind x, e           => s.insert x ⟨e, sorry⟩
  | .scon sc, .scon sc'  => if sc = sc' then s else none
  | .tuple [], .tuple [] => s
  | .tuple (p::ps), .tuple (e::es) => do
    eval_pat (← eval_pat s p e) (.tuple ps) (.tuple es)
  | .typed p _, e        => eval_pat s p e
  | .layer name _ p, e   => eval_pat (s.insert name ⟨e, sorry⟩) p e
  | _, _ => none

def eval_dec (s : State) : Dec → Option State
  | .val p e                 => eval_pat s p e
  | .valrec p expPat expBody => eval_pat s p (.lam expPat expBody)
  | .fun f pats _ body    => eval_pat s (.bind f) (.lam (.tuple pats) body)

def eval_prog (s : State) (prog : Prog) : Option State :=
  prog.decls.foldlM eval_dec s

def eval_prog! (s : State) (prog : Prog) : State :=
  match eval_prog s prog with
  | some s => s
  | none   => panic! "Error evaluating program {prog}!"

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

/- should require `e` typechecks rather than basically dynamically checking -/
def step (s : State) (exp : Exp) : StepRes (s, exp) :=
  match hexp : exp with
  | .scon sc  => .val (by simp [isVal])
  | .var x    =>
    match h : s.find x with
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
        .step s' (.tuple (e::es')) (.safeTupleTlStep he sorry hes)
    | .var x => .var x
    | .raise exn => .raise exn
    | .step s' e' he => .step s' (.tuple (e'::es)) (.safeTupleHdStep (sorry) he)
  | .raise e =>
    match step s e with
    | .var x => .var x
    | .raise exn => .raise exn
    | .step s' e' h => .step s' (.raise e') (.raiseStep h)
    | _ => .raise "INVALID"
  | .let_in _ _ => .raise "FAIL: Implement"
  | .app f e =>
    match step s f with
    | .step s' f' h => .step s' (.app f' e) (.appStepL (sorry) h)
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
| raise : Ident → StepsExp init (s, e) → EvalRes init
| nop : StepsExp init init → EvalRes init

instance : Inhabited (EvalRes init) where
  default := .nop ⟨0, by simp [StepsNExp]⟩

def EvalRes.exp : EvalRes init → Exp
  | .val e _            => e.val
  | .var (e := e) _ _   => e
  | .raise (e := e) _ _ => e
  | .nop _              => init.2

def EvalRes.state : EvalRes init → State
  | .val (s := s) _ _   => s
  | .var (s := s) _ _   => s
  | .raise (s := s) _ _ => s
  | .nop _              => init.1

def EvalRes.property : (res : EvalRes init) → StepsExp init (res.state, res.exp)
  | .val _ h   => h
  | .var _ h   => h
  | .raise _ h => h
  | .nop h     => h

def EvalRes.toString : EvalRes init → String
  | .val e _ => s!"val {e.val}"
  | .var (e:=e) x _ => s!"free-var: {x} in {e}"
  | .raise x _ => s!"raise {x}"
  | .nop _   => "nop"
instance : ToString (EvalRes init) := ⟨EvalRes.toString⟩

partial def eval_acc (s : State) (e : Exp) (acc : StepsExp init (s, e))
    : EvalRes init  :=
  match step s e with
  | .step s' e' h => eval_acc s' e' (trans acc h)
  | .val h => .val ⟨e, h⟩ acc
  | .var x => .var x acc
  | .raise exn => .raise exn acc

def eval (s : State) (e : Exp) : EvalRes (s, e) :=
  eval_acc s e (⟨0, by simp [StepsNExp]⟩)
