import Std
import Pauline.Statics

open Std

namespace Pauline

@[simp, reducible] def isVal : Exp → Bool
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

/- Maybe move these `Exn`/`Extern` into the Syntax file? -/
def Exn.bind   : Exp  := .var "Bind"
def Exn.match  : Exp  := .var "Match"
def Exn.div    : Exp  := .var "Div"

abbrev Extern.add : Exp :=
  .extern "+" (fun | [.int x, .int y] => .scon (.int (x + y))
                   | _ => panic! "Extern TC Failure" )
abbrev Extern.sub : Exp :=
  .extern "-" (fun | [.int x, .int y] => .scon (.int (x - y))
                   | _ => panic! "Extern TC Failure" )
abbrev Extern.mul : Exp :=
  .extern "*" (fun | [.int x, .int y] => .scon (.int (x * y))
                   | _ => panic! "Extern TC Failure" )
abbrev Extern.div : Exp :=
  .extern "div" (fun | [.int x, .int y] => .scon (.int (x / y))
                     | _ => panic! "Extern TC Failure" )
abbrev Extern.eq : Exp :=
  .extern "=" (fun | [.int x, .int y] => .scon (.bool (x = y))
                   | _ => panic! "Extern TC Failure" )
abbrev Extern.neq : Exp :=
  .extern "<>" (fun | [.int x, .int y] => .scon (.bool (x ≠ y))
                    | _ => panic! "Extern TC Failure" )
abbrev Extern.lt : Exp :=
  .extern "<" (fun | [.int x, .int y] => .scon (.bool (x < y))
                   | _ => panic! "Extern TC Failure" )
abbrev Extern.gt : Exp :=
  .extern ">" (fun | [.int x, .int y] => .scon (.bool (x > y))
                   | _ => panic! "Extern TC Failure" )
abbrev Extern.le : Exp :=
  .extern "<=" (fun | [.int x, .int y] => .scon (.bool (x ≤ y))
                    | _ => panic! "Extern TC Failure" )
abbrev Extern.ge : Exp :=
  .extern "<=" (fun | [.int x, .int y] => .scon (.bool (x ≥ y))
                    | _ => panic! "Extern TC Failure" )

def HashMap.beq [Hashable α] [BEq α] [BEq β] (m₁ m₂ : HashMap α β) : Bool :=
  m₁.toList == m₂.toList
instance [Hashable α] [BEq α] [BEq β] : BEq (HashMap α β) := ⟨HashMap.beq⟩

structure State where -- not correct for closures (doesn't include env) : )
  idents  : List Ident
  find : Ident → Option { e // isVal e }
  valid_map : ∀ x ∈ idents, ∃ e, find x = some e

def State.empty : State :=
  ⟨[], fun _ => none, by simp⟩

def State.insert (s : State) (x : Ident) (e : { e // isVal e }) : State :=
  ⟨ x :: s.idents
  , fun x' => if x = x' then some e else s.find x'
  , sorry
  ⟩

instance : BEq { e // isVal e } := ⟨(·.val == ·.val)⟩
-- instance : BEq State where
  -- beq s₁ s₂ := HashMap.beq s₁.values s₂.values

instance : Inhabited {e // isVal e} := ⟨⟨.tuple [], by decide⟩⟩
instance : Inhabited State where
  default :=
    State.empty
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

abbrev State.NonAdversarial (s : State) : Prop :=
    (s.find "+"   = some ⟨Extern.add, by decide⟩)
  ∧ (s.find "-"   = some ⟨Extern.sub, by decide⟩)
  ∧ (s.find "*"   = some ⟨Extern.mul, by decide⟩)
  ∧ (s.find "div" = some ⟨Extern.div, by decide⟩)
  ∧ (s.find "="   = some ⟨Extern.eq , by decide⟩)
  ∧ (s.find "<>"  = some ⟨Extern.neq, by decide⟩)
  ∧ (s.find "<"   = some ⟨Extern.lt , by decide⟩)
  ∧ (s.find ">"   = some ⟨Extern.gt , by decide⟩)
  ∧ (s.find "<="  = some ⟨Extern.le , by decide⟩)
  ∧ (s.find ">="  = some ⟨Extern.ge , by decide⟩)

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
@[simp, reducible]
def subst : Exp → Exp
| .scon x     => .scon x
| .lam p body => if p.bindsIdent x then .lam p body else .lam p (subst body)
| .tuple es => .tuple <| substList es
| .typed e' t => .typed (subst e') t
| .case e' ms => .case (subst e') (substMatches ms)
| .ite i t e' => .ite (subst i) (subst t) (subst e')
| .app f e' => .app (subst f) (subst e')
| .let_in _ _ => panic! "unimplemented"
| .extern name f => .extern name f
| .var i => if x = i then e else .var i
| .raise e' => .raise (subst e')

@[simp, reducible]
def substList : List Exp → List Exp
| [] => []
| e'::es => subst e' :: substList es

@[simp, reducible]
def substMatches : List (Pat × Exp) → List (Pat × Exp)
| [] => []
| (p,e')::ms => (if p.bindsIdent x then (p,e') else (p, subst e')) :: substMatches ms
end

@[simp] def substPat (body : Exp) (e :  { e // isVal e }) (p : Pat) : Exp :=
  match p with
  | .wild           => body
  | .bind name      => subst e.val name body
  | .layer name _ p => substPat (subst e.val name body) e p
  | .scon p_sc      => if let .scon e_sc := e.val then body else .raise Exn.bind
  | .typed p _      => substPat body e p
  | .tuple []       => if let .tuple [] := e.val then body else .raise Exn.bind
  | .tuple (p::[])  =>
    if let .tuple (e::[]) := e.val
    then substPat body ⟨e, sorry⟩ p
    else .raise Exn.bind
  | .tuple (p::ps)  =>
    if let .tuple (e::es) := e.val then
      let res := substPat body ⟨e, sorry⟩ p
      match substPat body ⟨.tuple es, sorry⟩ (.tuple ps) with
      | .tuple res_rest => .tuple (res :: res_rest)
      | _ => .raise Exn.bind
    else .raise Exn.bind


@[simp] private def callExtern.extractSCon : List Exp → List SCon
  | [] => []
  | (.scon sc) :: es => sc :: extractSCon es
  | (.tuple vs) :: es => extractSCon vs ++ extractSCon es
  | _ :: _ => []

@[simp] def callExtern (f : List SCon → Exp) : { e // isVal e } → Exp
  | ⟨.scon sc, _⟩ => f [sc]
  | ⟨.tuple [], _⟩ => f []
  | ⟨.tuple es, _⟩ => f (callExtern.extractSCon es)
  | _ => .raise Exn.bind

/- Added some duplicate rules, some require that something is not a value. This
    is useful for writing the tactics bc without that we might step the same
    thing forever.

  TODO: consider another way of implementing this? maybe we should just have
    the normal rules and then special theorems that have the additional
    restrictions and the tactics should only work with those theorems? similar
    to how the tactics just don't try and apply `tupleNilStep`
 -/
inductive StepExp : State × Exp → State × Exp → Prop
| tupleNilStep
  : StepExp (s, .tuple []) (s, .tuple [])
| tupleHdStep (he₁ : ¬isVal e) (he₂ : StepExp (s, e) (s', e'))
  : StepExp (s, .tuple (e::es)) (s', .tuple (e'::es))
| tupleHdStep' (he₂ : StepExp (s, e) (s', e')) -- weaker version
  : StepExp (s, .tuple (e::es)) (s', .tuple (e'::es))
| tupleTlStep (he : isVal e) (hes₁ : ¬isVal (.tuple es))
              (hes₂ : StepExp (s, .tuple es) (s', .tuple es'))
  : StepExp (s, .tuple (e::es)) (s', .tuple (e::es'))
| tupleTlStep' (he : isVal e) (hes₂ : StepExp (s, .tuple es) (s', .tuple es'))
  : StepExp (s, .tuple (e::es)) (s', .tuple (e::es'))
| typedStep
  : StepExp (s, .typed e t) (s, e)
| varStep (h : s.find i = some e)
  : StepExp (s, .var i) (s, e.val)
| appStepL (hf : ¬isVal f) (hf : StepExp (s, f) (s', f'))
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

@[simp] def StepsNExp : Nat → State × Exp → State × Exp → Prop
| 0 => λ (s, e) (s'', e'') => s = s'' ∧ e = e''
| 1 => StepExp
| n+1 => λ (s, e) (s'', e'') =>
  ∃ e' s', StepsNExp n (s,e) (s', e') ∧ StepExp (s', e') (s'', e'')

def StepsExp : State × Exp → State × Exp → Prop := (∃ n, StepsNExp n · ·)

theorem StepsExp.zero_step : ∀ e s, StepsExp (s, e) (s, e) := by
  intro e s; apply Exists.intro 0; simp

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

/- TODO: these should be iff -/
theorem StepsNExp.func_ext {f : Exp} (f_val : isVal f) (n : Nat)
    : ∀ e₁ e₂ s₁ s₂,
        StepsNExp n (s₁, e₁) (s₂, e₂)
      → StepsNExp n (s₁, Exp.app f e₁) (s₂, Exp.app f e₂) := by
  induction n
  case zero => simp
  case succ n ih =>
    intro e₁ e₂ s₁ s₂ h
    if is_zero : n = 0 then
      -- apply Iff.intro <;> intro h
      simp [is_zero] at *
      exact StepExp.appStepR f_val h
      -- . cases h
        -- case appStepL => contradiction
        -- case appStepR => assumption
        -- case appStep => sorry
        -- case externStep => sorry
    else
      simp [is_zero] at *
      match h with
      | ⟨e', s', h₂, h₃⟩ =>
        refine ⟨Exp.app f e', s', ?_⟩
        exact ⟨ih _ _ _ _ h₂, StepExp.appStepR f_val h₃⟩

-- TODO: likewise should probs be iff
theorem StepsExp.func_ext {f : Exp} (f_val : isVal f)
    : ∀ e₁ e₂ s₁ s₂,
        StepsExp (s₁, e₁) (s₂, e₂)
      → StepsExp (s₁, Exp.app f e₁) (s₂, Exp.app f e₂) := by
  intro e₁ e₂ s₁ s₂ h
  cases h; next n h =>
  exact ⟨n, StepsNExp.func_ext (f_val := f_val) n e₁ e₂ s₁ s₂ h⟩


theorem StepsNExp.tuple_hd {es : List Exp} (n : Nat) (e₁ : Exp)
    (e₁_not_val : ¬isVal e₁)
    : ∀ e₂ s₁ s₂,
        StepsNExp n (s₁, e₁) (s₂, e₂)
      → StepsNExp n (s₁, .tuple (e₁ :: es)) (s₂, .tuple (e₂ :: es)) := by
  induction n
  case zero => simp
  case succ n ih =>
    intro e₂ s₁ s₂
    if is_zero : n = 0 then
      simp [is_zero]
      exact StepExp.tupleHdStep e₁_not_val
      -- refine ⟨..., ?_⟩
      -- intro h; cases h <;> (first | assumption | contradiction)
    else
      intro h
      simp [is_zero]
      simp [is_zero] at ih h
      match h with
      | ⟨e', s', h₂, h₃⟩ =>
        refine ⟨.tuple (e' :: es), s', ?_⟩
        exact ⟨ih _ _ _ h₂, StepExp.tupleHdStep' h₃⟩

theorem StepsExp.tuple_hd {es : List Exp} {e₁ : Exp} (e₁_not_val : ¬isVal e₁)
    : ∀ e₂ s₁ s₂,
        StepsExp (s₁, e₁) (s₂, e₂)
      → StepsExp (s₁, .tuple (e₁ :: es)) (s₂, .tuple (e₂ :: es)) := by
  intro e₂ s₁ s₂ h
  cases h; next n h =>
  exact ⟨n, StepsNExp.tuple_hd n e₁ e₁_not_val e₂ s₁ s₂ h⟩


theorem StepsNExp.tuple_tl (n : Nat) (e : Exp) (es₁ : List Exp)
    (e_val : isVal e) (es₁_not_val : ¬isVal (.tuple es₁))
    : ∀ es₂ s₁ s₂,
        StepsNExp n (s₁, .tuple es₁) (s₂, .tuple es₂)
      → StepsNExp n (s₁, .tuple (e :: es₁)) (s₂, .tuple (e :: es₂)) := by
  induction n
  case zero => simp
  case succ n ih =>
    intro es₂ s₁ s₂
    if is_zero : n = 0 then
      simp [is_zero]
      exact StepExp.tupleTlStep e_val es₁_not_val
    else
      intro h
      simp [is_zero]
      simp [is_zero] at ih h
      match h with
      | ⟨.tuple es', s', h₂, h₃⟩ =>
        refine ⟨.tuple (e :: es'), s', ?_⟩
        exact ⟨ih _ _ _ h₂, StepExp.tupleTlStep' e_val h₃⟩
      | ⟨_, _, _, _⟩ =>
        -- todo we need theorems to reason about tuples staying tuples
        -- just gonna sorry for now
        sorry

theorem StepsExp.tuple_tl {e : Exp} {es₁ : List Exp}
    (e_val : isVal e) (es₁_not_val : ¬isVal (.tuple es₁))
    : ∀ es₂ s₁ s₂,
        StepsExp (s₁, .tuple es₁) (s₂, .tuple es₂)
      → StepsExp (s₁, .tuple (e :: es₁)) (s₂, .tuple (e :: es₂)) := by
  intro es₂ s₁ s₂ h
  cases h; next n h =>
  exact ⟨n, StepsNExp.tuple_tl n e es₁ e_val es₁_not_val es₂ s₁ s₂ h⟩
