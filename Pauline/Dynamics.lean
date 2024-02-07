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


/- TODO: consider removing some of the `isVal` requirements and making "safe"
    theorems like done for tuples
 -/
inductive StepExp : State × Exp → State × Exp → Prop
| tupleNilStep
  : StepExp (s, .tuple []) (s, .tuple [])
| tupleHdStep (he₁ : ¬isVal e) (he₂ : StepExp (s, e) (s', e'))
  : StepExp (s, .tuple (e::es)) (s', .tuple (e'::es))
| tupleTlStep (he : isVal e) (hes : StepExp (s, .tuple es) (s', .tuple es'))
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


/- These theorems are wrappers that make using tactics more safe
    (prevents getting stuck/not making progress)
   TODO: should more be moved over?
 -/
theorem StepExp.safeTupleHdStep (he₁ : ¬isVal e)
    (he₂ : StepExp (s, e) (s', e'))
    : StepExp (s, .tuple (e::es)) (s', .tuple (e'::es)) :=
  .tupleHdStep he₁ he₂

theorem StepExp.safeTupleTlStep (he : isVal e) (hes₁ : ¬isVal (.tuple es))
    (hes₂ : StepExp (s, .tuple es) (s', .tuple es'))
    : StepExp (s, .tuple (e::es)) (s', .tuple (e::es')) :=
  .tupleTlStep he hes₂


@[simp] def StepsNExp : Nat → State × Exp → State × Exp → Prop
| 0 => fun (s, e) (s'', e'') => s = s'' ∧ e = e''
| 1 => StepExp
| n+1 => fun (s, e) (s'', e'') =>
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

/- Evaluation is deterministic, i.e. there is at most one evaluation path -/
theorem StepExp.determ
    (h₁ : StepExp (s, e) (s₁, e₁))
    (h₂ : StepExp (s, e) (s₂, e₂))
    : s₁ = s₂ ∧ e₁ = e₂ := by
  cases h₁ with
  | tupleNilStep => cases h₂; exact ⟨by rfl, by rfl⟩

  | tupleHdStep he₁ he₁' =>
    cases h₂ with
    | tupleHdStep he₂ he₂' =>
      have := StepExp.determ he₁' he₂'
      simp at this
      simp [this]
    | tupleTlStep he₂ hes₂ =>
      rw [he₂] at he₁
      contradiction

  | tupleTlStep he₁ hes₁ =>
    cases h₂ with
    | tupleHdStep he₂ he₂' =>
      rw [he₁] at he₂
      contradiction
    | tupleTlStep he₂ hes₂ =>
      have := StepExp.determ hes₁ hes₂
      simp at this
      simp [this]

  | typedStep => cases h₂; exact ⟨by rfl, by rfl⟩

  | varStep h₁' =>
    cases h₂ with
    | varStep h₂' =>
      simp only [h₂', Option.some.injEq] at h₁'
      simp only [h₁', and_self]

  | appStepL hf₁ hf₁' =>
    cases h₂ with
    | appStepL hf₂ hf₂' => simp [StepExp.determ hf₁' hf₂']
    | appStepR hf₂ he₂  => simp [hf₂] at hf₁
    | appStep    => simp at hf₁
    | externStep => simp at hf₁

  | appStepR hf₁ he₁ =>
    cases h₂ with
    | appStepL hf₂ hf₂' => simp [hf₂] at hf₁
    | appStepR hf₂ he₂  => simp [StepExp.determ he₁ he₂]
    | appStep    => sorry
    | externStep => sorry

  | appStep he₁ he₁' =>
    cases h₂ with
    | appStepL hf₂ hf₂' => simp at hf₂
    | appStepR hf₂ he₂ =>
      sorry
    | appStep he₂ he₂' => rw [←he₂'] at he₁'; simp [he₁']

  | raiseStep h₁' =>
    cases h₂ with
    | raiseStep h₂' => simp [StepExp.determ h₁' h₂']

  | externStep he₁ he₁' =>
    cases h₂ with
    | appStepL hf₂ hf₂' => simp only [isVal._eq_3, not_true_eq_false] at hf₂ 
    | appStepR hf₂ he₂ =>
      sorry
    | externStep he₂ he₂' => rw [←he₂'] at he₁'; simp [he₁']

  | iteStepB h₁' =>
    cases h₂ with
    | iteStepB h₂' => simp [StepExp.determ h₁' h₂']
    | iteStepT h₂' => rw [h₂'] at h₁'; cases h₁'
    | iteStepF h₂' => rw [h₂'] at h₁'; cases h₁'

  | iteStepT h₁' =>
    cases h₂ with
    | iteStepB h₂' => rw [h₁'] at h₂'; cases h₂'
    | iteStepT h₂' => exact ⟨by rfl, by rfl⟩
    | iteStepF h₂' => simp [h₁'] at h₂'

  | iteStepF h₁' =>
    cases h₂ with
    | iteStepB h₂' => rw [h₁'] at h₂'; cases h₂'
    | iteStepT h₂' => simp [h₁'] at h₂'
    | iteStepF h₂' => exact ⟨by rfl, by rfl⟩
decreasing_by sorry

/- Stepping formulation but moving backwards which can be useful for proofs -/
@[simp] def BackStepsNExp : Nat → State × Exp → State × Exp → Prop
| 0 => fun (s, e) (s'', e'') => s = s'' ∧ e = e''
| n+1 => fun (s, e) (s'', e'') =>
  ∃ e' s', StepExp (s, e) (s', e') ∧ BackStepsNExp n (s',e') (s'', e'')

theorem BackStepsNExp.iff_steps
    : BackStepsNExp n (s₁, e₁) (s₂, e₂) ↔ StepsNExp n (s₁, e₁) (s₂, e₂) := by
  induction n generalizing s₁ e₁ s₂ e₂
  case zero => simp
  case succ n' ih =>
    simp
    apply Iff.intro <;> intro h
    . let ⟨e', s', h'⟩ := h
      have := ih.mp h'.right
      sorry
    . cases n'
      case zero => exact ⟨e₂, s₂, h, rfl, rfl⟩
      case succ n'' =>
        let ⟨e', s', h'⟩ := h
        have := ih.mpr h'.left
        simp at this
        sorry

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
      exact StepExp.safeTupleHdStep e₁_not_val
      -- refine ⟨..., ?_⟩
      -- intro h; cases h <;> (first | assumption | contradiction)
    else
      intro h
      simp [is_zero]
      simp [is_zero] at ih h
      match h with
      | ⟨e', s', h₂, h₃⟩ =>
        refine ⟨.tuple (e' :: es), s', ?_⟩
        exact ⟨ih _ _ _ h₂, StepExp.tupleHdStep sorry h₃⟩

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
      exact StepExp.safeTupleTlStep e_val es₁_not_val
    else
      intro h
      simp [is_zero]
      simp [is_zero] at ih h
      match h with
      | ⟨.tuple es', s', h₂, h₃⟩ =>
        refine ⟨.tuple (e :: es'), s', ?_⟩
        exact ⟨ih _ _ _ h₂, StepExp.tupleTlStep e_val h₃⟩
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


theorem StepsNExp.from_scon (n : Nat)
    : ∀ s' e, StepsNExp n (s, .scon sc) (s', e) → s = s' ∧ e = .scon sc := by
  induction n
  case zero => intro s e h; simp at h; simp [h]
  case succ n' ih =>
    intro s e h
    if is_zero : n' = 0 then
      simp [is_zero] at *
      cases h
    else
      simp at h
      let ⟨_, _, hl, hr⟩ := h
      simp [ih _ _ hl] at hr
      cases hr

theorem StepsExp.from_scon
    : ∀ s' e, StepsExp (s, .scon sc) (s', e) → s = s' ∧ e = .scon sc := by
  intro s' e h
  cases h; next n h =>
  exact StepsNExp.from_scon n s' e h

def Valuable : State × Exp → Prop :=
  fun (s₁, e) => ∃ v s₂, isVal v ∧ StepsExp (s₁, e) (s₂, v)

theorem Valuable.value : isVal e → Valuable (s, e) := by
  intro h; simp [Valuable]; refine ⟨e, h, s, 0, by simp⟩

theorem StepsExp.toValuable
    (h : StepsExp (s, e) (s', .scon (.int ↑n)))
    : Valuable (s, e) := by
  exact ⟨.scon (.int ↑n), s', by simp, h⟩

theorem Valuable.split
    (h₁ : Valuable (s₁, e₁))
    (h₂ : StepsExp (s₁, e₁) (s₂, e₂))
    : Valuable (s₂, e₂) := by
  sorry


theorem BackStepsNExp.split_int
    (h₁ : BackStepsNExp n (s₁, e₁) (s₃, .scon (.int ↑v)))
    (h₂ : BackStepsNExp m (s₁, e₁) (s₂, e₂))
    : StepsExp (s₂, e₂) (s₃, .scon (.int ↑v)) := by
  induction m generalizing e₁ s₁ n
  case zero =>
    simp at h₂
    simp [h₂] at *
    exact ⟨n, BackStepsNExp.iff_steps.mp h₁⟩
  case succ m' ih₂ =>
    cases n
    case zero =>
      simp at h₁ h₂
      simp [h₁] at h₂
      let ⟨e₂', s₂', h₂'⟩ := h₂
      have := StepsExp.from_scon _ _ ⟨1, h₂'.left⟩
      simp [this] at *
      have := BackStepsNExp.iff_steps.mp h₂'.right
      simp [StepsExp.from_scon _ _ ⟨m', this⟩] at *
      apply ih₂ h₂'.right h₂'.right
    case succ n' =>
      simp at h₁ h₂
      let ⟨e₁', s₁', h₁'⟩ := h₁
      let ⟨e₂', s₂', h₂'⟩ := h₂
      apply ih₂ h₁'.right
      have := StepExp.determ h₁'.left h₂'.left
      simp [this]
      exact h₂'.right

theorem StepsExp.split_int
    (h₁ : StepsExp (s₁, e₁) (s₃, .scon (.int ↑v)))
    (h₂ : StepsExp (s₁, e₁) (s₂, e₂))
    : StepsExp (s₂, e₂) (s₃, .scon (.int ↑v)) :=
  let ⟨_, h₁⟩ := h₁
  let ⟨_, h₂⟩ := h₂
  BackStepsNExp.split_int
    (BackStepsNExp.iff_steps.mpr h₁)
    (BackStepsNExp.iff_steps.mpr h₂)
