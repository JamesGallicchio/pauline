import Pauline.Notation
import Pauline.Statics

open Pauline

def fact := [sml|

  fun fact (n : int) : int =
    if n = 0
    then 1
    else n * fact (n - 1)

]

def program_ctx : Context := sorry
def program_state : State :=
  let init : State := default
  ⟨ Std.HashMap.insert init.values "fact" -- todo automate
      ⟨[sml_exp| fn n => if n = 0 then 1 else n * fact (n - 1)], by decide⟩
  ⟩
#eval eval program_state [sml_exp| fact 12]

theorem fact_tc
  : [smlprop|
      program_ctx ⊢ fact : int -> int
    ]
  := by
  sorry

elab "sml_eval" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainTarget
    let expr_type ← Lean.Meta.inferType goal
    dbg_trace f!"goal: {goal}"


theorem fact_requires_total
  : ∀ n : Nat, n ≥ 0 → ∃ v : Nat,
    [smlprop|
      program_state ⊢ fact ↑n ==>* program_state ⊢ ↑v
    ]
  := by
  intro n requires
  induction n
  case zero =>
    refine ⟨0, ?_⟩
    sml_eval
    (calc
      (program_state, [sml_exp| fact ↑0])
      ==>* (program_state, [sml_exp| 0]) := by sorry
    )
  case succ n' ih =>
    simp at *
    have v' := ih.choose
    refine ⟨n' * v', ?_⟩
    (calc
             (program_state, [sml_exp| fact (↑(n' + 1))])
        ==>* (program_state, [sml_exp| ↑n' * fact (↑n' - 1)]) := by sorry
      _ ==>* (program_state, [sml_exp| ↑n' * ↑v'])            := by sorry -- ih
      _ ==>* (program_state, [sml_exp| ↑(n' * v')])          := by sorry
    )
