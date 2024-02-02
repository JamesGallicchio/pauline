import Pauline.Notation
import Pauline.Statics
import Pauline.Tactic

open Pauline Pauline.Tactic

def fact := [sml|
  fun fact (n : int) : int =
    if n = 0
    then 1
    else n * fact (n - 1)
]

def program_ctx : Context := sorry
abbrev program_state : State := -- todo automate
  let init : State := default
  init.insert "fact"
    ⟨[sml_exp| fn n => if n = 0 then 1 else n * fact (n - 1)], by decide⟩

theorem fact_tc
  : [smlprop|
      program_ctx ⊢ fact : int -> int
    ]
  := by sorry

example : [smlprop|
           program_state ⊢ if 1 = 1 then (if false then 0 else 1) else 2
      ==>* program_state ⊢ 1
    ] := by
  repeat sml_step

example : [smlprop|
           program_state ⊢ if 1 = 1 then 1 else 0
      ==>* program_state ⊢ 1
    ] := by
  repeat sml_step

set_option maxRecDepth 5000 in
example : [smlprop|
           program_state ⊢ fact 2
      ==>* program_state ⊢ 2
    ] := by
  repeat sml_step

theorem fact_nat_total
  : ∀ n : Nat, ∃ v : Nat,
    [smlprop|
      program_state ⊢ fact ↑n ==>* program_state ⊢ ↑v
    ]
  := by
  intro n
  induction n
  case zero =>
    apply Exists.intro 1
    repeat sml_step
  case succ n' ih =>
    have := ih.choose_spec
    apply Exists.intro ((n' + 1) * ih.choose)
    simp
    (calc
             (program_state, [sml_exp| fact (↑(n' + 1))])
      _ ==>* (program_state, [sml_exp| ↑(n' + 1) * fact ↑n'])
          := by sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                sml_step
                <;> sorry
      _ ==>* (program_state, [sml_exp| ↑(n' + 1) * ↑ih.choose]) := by sorry
    )
    sorry
