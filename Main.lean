import Pauline.Notation
import Pauline.Statics
import Pauline.Tactic
import Mathlib.Tactic
import Mathlib.Data.String.Lemmas

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
  := by
  sorry

-- #eval step program_state [sml_exp| if 0 = 0 then 1 else n * fact (n - 1)]

abbrev test := [sml_exp| if true then (if false then 0 else 1) else 2]

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

example : [smlprop|
           program_state ⊢ fact 1
      ==>* program_state ⊢ 1
    ] := by
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
  simp
  sorry


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
    let v_ih := ih.choose
    have := ih.choose_spec
    apply Exists.intro ((n' + 1) * v_ih)
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
                sorry
                -- sml_step_rfl
      -- _ ==>* (program_state, [sml_exp| (↑n' + 1) * ↑ih.choose])  := by sorry
      -- _ ==>* (program_state, [sml_exp| ↑((n' + 1) * ih.choose)]) := by sorry
    )
    sorry
