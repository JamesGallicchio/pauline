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
           program_state ⊢ fact 0
      ==>* program_state ⊢ 1
    ] := by
  sml_step
  sml_step
  sml_step
  simp
  -- sml_eval'
  sorry

theorem fact_requires_total
  : ∀ n : Nat, n ≥ 0 → ∃ v : Nat,
    [smlprop|
      program_state ⊢ fact ↑n ==>* program_state ⊢ ↑v
    ]
  := by
  intro n requires
  induction n
  case zero =>
    refine ⟨1, ?_⟩
    let fact0 := [sml_exp| fact ↑0]
    let res := eval program_state fact0
    -- sml_eval
    (calc
             (program_state, [sml_exp| fact ↑0])
        ==>* (program_state, [sml_exp| if ↑0 = 0 then 1 else n * fact (n - 1)])
          := by sorry
      _ ==>* (program_state, [sml_exp| if true then 1 else n * fact (n - 1)])
          := by sorry
      _ ==>* (program_state, [sml_exp| 1])
          := by refine ⟨1, ?_⟩
                exact .iteStepT rfl
      _ ==>* (program_state, [sml_exp| 1])
          := by try (refine ⟨0, ?_⟩; simp)
    )
  case succ n' ih =>
    simp at ih
    let v' := ih.choose
    have := ih.choose_spec
    refine ⟨n' * ih.choose, ?_⟩
    (calc
             (program_state, [sml_exp| fact (↑(n' + 1))])
        ==>* (program_state, [sml_exp| ↑n' * fact ↑n']) := by sorry
      _ ==>* (program_state, [sml_exp| ↑n' * ↑v'])
          := by apply StepsExp.trans
                case y => exact (program_state, ih.choose)
                apply Exists.intro 1
                simp
                sorry
                -- exact .tupleTlStep sorry sorry
                -- sorry
                -- exact ih.choose_spec
                sorry
      _ ==>* (program_state, [sml_exp| ↑(n' * v')])          := by sorry
    )
