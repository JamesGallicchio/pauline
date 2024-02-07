import Pauline.Notation
import Pauline.Statics
import Pauline.Interp
import Pauline.Tactic

open Pauline Pauline.Tactic

def fact := [sml|
  fun fact (n : int) : int =
    if n = 0
    then 1
    else n * fact (n - 1)
]

def program_ctx : Context := sorry
abbrev env : State := -- todo automate
  let init : State := default
  init.insert "fact"
    ⟨[sml_exp| fn n => if n = 0 then 1 else n * fact (n - 1)], by decide⟩

theorem fact_tc
  : [smlprop|
      program_ctx ⊢ fact : int -> int
    ]
  := by sorry


example : [smlprop|
           env ⊢ if 1 = 1 then (if false then 0 else 1) else 2
      ==>* env ⊢ 1
    ] := by
  repeat sml_step


example : [smlprop|
           env ⊢ if 1 = 1 then 1 else 0
      ==>* env ⊢ 1
    ] := by
  repeat sml_step


set_option maxRecDepth 5000 in
example : [smlprop|
           env ⊢ fact 2
      ==>* env ⊢ 2
    ] := by
  repeat sml_step

/- yes we can simplify this but this is readable for non-lean people imo -/
theorem fact_nat_total
  : ∀ n : Nat, ∃ v : Nat,
    [smlprop|
      env ⊢ fact ↑n ==>* env ⊢ ↑v
    ] := by
  intro n
  induction n with
  | zero =>
    apply Exists.intro 1
    repeat sml_step
  | succ n' ih =>
    let ⟨v', ih⟩ := ih
    apply Exists.intro ((n' + 1) * v')
    (calc
             (env, [sml_exp| fact (↑(n' + 1))])
      _ ==>* (env, [sml_exp| ↑(n' + 1) * (fn n => if n = 0 then 1 else n * fact (n - 1)) ↑n'])
          := by repeat sml_step
      _ ==>* (env, [sml_exp| ↑(n' + 1) * ↑v'])
          := by (repeat sml_congr); sml_apply_ih ih
      _ ==>* (env, [sml_exp| ↑((n' + 1) * v')])
          := by repeat sml_step
    )
