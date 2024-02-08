import Pauline

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


/- Another example, based on some code that ME used in lecture : ) -/
def square := [sml|
  fun square (n : int) : int = n * n
]

abbrev env' : State := -- todo automate
  let init : State := default
  init.insert "square" ⟨[sml_exp| fn n => n * n], by decide⟩

-- https://www.cs.cmu.edu/~15150/resources/lectures/02/lecture02.html
example : [smlprop|
           env' ⊢ square (3 + 4)
      ==>* env' ⊢ 49
    ] := by
  repeat sml_step

theorem square_ensures :
    ∀ n : Nat,
      [smlprop|
        env' ⊢ square ↑n ==>* env' ⊢ ↑(n * n)
      ] := by
  intro n
  repeat sml_step


def power := [sml|
  fun power (n : int, k : int) : int =
    if k = 0
    then 1
    else n * power(n, k - 1)
]

abbrev env'' : State := -- todo automate
  let init : State := default
  init.insert "power"
    ⟨ [sml_exp| fn (n, k) => if k = 0 then 1 else n * power (n, k - 1)]
    , by decide
    ⟩

theorem power_correct
    : ∀ n k : Nat, [smlprop|
        env'' ⊢ power (↑n, ↑k) ==>* env'' ⊢ ↑(n.pow k)
      ] := by
  intro n k
  induction k with
  | zero => repeat sml_step
  | succ k' ih =>
    (calc
             (env'', [sml_exp| power (↑n, ↑(k' + 1))])
      _ ==>* (env'', [sml_exp| ↑n * power (↑n, ↑(k' + 1) - 1)])
          := by repeat sml_step                       -- stepping (else clause)
      _ ==>* (env'', [sml_exp| ↑n * (fn (n, k) => if k = 0 then 1 else n * power (n, k - 1)) (↑n, ↑k')])
          := by repeat sml_step                       -- eval + arithmetic math
      _ ==>* (env'', [sml_exp| ↑n * ↑(n.pow k')])
          := by (repeat sml_congr); sml_apply_ih ih   -- applying the IH
      _ ==>* (env'', [sml_exp| ↑(n * n.pow k')])
          := by repeat sml_step                       -- stepping
    )
    sml_step_rfl        -- gets out of the SML to prove the math part
    simp [Nat.pow]
    linarith
