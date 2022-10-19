import Pauline.Notation
import Pauline.Statics

open Pauline

def program := [sml|

  val loop = fn L => loop L

  fun div (n : int, d : int) : int =
    if n < d
    then 0
    else 1 + div (n-d, d)

]

def program_ctx : Context := sorry
def program_state : State := sorry

theorem div_tc
  : [smlprop|
      program_ctx ⊢ div : int * int -> int
    ]
  := by
  sorry

theorem div_thm
  : ∀ n d : Nat, ∃ q r : Nat,
    r < d ∧
    n = q * d + r ∧
    [smlprop|
      program_state ⊢ div (↑n, ↑d) ==>* program_state ⊢ ↑q
    ]
  := by
  intro n d
  induction n using Nat.strongInductionOn
  case ind n ih =>
  cases h : decide (n < d)
  case true =>
    clear ih
    refine ⟨0, n, (decide_eq_true_iff _).mp h, by simp, ?_⟩
    (calc
      (program_state, [sml_exp| div (↑n, ↑d)])
        ==>* (program_state, [sml_exp| 0 ]) := by sorry
      _ ==>* (program_state, [sml_exp| ↑0 ]) := ⟨0, rfl, rfl⟩
    )
  case false =>
    have : n - d < n := sorry
    have ⟨q,r,hr,hn,steps⟩ := ih (n-d) this
    have : n = (1+q) * d + r := sorry
    refine ⟨_, _, hr, this, ?_⟩
    (calc
             (program_state, [sml_exp| div (↑n, ↑d)])
        ==>* (program_state, [sml_exp| 1 + div (↑n-↑d,↑d)]) := by sorry
      _ ==>* (program_state, [sml_exp| 1 + ↑q ])            := by sorry -- ih
      _ ==>* (program_state, [sml_exp| ↑(1+q) ])            := by sorry
    )
