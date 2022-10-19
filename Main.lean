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
  : ∀ n d : Nat, d > 0 → ∃ q r : Nat,
    r < d ∧
    n = q * d + r ∧
    [smlprop|
      program_state ⊢ div (↑n, ↑d) ==>* program_state ⊢ ↑q
    ]
  := by
  intro n d h_d
  induction n using Nat.strongInductionOn
  case ind n ih =>
  if h : n < d then
    refine ⟨0, n, h, by simp, ?_⟩
    (calc
      (program_state, [sml_exp| div (↑n, ↑d)])
        ==>* (program_state, [sml_exp| 0 ]) := by sorry
      _ ==>* (program_state, [sml_exp| ↑0 ]) := ⟨0, rfl, rfl⟩
    )
  else
    have : n - d < n := Nat.sub_lt (Nat.lt_of_lt_of_le h_d (Nat.ge_of_not_lt h)) h_d
    have ⟨q,r,hr,hn,steps⟩ := ih (n-d) this
    have : n = (1+q) * d + r := by
      rw [Nat.add_mul, Nat.add_assoc, ←hn, Nat.one_mul, Nat.add_comm, Nat.sub_add_cancel (Nat.ge_of_not_lt h)]
    refine ⟨_, _, hr, this, ?_⟩
    (calc
             (program_state, [sml_exp| div (↑n, ↑d)])
        ==>* (program_state, [sml_exp| 1 + div (↑n-↑d,↑d)]) := by sorry
      _ ==>* (program_state, [sml_exp| 1 + ↑q ])            := by sorry -- ih
      _ ==>* (program_state, [sml_exp| ↑(1+q) ])            := by sorry
    )
