import Std
import Pauline.Dynamics
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Pauline.Tactic

open Lean Lean.Expr Lean.Meta

macro "sml_step_rfl" : tactic =>
  `(tactic| first | apply StepsExp.zero_step
                  | apply StepsExp.scon_eq.mpr
   )

macro "sml_step_extern" : tactic =>
  `(tactic| ( apply StepExp.externStep
              rfl
              simp
              simp (config := {decide := .true})
              norm_num
            )
   )

macro "sml_step_apply" : tactic =>
  `(tactic| ( apply StepExp.appStep
              rfl
              simp
              simp (config := {decide := .true})
              norm_num
            )
   )

macro "sml_step_one" : tactic =>
  `(tactic| ( first | exact StepExp.tupleNilStep; dbg_trace "step: unit"
                    | sml_step_apply; dbg_trace "step: apply"
                    | sml_step_extern; dbg_trace "step: extern"
                    | exact StepExp.typedStep; dbg_trace "step: typed"
                    | (apply StepExp.varStep (by constructor); simp); dbg_trace "step: var"
                    | apply StepExp.appStepL (by decide); dbg_trace "step: app left"
                    | apply StepExp.appStepR (by decide); dbg_trace "step: app right"
                    | apply StepExp.raiseStep; dbg_trace "step: raise"
                    | exact StepExp.iteStepT rfl; dbg_trace "step: ite true"
                    | exact StepExp.iteStepF rfl; dbg_trace "step: ite false"
                    | apply StepExp.iteStepB; dbg_trace "step: ite cond"
            )
   )

macro "sml_step_tuple" : tactic =>
  `(tactic| ( first | apply StepExp.safeTupleTlStep
                        (by rewrite [isVal]; decide) (by simp)
                      dbg_trace "step: tuple tl"
                    | apply StepExp.safeTupleHdStep (by rewrite [isVal]; decide)
                      dbg_trace "step: tuple hd"
              -- try sml_step_one
            )
   )

macro "sml_step_left_star" : tactic =>
  `(tactic| ( apply StepsExp.trans
              apply Exists.intro 1
              first | sml_step_one
                    | sml_step_tuple
            )
   )

macro "sml_congr" : tactic =>
  `(tactic| first | apply StepsExp.func_ext (by decide)
                  | apply StepsExp.tuple_tl (by simp) (by simp)
                  | apply StepsExp.tuple_hd (by simp)
   )

macro "sml_step" : tactic =>
  `(tactic| first | sml_step_rfl
                  | sml_congr -- shld this be here?
                  | sml_step_left_star
                  | sml_step_tuple
                  | sml_step_one
   )

macro "sml_apply_ih" t:term : tactic =>
  `(tactic| first | apply $t
                  | apply StepsExp.split_int $t (by repeat sml_step)
   )
