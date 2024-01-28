import Std
import Pauline.Dynamics

namespace Pauline.Tactic

/-
open Lean Lean.Expr Lean.Meta

elab "sml_eval'" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainTarget
    let expr_type ← Lean.Meta.inferType goal
    dbg_trace f!"goal: {goal}\n\n{expr_type}"

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- Check that the goal is not yet assigned.
  goal.checkNotAssigned `myApply
  -- Operate in the local context of the goal.
  goal.withContext do
    -- Get the goal's target type.
    let target ← goal.getType
    -- Get the type of the given expression.
    let type ← inferType e
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- If the conclusion unifies with the target:
    if ← isDefEq target conclusion then
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      goal.assign (mkAppN e args)
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"

elab "sml_step'" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    sorry
-/

macro "sml_step_rfl" : tactic =>
  `(tactic| exact ⟨0, by simp⟩)

macro "sml_step_extern" : tactic =>
  `(tactic| ( apply StepExp.externStep
              rfl
              decide
            )
   )

macro "sml_step_apply" : tactic =>
  `(tactic| ( apply StepExp.appStep
              rfl
              decide
            )
   )

macro "sml_step_one" : tactic =>
  `(tactic| ( first | exact StepExp.tupleNilStep
                    | sml_step_extern
                    | sml_step_apply
                    | exact StepExp.typedStep
                    | apply StepExp.varStep (by constructor)
                    | apply StepExp.appStepL (by decide)
                    | apply StepExp.appStepR
                    | apply StepExp.raiseStep
                    | exact StepExp.iteStepT rfl
                    | exact StepExp.iteStepF rfl
                    | apply StepExp.iteStepB
              --  (apply .tupleHdStep; sorry))
            )
   )

macro "sml_step_star" : tactic =>
  `(tactic| ( apply StepsExp.trans
              apply Exists.intro 1
              sml_step_one
            )
   )

macro "sml_step" : tactic =>
  `(tactic| first | sml_step_star
                  | sml_step_one
                  | sml_step_rfl
   )

-- todo make SML tactic specific syntax category
