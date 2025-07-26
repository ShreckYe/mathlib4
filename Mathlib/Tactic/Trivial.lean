/-
Copyright (c) 2024 GitHub Copilot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GitHub Copilot
-/
import Mathlib.Init
import Lean.Meta.Tactic.TryThis

/-!
# `trivial?` tactic

The `trivial?` tactic is a suggestion tactic that will try each of the simple tactics used by
`trivial` and report which one succeeds with a "Try this:" suggestion. This allows the user to
replace `trivial?` with the actual simple tactic in their proof.

This is similar to `apply?` and `simp?` in that it helps users understand what simple tactic
can be used to solve their goal.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Tactic Lean.Meta.Tactic.TryThis

/--
`trivial?` attempts to close the goal using simple tactics.

It tries, in order:
- `assumption`
- `rfl`
- `contradiction`
- `decide`
- `apply True.intro`

When one of these succeeds, `trivial?` reports a "Try this:" suggestion with the successful tactic.

This tactic should not be left in proofs; it is a search tool, like `apply?` and `simp?`.
-/
syntax (name := trivial?) "trivial?" : tactic

elab_rules : tactic
| `(tactic| trivial?%$tk) => withMainContext do
  -- Try each simple tactic in sequence
  let tactics : Array (TSyntax `tactic) := #[
    ← `(tactic| assumption),
    ← `(tactic| rfl),
    ← `(tactic| contradiction),
    ← `(tactic| decide),
    ← `(tactic| apply True.intro)
  ]

  for tacticStx in tactics do
    let state ← saveState
    try
      evalTactic tacticStx
      -- If we reach here, the tactic succeeded
      addSuggestion tk { suggestion := tacticStx } (origSpan? := tk)
      return
    catch _ =>
      restoreState state
      continue

  -- If none of the simple tactics worked, try the And.intro case
  let state ← saveState
  try
    evalTactic (← `(tactic| apply And.intro))
    -- Check if this created goals that trivial can solve
    let goals ← getGoals
    if goals.isEmpty then
      -- And.intro closed the goal entirely
      addSuggestion tk { suggestion := ← `(tactic| apply And.intro) } (origSpan? := tk)
      return
    else
      -- We need to apply trivial to the subgoals
      evalTactic (← `(tactic| all_goals trivial))
      -- If successful, suggest the combined tactic
      addSuggestion tk { suggestion := ← `(tactic| apply And.intro <;> trivial) } (origSpan? := tk)
      return
  catch _ =>
    restoreState state
    throwError "trivial?: no applicable tactic found"

end Mathlib.Tactic
