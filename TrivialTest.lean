import Mathlib.Tactic.Trivial

-- Test the trivial? tactic
example : True := by
  trivial?

example : True ∧ True := by
  trivial?

example : 1 = 1 := by
  trivial?

example (h : False) : 1 = 2 := by
  trivial?

example : (fun x : Nat => x) = fun x => x := by
  trivial?
