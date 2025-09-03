import Mathlib

open Fin
open Finset
open List

example (p : Fin n → ℕ) : ∏ j, insertNth i x p j = x * ∏ j, p j := by simp [prod_univ_succAbove]

example (l : List ℕ) (h : i < l.length) : (l.insertIdx i a).prod = a * l.prod := by
  induction l generalizing i with
  | nil => omega
  | cons head tail ih =>
    cases i with
    | zero => simp
    | succ j => simp [ih (by omega), mul_assoc]
