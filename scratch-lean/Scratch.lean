import Mathlib

inductive Evidence : Prop where
  | left (n : Nat)
  | right (n : Nat)

noncomputable def Evidence.value (h : Evidence) : Nat :=
  match h with
  | .left n => n
  | .right n => n + 1

#check Evidence.value
