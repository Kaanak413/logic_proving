import Mathlib.Topology.Basic
import Mathlib.Tactic
import Init
variable (P Q R: Prop)

example : P->Q->P := by
  intro carrot
  intro hQ
  exact carrot


lemma modus_ponens : P->(P->Q)->Q := by
  intro hP
  intro hPQ
  apply hPQ
  exact hP


lemma e1 : (P->Q->R) -> (P->Q) -> (P->R) := by
  intros hPQR hPQ hP
  apply hPQR
  exact hP
  apply hPQ
  exact hP

example : (true -> false) -> false := by
  intros h
  apply h
  trivial


-- example : false->P := by
--   intro hP
--   exfalso
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
