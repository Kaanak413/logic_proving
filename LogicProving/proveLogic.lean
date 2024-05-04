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


theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp


example : P ↔ P := by
  apply Iff.refl
  -- rfl

example (y : Nat) : (fun x : Nat => 0) y = 0 := by
    rfl

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption


variable (A B C : Type)

variable (PP QQ  : A → Prop)

-- lemma two : (∀x : A , Px -> Q ) = (∃x : A , Px -> Q ) :=


-- lemma three : ((∀x : A , PPx) ∧ (∀x : A , QQx) ) -> (∀x : A , PPx ∧  QQx ) := by
--   intro hPP hA
--   cases hPP with
--   | intro h q =>
--     cases q with
--     | intro a x =>
--       exists h


  -- apply And.intro
  -- case right =>
  --   apply
example : (∀ x : A, PP x ∧ QQ x)
↔ (∀ x : A , PP x) ∧ (∀ x : A, QQ x) := by
  constructor
  intro h
  constructor
  intro a
  have pq :PP a ∧ QQ a
  apply h
  cases pq with
  | intro pa qa =>
    exact pa
  intro a
  have pq :PP a ∧ QQ a
  apply h
  cases pq with
  | intro pa qa =>
    exact qa
  intro h
  cases h with
  | intro hp qp =>
    intro a
    constructor
    apply hp
    apply qp


#check em
#check by_contradiction












theorem lemma7 : ¬ (∀ x : A, PP x) ↔ ∃ x : A, ¬ PP x := by
  constructor
  intro h
  apply by_contradiction
  intro ne
  apply h
  intro a
  apply by_contradiction
  intro np
  apply ne
  exists a
  intro h na
  cases h with
  | intro a np =>
    apply np
    apply na
