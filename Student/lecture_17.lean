#check Empty
--inductive Empty : Type

inductive Chaos: Type
def from_empty (e: Empty) : Chaos := nomatch e

#check False
-- inductive False: Prop

def from_false {P : Prop} (p: False): P := False.elim p

def from_false_is_false (p: False) : True = False := False.elim p

-- no introduction rule

/-!
Unit ==> True
-/



#check Unit
-- inductive PUnit : Sort u where
-- | unit : PUnit


#check True
-- inductive True : Prop where
-- | intro : True

#check True.intro

-- no elimination rule

def proof_of_true : True := True.intro

def false_implies_true : False → True := λ f => False.elim f

/-
Prod ==> And

-/

#check Prod

/-
structure Prod (α : Type u) (β : Type v) where
fst : α
snd : β

-/

#check And

/-
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
-/

inductive Bird_chirping : Prop
| yep
| boo


inductive Sky_blue : Prop
|yep

#check(And Bird_chirping Sky_blue)


theorem both_and : And Bird_chirping Sky_blue := And.intro Bird_chirping.boo Sky_blue.yep

/-
Proof Irrelevence
-/

namespace cs2120f23

inductive Bool : Type
| true
| false


theorem proof_equal : Bird_chirping.boo = Bird_chirping.yep := by trivial

-- In Prop all proofs are equivalent
-- Choice of values in Prop can't influence computations

/-
Sum ==> Or
-/

#check Sum

/-
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
-/

#check Or

/-
inductive Or (a b : Prop) where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

theorem one_or_other : Or Bird_chirping Sky_blue := Or.inl Bird_chirping.yep
theorem one_or_other' : Or Bird_chirping Sky_blue := Or.inr Sky_blue.yep

example : Or Bird_chirping (0=1) := Or.inl Bird_chirping.yep
example : (0=1) ∨ (1=2) := _


theorem or_comm {P Q : Prop} : P ∨  Q → Q ∨  P :=
λ d =>
  match d with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q


  /-
  Not (no)
  -/

  def no (α : Type) := α → Empty

  #check Not
  --Not p is defined to be P → False

example : no Chaos := λ (c : Chaos) => nomatch c

inductive Raining : Prop

example : ¬Raining := λ (r : Raining) => nomatch r
