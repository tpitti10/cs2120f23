/-!
# Exam 1

DO NOT CHEAT.
-/

/-! 
## #1 Easy Functions [15 points]

Define a function, *pythag*, that takes three natural 
numbers, call them *a, b,* and *c*, and that returns
*true* if *a^2 + b^2 = c^2* and that returns *false*
otherwise.
-/

-- Define your function here

def pythag : Nat → Nat → Nat → Bool
|a, b, c => a^2 + b^2 = c^2


-- The following test cases should then pass
#eval pythag 3 4 5  -- expect true
#eval pythag 6 7 8  -- expect false

/-! 
## #2 Recursive Functions

Define a function, sum_cubes, that takes any natural
number, *n*, as an argument, and that retrns the sum
of the cubes of the natural numbers from *1* up to *n*
inclusive.
-/

-- Define your function here
def cube : Nat → Nat
|a => a*a*a

def sum_cubes : Nat → Nat
| 0 => 0
| (n+1) => cube (n+1) + sum_cubes n


-- test case: sum_cubes 4 = 1 + 8 + 27 + 64 = 100
#eval sum_cubes 4   -- expect 100


/-!
## #3 Product and Sum Types

Define two functions, called *prod_ors_to_or_prods*, 
and *or_prods_to_prod_ors* that shows that a product 
of sums be converted into a sum of products in a way
that the result can then be converted back into the
original product of sums. 

As a concrete example, you might want to show that if 
you have an apple or an orange and you have a cup or
a bowl, then you have an apple and a cup or an apple
and a bowl or an orange and a cup or an orange and a
bowl. 

Hints: 1. Be sure you understand the reasoning before
you try to define your functions. 2. Use four cases. 3. 
Use type-guided, top-down programming, assisted by the
Lean prover to work out a solution for each case.  
-/

def prod_ors_to_or_prods {α β γ δ: Type} :
  (α ⊕ β) × (γ ⊕ δ) → (α × γ) ⊕ ((α × δ) ⊕ ((β × γ) ⊕ (β × δ))) 
| ((Sum.inl a), (Sum.inl c)) => Sum.inl (a,c)
| ((Sum.inr b), (Sum.inr d)) => Sum.inr (Sum.inr (Sum.inr (b, d)))
| ((Sum.inl a), (Sum.inr d)) => Sum.inr (Sum.inl (a,d))
| ((Sum.inr b), (Sum.inl c)) => Sum.inr (Sum.inr (Sum.inl (b,c)))

-- Write the second function here from scratch

def or_prods_to_prod_ors {α β γ δ: Type} :  
 (α × γ) ⊕ ((α × δ) ⊕ ((β × γ) ⊕ (β × δ))) → (α ⊕ β) × (γ ⊕ δ)
|  Sum.inl (a,c) => ((Sum.inl a), (Sum.inl c))
|  Sum.inr (Sum.inr (Sum.inr (b, d))) => ((Sum.inr b), (Sum.inr d))
|  Sum.inr (Sum.inl (a,d)) => ((Sum.inl a), (Sum.inr d)) 
|  Sum.inr (Sum.inr (Sum.inl (b,c))) => ((Sum.inr b), (Sum.inl c))


/-!
## #4 Propositional Logic Syntax and Semantics

Extend your Homework #7 solution to implement the
propositional logic *iff/equivalence* (↔) operator.
Note that Lean does not natively define the *iff*
Boolean operator. 
-/
structure var : Type :=  (n: Nat)
inductive unary_op : Type | not
inductive binary_op : Type
| and
| or
| imp
| iff


inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)
notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true

def biimplies : Bool → Bool → Bool
| true, true => true
| false, false => true
|_, _ => false 

def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
| binary_op.iff => biimplies

def Interp := var → Bool  
def eval_expr : Expr → Interp → Bool 
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)


/-!
Using our syntax for propositional logic, and the
variable names *A, O, C,* and *B*, respectively for
the propositions *I have an apple, I have an orange,
I have a cup,* and *I have a bowl* write a proposition
that having an orange or an apple and a bowl or a cup
is equivalent to having an apple and a bowl or an
apple and a cup or an orange and a bowl or an orange
and a cup.

Note: There's no need here to use our implementation
of propositional logic. Just write the expression 
here using the notation we've defined.
-/


def A := {var.mk 3} 
def O := {var.mk 4}
def C := {var.mk 5}
def B := {var.mk 6}

def my_prop := (O ∨ A) ∧ (B ∨ C) ⇔ (A ∧ B) ∨ (A ∧ C) ∨ (O ∧ B) ∨ (O ∧ C)

/-!
## #5 Propositional Logic Validity

At the end of your updated Homework #7 file, use our 
validity checking function to check your expression for
validity, in the expectation that the checker will 
determine that the expression is in fact valid.
-/



def right_bit (n : Nat) := n%2

def shift_right (n : Nat) := n/2

def nat_to_bin : Nat → List Nat
| 0     => [0]
| 1     => [1]
| n' + 2 =>
  have : (shift_right (n' + 2)) < (n' + 2) := sorry
  nat_to_bin (shift_right (n' + 2)) ++ [right_bit (n' + 2)]

def zero_pad : Nat → List Nat → List Nat
  | v, l => zero_pad_recursive (v - (l.length)) l
where zero_pad_recursive : Nat → List Nat → List Nat
  | 0, l => l
  | v'+1, l => zero_pad_recursive v' (0::l)

def mk_bit_row : (row: Nat) → (cols : Nat) → List Nat
| r, c => zero_pad c (nat_to_bin r)

-- Convert nat to bool where 0 ↦ false, ¬0 ↦ true
def bit_to_bool : Nat → Bool
| 0 => false
| _ => true

def bit_list_to_bool_list : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

def mk_row_bools : (row : Nat) → (vars : Nat) → List Bool
| r, v => bit_list_to_bool_list (mk_bit_row r v)

def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

def v₀ := var.mk 0
def v₁ := var.mk 1
def v₂ := var.mk 2

def all_false : Interp := λ _ => false

-- interp for [false, true, false], i.e., [0, 1, 0]
def interp2 := override all_false v₁ true

-- interp for [false, true, true], i.e., [0, 1, 1]
def interp3 := override interp2 v₂ true

def bools_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => all_false
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 

-- Demonstration
def interp3' := bools_to_interp [false, true, true] 

def mk_interp_vars_row : (vars: Nat) → (row: Nat) → Interp
| v, r => bools_to_interp (mk_row_bools r v)

def interp3'' :=  mk_interp_vars_row 3 3 -- vars=3, row=3

def mk_interps (vars : Nat) : List Interp := 
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List Interp
  | 0, _         => []
  | (n' + 1), v  => (mk_interp_vars_row v n')::mk_interps_helper n' v


def interps3 := mk_interps 3

def eval_expr_interps : List Interp → Expr → List Bool
| [], _ => []
--| h::t, e => (eval_expr e h)::eval_expr_interps t e
| h::t, e => eval_expr_interps t e ++ [eval_expr e h]

def highest_variable_index : Expr → Nat
| Expr.var_exp (var.mk i) => i
| Expr.un_exp _ e => highest_variable_index e
| Expr.bin_exp _ e1 e2 => max (highest_variable_index e1) (highest_variable_index e2)

def truth_table_outputs : Expr → List Bool
| e =>  eval_expr_interps (mk_interps (highest_variable_index e + 1)) e
def list_and : List Bool → Bool
| [] => false
| (h::t) => and h (list_and t)


/-!
## HOMEWORK PART 1:

Write three functions
- sat : Expr → Bool
- unsat: Expr → Bool
- valid: Expr → Bool

Given any expression, *e*, in propositional logic, the first returns true
if *e* is sastisfiable, otherwise false. The second returns true if *e* is
unsatisfiable, otherwise false. The third returns true if *e* is valid, and
otherwise returns false. You can write helper functions if/as needed. Write
short comments to explain what each of your functions does. Write a few test
cases to demonstrate your results.
-/

-- Here
def list_or : List Bool → Bool
| [] => false
| (h::t) => or h (list_or t)

def is_sat : Expr → Bool
|e => list_or (truth_table_outputs e)

def is_unsat : Expr → Bool
|e => not (is_sat e)

def is_valid : Expr → Bool
|e => list_and (truth_table_outputs e)

#eval is_valid (my_prop)

def fact: Nat →  Nat
| 0 => 1
| (n' +1 ) => (n'+1) *fact n'


def list_len {α : Type} : List α → Nat
| [] => 0
| h::t => 1+ list_len t

#eval list_len [1,2,3,4]