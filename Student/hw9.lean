### Use *em* For Classical Reasoning

Accepting the law of the excluded middle as an axiom puts
us back in classical reasoning space. Using it, you can get
yourself proofs of both A ∨ ¬A and B ∨ ¬B, and now, to prove
the validity of the DeMorgan's law variant that had us hung up,
it's just a matter of showing that the proposition is true in each
of the four resulting cases.

HOMEWORK: Complete this proof.
-/

example (A B : Prop) : ¬(A ∧ B) -> ¬A ∨ ¬B :=
λ nab =>
let proof_of_aornota := em A
let proof_of_bornotb := em B
match proof_of_aornota with
| Or.inl a =>
  match proof_of_bornotb with
  |Or.inl b => False.elim (nab ⟨a,b⟩)
  |Or.inr notb => Or.inr notb
|Or.inr nota => Or.inl nota
