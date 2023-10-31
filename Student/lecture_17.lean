#check Empty
--inductive Empty : Type

inductive Chaos: Type
def from_empty (e: Empty) : Chaos := nomatch e

#check False
-- inductive False: Prop

def from_false (P : Prop) (p: False): P := _
