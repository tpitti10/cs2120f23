/-
1.
-/
namespace dogs_like_cat
variable
(Dog : Type)
(Blue : Dog)

(Cat : Type)
(Likes : Dog → Cat → Prop)
(all_dogs_like_some_cat : ∀ (d : Dog), ∃ (c : Cat), Likes d c)

#check all_dogs_like_some_cat Blue
end dogs_like_cat

/-
2.
-/
namespace d_likes_w
variable
(Dog : Type)
(Likes : Dog → Dog → Prop)
(likes_transitive : ∀ (d g w : Dog), Likes d g → Likes g w → Likes d w)

#check likes_transitive
end d_likes_w

/-
3.
-/
namespace cat_likes_cat
variable
(Cat : Type)
(Likes : Cat → Cat → Prop)
(both_like : ∀ (c d : Cat), Likes c d → Likes d c)

#check both_like
end cat_likes_cat

/-
4.
-/
namespace cat_likes_itself
variable
(Cat : Type)
(Likes : Cat → Cat → Prop)
(likes_itself : ∀ (c : Cat), Likes c c)

#check likes_itself
end cat_likes_itself

/-
5.
-/
namespace every_cat
variable
(Cat : Type)
(Likes : Cat → Cat → Prop)
(every_cat_likes_everyother_cat : ∀ (c d : Cat), Likes c d)

(c d : Cat)
example : Likes c d := every_cat_likes_everyother_cat c d
