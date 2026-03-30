import Game.Metadata
-- import Mathlib

World "GroupBasics"

Level 5

Title "Uniqueness of Inverses"

Introduction "
Note that if inverse exits, then it is unique.
"
open Monoid
variable (G :Type*) [Monoid G]

Introduction "The following statement proves that in a monoid, if an element $a$ has two right inverses $b$ and $c$ (and they are also left inverses), then $b = c$. This is a fundamental property of inverses in algebraic structures."

Statement (a b c: G)
  (leftinvb : a * b = 1)
  (rightinvb : b * a = 1)
  (leftinvc : a * c = 1)
  (rightinvc : c * a = 1)
: b = c := by
  Hint "We'll start by rewriting $b$ as $b * 1$ using the property that multiplying by 1 on the right doesn't change the value. You can use `rw [<-mul_one b]`."
  rw [<-mul_one b]

  Hint "Now we can substitute $a * c$ for 1 using the hypothesis {leftinvc}."
  rw [<-leftinvc]

  Hint "We need to rearrange the parentheses in the expression $b * (a * c)$ using the associativity of multiplication. "
  rw [<-mul_assoc]

  Hint "Now we can use the hypothesis {rightinvb} to replace $b * a$ with 1. "
  rw [rightinvb]

  Hint "Finally, we use the property that multiplying by 1 on the left doesn't change the value. "
  rw [one_mul]

Conclusion "Inverses are unique: if both b and c are inverses of a, then b = c. The proof uses associativity and the identity element."

NewTheorem And.intro mul_one mul_assoc one_mul
