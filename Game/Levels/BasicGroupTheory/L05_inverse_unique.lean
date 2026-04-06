import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 5

Introduction "If an element in a monoid has an inverse, that inverse is **unique**. This level proves: given $a \\cdot b = 1$, $b \\cdot a = 1$, $a \\cdot c = 1$, and $c \\cdot a = 1$, then $b = c$.

The proof idea is a classic trick: start with $b$, multiply by $1$ on the right, replace $1$ with $a \\cdot c$, re-associate, replace $b \\cdot a$ with $1$, and simplify.

Key theorems used:
- `mul_one` : `a * 1 = a`
- `mul_assoc` : `a * b * c = a * (b * c)`
- `one_mul` : `1 * a = a`"
open Monoid
variable (G :Type*) [Monoid G]

Statement (a b c: G)
  (leftinvb : a * b = 1)
  (rightinvb : b * a = 1)
  (leftinvc : a * c = 1)
  (rightinvc : c * a = 1)
: b = c := by
  Hint "Start by rewriting `b` as `b * 1`. Use `rw [<-mul_one b]` -- the `←` direction of `mul_one` rewrites `b` into `b * 1`."
  rw [<-mul_one b]

  Hint "Now replace `1` with `a * c` using `rw [<-leftinvc]`, since `{leftinvc} : a * c = 1`."
  rw [<-leftinvc]

  Hint "Re-associate using `rw [<-mul_assoc]` to change `b * (a * c)` into `b * a * c`."
  rw [<-mul_assoc]

  Hint "Now use `rw [rightinvb]` to replace `b * a` with `1`."
  rw [rightinvb]

  Hint "Finally, use `rw [one_mul]` to simplify `1 * c` to `c`."
  rw [one_mul]

NewTheorem And.intro mul_one mul_assoc one_mul
