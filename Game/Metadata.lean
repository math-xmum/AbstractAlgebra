import GameServer
import Mathlib.Tactic
import Mathlib.Data.Set.Basic

--import Game.Levels.Lemmas.GroupTheory
--import Game.Levels.Lemmas.Partition

--import Mathlib.Tactic.Common

--import Game.Generator.Basic

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file lean file per world
that imports all its levels.
-/


--lemma have_intro {Q : Prop} (P : Prop) (p : P) : (P→Q) → Q  := fun h => h p
