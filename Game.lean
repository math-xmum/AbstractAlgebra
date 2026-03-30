import Game.Metadata
import Game.Levels.BasicLean
import Game.Levels.BasicFunctions
import Game.Levels.EquivalenceRelation
import Game.Levels.Magma
import Game.Levels.GroupBasics
import Game.Levels.CosetsAndLagrange
import Game.Levels.GroupHomo
import Game.Levels.GroupAction

set_option lean4game.showDependencyReasons true
-- Here's what we'll put on the title screen
Title "Abstract Algebra Game"
Introduction
"
Welcome to the abstract algebra game!
"

Info "
We plan to cover basic group theory, ring theory and Galois theory.
"



/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Abstract Algebra Game "
CaptionLong "Abstract Algebra Game for MAT205 Xiamen University Malaysia."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
