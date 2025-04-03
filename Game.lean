import Game.Metadata
import Game.Levels.BasicLean
import Game.Levels.BasicGroupTheory
import Game.Levels.GroupHomo

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
