-- Define actions for a 2-choice game
inductive Action
  | cooperate
  | defect
  deriving DecidableEq, Repr

open Action

-- Payoff function for Player 1 in a symmetric Prisoner's Dilemma
-- Cooperate/Cooperate -> 3, Cooperate/Defect -> 0
-- Defect/Cooperate -> 5, Defect/Defect -> 1
def payoff1 (p1 p2 : Action) : Nat :=
  match p1, p2 with
  | cooperate, cooperate => 3
  | cooperate, defect    => 0
  | defect,    cooperate => 5
  | defect,    defect    => 1

-- Check payoffs interactively in the InfoView
#eval payoff1 defect cooperate    -- Outputs: 5
#eval payoff1 cooperate cooperate -- Outputs: 3

-- Definition: What it means for an action 'best' to strictly dominate another 'other'
def StrictlyDominates (best other : Action) : Prop :=
  ∀ (opponent : Action), payoff1 best opponent > payoff1 other opponent

-- Theorem: Defect strictly dominates Cooperate in this game
theorem defect_strictly_dominates_cooperate : StrictlyDominates defect cooperate := by
  intro opponent
  cases opponent
  · -- Opponent plays Cooperate: payoff1 defect cooperate > payoff1 cooperate cooperate
    simp [payoff1]
  · -- Opponent plays Defect: payoff1 defect defect > payoff1 cooperate defect
    simp [payoff1]
