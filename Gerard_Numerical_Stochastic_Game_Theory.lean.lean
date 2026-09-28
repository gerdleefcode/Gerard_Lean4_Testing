-- No imports needed! Pure Lean 4 core and standard library.

/-
=====================================================================
ADVANCED APPLIED MATHEMATICS STARTER SCRIPT
Tailored for: Gerard Lee (Math Postgrad, Applied Analysis focus)
=====================================================================
-/

-- ==========================================
-- 1. NUMERICAL ANALYSIS: Newton's Method for Square Roots
-- ==========================================

theorem babylonian_decreases (S x : Nat) (hx : x > 0) (h : S < x * x) :
    (x + S / x) / 2 < x := by
  -- We want to prove (x + S/x)/2 < x.
  -- By the division lemma, this is equivalent to x + S/x < x * 2.
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]

  -- We know S/x < x because S < x*x.
  have h1 : S / x < x := by
    rw [Nat.div_lt_iff_lt_mul hx]
    exact h

  -- Now we just need to prove x + S/x < 2*x, which follows from h1.
  omega

-- ==========================================
-- 2. MARKOV CHAINS: State Reachability
-- ==========================================

inductive State : Type
  | A | B | C | D
  deriving DecidableEq, Repr

-- Define the directed edges of our Markov chain
inductive Edge : State → State → Prop
  | ab : Edge State.A State.B
  | bc : Edge State.B State.C
  | cd : Edge State.C State.D
  | dd : Edge State.D State.D  -- D is an absorbing state

-- Define what it means for a path to exist between two states
inductive Path : State → State → Prop
  | refl (s : State) : Path s s
  | step {u v w : State} : Edge u v → Path v w → Path u w

-- Theorem: There exists a path from A to D.
-- This proves reachability, a crucial property in Markov chain analysis.
theorem reach_D_from_A : Path State.A State.D := by
  apply Path.step Edge.ab
  apply Path.step Edge.bc
  apply Path.step Edge.cd
  apply Path.refl

-- ==========================================
-- 3. GAME THEORY: Strict Dominance in 3x3
-- ==========================================

inductive Action : Type
  | a | b | c
  deriving DecidableEq, Repr

-- Payoff matrix for Player 1 (Row player)
-- Actions: a, b, c
def payoff_P1 : Action → Action → Int
  | Action.a, Action.a => 1
  | Action.a, Action.b => 1
  | Action.a, Action.c => 1
  | Action.b, Action.a => 2
  | Action.b, Action.b => 3
  | Action.b, Action.c => 6  -- CHANGED FROM 4 TO 6 to make 'b' strictly dominant
  | Action.c, Action.a => 0
  | Action.c, Action.b => -1
  | Action.c, Action.c => 5

-- Theorem: Action `b` strictly dominates Action `a` for Player 1.
theorem b_strictly_dominates_a (a2 : Action) :
    payoff_P1 Action.b a2 > payoff_P1 Action.a a2 := by
  cases a2 <;> decide

-- Theorem: Action `b` strictly dominates Action `c` for Player 1.
theorem b_strictly_dominates_c (a2 : Action) :
    payoff_P1 Action.b a2 > payoff_P1 Action.c a2 := by
  cases a2 <;> decide
