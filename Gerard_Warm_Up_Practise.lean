-- No imports needed! Pure Lean 4 core and standard library.

/-
=====================================================================
APPLIED ANALYSIS & DISCRETE MATHEMATICS STARTER SCRIPT
Tailored for: Gerard Lee (Math Postgrad, Applied Analysis focus)
=====================================================================
-/

-- ==========================================
-- 1. DISCRETE DYNAMICAL SYSTEM (Numerical Iteration)
-- ==========================================
-- In applied analysis, we study iterative numerical schemes.
-- Let's define a simple linear iterative scheme: u(0) = 1, u(n+1) = u(n) + 2

def u : Nat → Nat
  | 0 => 1
  | n + 1 => u n + 2

-- Theorem: The closed-form solution is u(n) = 2n + 1.
-- This demonstrates inductive proofs, which are the foundation of proving
-- convergence and stability of numerical algorithms.
theorem u_closed_form (n : Nat) : u n = 2 * n + 1 := by
  induction n with
  | zero =>
    -- Base case: u(0) = 1 = 2*0 + 1
    rfl
  | succ n ih =>
    -- Inductive step: Assume u(n) = 2n + 1, prove u(n+1) = 2(n+1) + 1
    rw [u]          -- Unfold the definition of u for n+1
    rw [ih]         -- Apply the inductive hypothesis
    -- Now we need to prove: 2n + 1 + 2 = 2(n+1) + 1
    -- `omega` is a built-in decision procedure for linear arithmetic on Nat.
    omega

-- ==========================================
-- 2. MARKOV CHAINS (Discrete State Space)
-- ==========================================
-- You have extensive experience with Markov chains.
-- Here we formalize a simple 2-state weather chain.

inductive Weather : Type
  | sunny : Weather
  | rainy : Weather
  deriving BEq, Repr, DecidableEq

-- Transition weights (scaled by 10 to avoid real numbers, since we don't have Mathlib)
def transition_weight : Weather → Weather → Nat
  | Weather.sunny, Weather.sunny => 9
  | Weather.sunny, Weather.rainy => 1
  | Weather.rainy, Weather.sunny => 4
  | Weather.rainy, Weather.rainy => 6

-- Theorem: The sum of transition weights from any state is always 10.
-- This proves that the matrix is row-stochastic (when normalized by 10).
theorem transition_sum_10 (w : Weather) : transition_weight w Weather.sunny + transition_weight w Weather.rainy = 10 := by
  cases w <;> decide

-- ==========================================
-- 3. GAME THEORY & OPTIMIZATION (Payoff Matrices)
-- ==========================================
-- You are taking Game Theory this term.
-- We define a custom Action type instead of using `Fin 2` to avoid Mathlib dependencies.
inductive Action : Type
  | cooperate : Action
  | defect : Action
  deriving DecidableEq, Repr

-- Payoff for Player 1 (Row player)
-- Actions: cooperate, defect
def payoff_P1 : Action → Action → Int
  | Action.cooperate, Action.cooperate => 3  -- Both cooperate
  | Action.cooperate, Action.defect => 0  -- P1 cooperates, P2 defects
  | Action.defect, Action.cooperate => 5  -- P1 defects, P2 cooperates
  | Action.defect, Action.defect => 1  -- Both defect

-- Theorem: Defect is a strictly dominant strategy for Player 1.
-- For any action of Player 2, choosing Defect yields a strictly higher payoff.
theorem defect_dominant (a2 : Action) : payoff_P1 Action.defect a2 > payoff_P1 Action.cooperate a2 := by
  cases a2 <;> decide
