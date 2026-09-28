-- Define discrete states for a Markov Chain
inductive WeatherState
  | sunny
  | rainy
  deriving DecidableEq, Repr

open WeatherState

-- Transition matrix logic
def transitionProb (fromState : WeatherState) (toState : WeatherState) : Float :=
  match fromState, toState with
  | sunny, sunny => 0.8
  | sunny, rainy => 0.2
  | rainy, sunny => 0.4
  | rainy, rainy => 0.6

structure Distribution where
  pSunny : Float
  pRainy : Float
  deriving Repr

-- 1-step matrix multiplication
def step (d : Distribution) : Distribution :=
  { pSunny := d.pSunny * transitionProb sunny sunny + d.pRainy * transitionProb rainy sunny,
    pRainy := d.pSunny * transitionProb sunny rainy + d.pRainy * transitionProb rainy rainy }

-- Recursive simulation over n steps
def stepN (d : Distribution) : Nat → Distribution
  | 0     => d
  | n + 1 => step (stepN d n)

-- The executable entry point
def main : IO Unit := do
  IO.println "=== Lean 4 Execution Output ==="

  let initialDay : Distribution := { pSunny := 1.0, pRainy := 0.0 }

  IO.println s!"Day 0: Sunny={initialDay.pSunny}, Rainy={initialDay.pRainy}"

  -- Loop through 5 days and print results
  for i in [1:6] do
    let state := stepN initialDay i
    IO.println s!"Day {i}: Sunny={state.pSunny}, Rainy={state.pRainy}"

  IO.println "Simulation complete!"

-- Evaluate directly inside VS Code InfoView
#eval main
