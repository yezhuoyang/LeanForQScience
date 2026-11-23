import SciIR.Render

/-!
# Playing an episode

An episode is a list of entries: what the agent submitted, what Lean's type checker refused
before anything was submitted, and what the human replied.  `play` runs it through the gate
and prints the trace.
-/

namespace SciIR

inductive Entry where
  /-- The agent's thought in its own words, and the step it submits. -/
  | agent (title says : String) (step : Step)
  /-- A statement that did not type-check, with Lean's complaint in a sentence. -/
  | illTyped (title says attempt error : String)
  /-- A human reply. -/
  | human (d : Decision) (allow : List Assumption := []) (approve : List Experiment := [])

def Step.render : Step → String
  | .assume as goal => s!"assume {names as}   (for: {goal.id})"
  | .assert c declared goal => s!"claim {c.name}, declared \"{declared.word}\"   (for: {goal.id})"
  | .retarget old new _ => s!"retarget {old.id} -> {new.id}"
  | .propose e => s!"propose experiment {e.name}"
  | .report claims => s!"report {", ".intercalate (claims.map (·.name))}"

/-- Run the entries through the gate, printing each verdict; return the final state. -/
def play (holes : List Question) (script : List Entry) : IO State := do
  let mut s : State := { holes := holes }
  let mut n := 0
  for entry in script do
    match entry with
    | .agent title says step =>
      n := n + 1
      let v := gate s step
      IO.println s!"\n{n}. {title}"
      IO.println s!"   agent:  {says}"
      IO.println s!"   step:   {step.render}"
      IO.println s!"   gate:   {v.render}"
      if let .proceed := v then s := s.record step
    | .illTyped title says attempt error =>
      n := n + 1
      IO.println s!"\n{n}. {title}"
      IO.println s!"   agent:  {says}"
      IO.println s!"   writes: {attempt}"
      IO.println s!"   Lean:   TYPE ERROR  {error}"
    | .human d allow approve =>
      IO.println s!"   human:  {d.question.id}: {d.answer}"
      s := s.decide d allow approve
  return s

/-- The result, printed from the IR. -/
def State.report (s : State) : String :=
  let claims := s.claims.foldl (fun out c => out ++ s!"\n  {c.render}") "Claims"
  let exps := s.experiments.foldl (fun out e => out ++ s!"\n  {e.render}") "\nExperiments approved"
  let decs := s.decisions.foldl (fun out d => out ++ s!"\n  {d.question.id}: {d.answer}") "\nDecisions by the human"
  claims ++ exps ++ decs

end SciIR
