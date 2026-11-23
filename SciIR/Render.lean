import SciIR.Harness

/-!
# From the IR back to the human's language

The human never has to read the agent's prose.  What they read is printed from the IR by these
functions, so two claims with the same premises always read the same way, and a claim cannot
be worded more strongly than its grade.
-/

namespace SciIR

/-- How an assumption is introduced in a sentence. -/
def Assumption.kind (a : Assumption) : String :=
  match a.basis with
  | .cited src => s!"published theorem, {src}"
  | .conjectured => "conjecture"
  | .observed regime => s!"evidence, valid for {regime}"
  | .hypothesized falsifier => s!"hypothesis, refuted by {falsifier}"

def Assumption.render (a : Assumption) : String := s!"{a.name} ({a.kind}): {a.text}"

/-- A claim with its grade in front and its premises under it. -/
def Claim.render (c : Claim) : String :=
  let head := s!"[{c.grade.word}] {c.name}: {c.text}"
  c.premises.foldl (fun out a => out ++ s!"\n      rests on {a.render}") head

def Experiment.render (e : Experiment) : String :=
  s!"{e.name}, testing {", ".intercalate e.tests}\n      protocol: {e.protocol}\n      prediction: {e.prediction}" ++
  s!"\n      refuted by: {e.falsifier}\n      calibration: {e.calibration}"

def Verdict.render : Verdict → String
  | .proceed => "PROCEED"
  | .reject why => s!"REJECT  {why}"
  | .detour why => s!"DETOUR  {why}"
  | .ask qs => qs.foldl (fun out q => out ++ s!"\n      ? {q.ask}" ++
      q.options.foldl (fun o opt => o ++ s!"\n          - {opt}") "") "ASK THE HUMAN"

end SciIR
