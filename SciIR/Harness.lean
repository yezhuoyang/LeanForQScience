import SciIR.Basic

/-!
# The harness: when the agent may go on, and when it must stop

The agent works by submitting steps.  `gate` looks at the state and the step and returns one
of four verdicts.  It is an ordinary function: it reads no prose and it does not ask the agent
whether the agent thinks it should stop.

* `proceed`: the step is recorded.
* `reject`: the step is wrong as stated (an overclaim, an unlisted premise, an untested
  hypothesis in a report).
* `detour`: the agent moved to a goal with no certificate that it serves the old one.
* `ask`: only the human can settle this; the question is rendered for them.
-/

namespace SciIR

/-- Something only the human can settle. -/
structure Question where
  id : String
  ask : String
  options : List String
  deriving Repr, Inhabited

/--
A human's reply.  The constructor is private: a module written by the agent cannot build one,
so a step that needs a decision cannot be made to pass by the agent alone.
-/
structure Decision where
  private mk ::
  question : Question
  answer : String

namespace Human

/--
The only way to obtain a `Decision`.  In a live harness this waits for the person; in the
examples of this repository the replies are scripted.
-/
def answer (q : Question) (reply : String) : Decision := ⟨q, reply⟩

end Human

/-- Something the human wants established, and the weakest grade they accept for it. -/
structure Goal where
  id : String
  prop : Prop
  text : String
  accept : Grade

/-- A certificate that reaching `new` also reaches `old`. -/
structure Refines (new old : Goal) where
  /-- The reason in a sentence, for the human. -/
  because : String
  proof : new.prop → old.prop

/-- An experiment: what it tests, what it predicts, and what outcome would refute that. -/
structure Experiment where
  name : String
  /-- Names of the assumptions it can refute. -/
  tests : List String
  protocol : String
  prediction : String
  falsifier : String
  /-- A regime where the answer is already known, to check the apparatus. -/
  calibration : String

/-- What the agent can submit. -/
inductive Step where
  /-- Lean on these, in the service of a goal. -/
  | assume (as : List Assumption) (goal : Goal)
  /-- State a claim at a declared grade, in the service of a goal. -/
  | assert (c : Claim) (declared : Grade) (goal : Goal)
  /-- Work towards `new` instead of `old`. -/
  | retarget (old new : Goal) (cert : Option (Refines new old))
  /-- Propose an experiment. -/
  | propose (e : Experiment)
  /-- Report these claims as the result. -/
  | report (claims : List Claim)

inductive Verdict where
  | proceed
  | reject (why : String)
  | detour (why : String)
  | ask (questions : List Question)

/-- What the harness remembers. -/
structure State where
  /-- Questions the intention leaves open. -/
  holes : List Question := []
  /-- Every assumption in use. -/
  ledger : List Assumption := []
  /-- Assumptions a human decision has allowed beyond a goal's accepted grade. -/
  accepted : List String := []
  claims : List Claim := []
  /-- Experiments the human approved. -/
  experiments : List Experiment := []
  decisions : List Decision := []

def names (as : List Assumption) : String := ", ".intercalate (as.map (·.name))

/-- Is the assumption allowed for this goal: by the goal's grade, or by a decision? -/
def State.allows (s : State) (goal : Goal) (a : Assumption) : Bool :=
  decide (a.basis.grade ≤ goal.accept) || s.accepted.contains a.name

/-- Does an approved experiment test this assumption? -/
def State.tested (s : State) (a : Assumption) : Bool :=
  s.experiments.any (·.tests.contains a.name)

def isHypothesis (a : Assumption) : Bool :=
  match a.basis with
  | .hypothesized _ => true
  | _ => false

/-- The gate. -/
def gate (s : State) (step : Step) : Verdict :=
  -- Nothing starts while the intention has open questions.
  if !s.holes.isEmpty then .ask s.holes else
  match step with
  | .assume as goal =>
    match as.filter (fun a => !s.allows goal a) with
    | [] => .proceed
    | extra => .ask [{
        id := s!"accept {names extra}"
        ask := s!"For \"{goal.text}\" you accepted a result that is {goal.accept.word}. " ++
          s!"Using {names extra} would make it {(goal.accept.join (gradeOf extra)).word}. Accept that?"
        options := ["accept, and report it as such", "do not accept: find another route"] }]
  | .assert c declared _ =>
    if !decide (c.grade ≤ declared) then
      .reject s!"{c.name} is declared \"{declared.word}\" but rests on {names c.premises}: it is \"{c.grade.word}\"."
    else match c.premises.filter (fun a => !s.ledger.any (·.name == a.name)) with
    | [] => .proceed
    | missing => .reject s!"{c.name} uses {names missing}, which the ledger does not hold."
  | .retarget old new none =>
    .detour s!"no certificate that reaching \"{new.text}\" reaches \"{old.text}\"."
  | .retarget _ _ (some _) => .proceed
  | .propose e =>
    match e.tests.filter (fun n => !s.ledger.any (·.name == n)) with
    | [] => .ask [{
        id := s!"approve {e.name}"
        ask := s!"Experiment {e.name} tests {", ".intercalate e.tests}. Protocol: {e.protocol} " ++
          s!"Prediction: {e.prediction} It is refuted by: {e.falsifier} Approve?"
        options := ["approve", "revise", "drop"] }]
    | unknown => .reject s!"{e.name} tests {", ".intercalate unknown}, which the ledger does not hold."
  | .report claims =>
    let untested := (claims.flatMap (·.premises)).filter (fun a => isHypothesis a && !s.tested a)
    match untested.map (·.name) |>.eraseDups with
    | [] => .proceed
    | ns => .reject s!"the report rests on {", ".intercalate ns}: hypotheses with no approved experiment."

/-- Record a step that passed. -/
def State.record (s : State) : Step → State
  | .assume as _ => { s with ledger := s.ledger ++ as.filter (fun a => !s.ledger.any (·.name == a.name)) }
  | .assert c _ _ => { s with claims := s.claims ++ [c] }
  | _ => s

/-- Record a human reply: it closes its question and may allow assumptions or approve experiments. -/
def State.decide (s : State) (d : Decision) (allow : List Assumption := []) (approve : List Experiment := []) : State :=
  { s with
    holes := s.holes.filter (·.id != d.question.id)
    accepted := s.accepted ++ allow.map (·.name)
    experiments := s.experiments ++ approve
    decisions := s.decisions ++ [d] }

end SciIR
