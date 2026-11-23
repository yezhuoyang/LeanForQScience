# LeanForQScience

Lean infrastructure for AI-driven discovery in quantum science. The aim is to formalize the
discovery process as it happens, and not only its result, so that what an agent establishes
stays aligned with what the human asked for.

This repository holds the first demo: **SciIR**, a small typed language that sits between the
language people do research in and Lean, and a **gate** that decides from the IR when an agent
may go on, when a step is wrong, when it has drifted from the goal, and when it must ask the
human.

## Run it

Lean 4.36.0 (see `lean-toolchain`); no dependencies beyond Lean itself.

```
lake build
lake exe episode
```

`lake exe episode` plays one research episode on this intention:

> Find a quantum algorithm with advantage over classical algorithms that finds a
> high-temperature superconducting material, and propose a concrete experiment to prove it.

It prints 18 steps with the gate's verdict on each, then the report printed from the IR, then
the report the same episode produces in free prose. In the 18 steps the gate stops for the
human four times (once for the three things the sentence leaves open, once for a weakening of
the goal, once for each of the two experiments), rejects an overclaim and a report that rests
on untested hypotheses, flags one detour, and Lean's type checker refuses two sentences before
they are submitted.

## The idea in the code

**A statement carries what it rests on** (`SciIR/Basic.lean`). An `Assumption` is a named
statement used on a `Basis`: a cited theorem, a conjecture, evidence in a stated regime, or a
hypothesis about the world, which must name the observation that would refute it. A `Claim` is
a statement, its list of premises, and a Lean proof of the statement from exactly those
premises. Its `Grade` is computed from the premises and cannot be declared.

**A surface syntax** (`SciIR/Syntax.lean`). The doc comment is the statement's reading in the
human's language.

```lean
/-- BQP differs from BPP. -/
conjecture K1 : BQPneBPP

/-- Pairing in the downfolded model means pairing in the material. -/
hypothesis B1 : ∀ m, PairsInModel m → PairsInMaterial m
  falsified_by "a compound whose model pairs while its measured gap is absent or not d-wave"

/-- Every material the algorithm selects superconducts at or above 77 K at ambient pressure. -/
claim P1 : ∀ m, PairsInModel m → Superconducts m liquidNitrogen .ambient
  uses [B1, B2] := fun b1 b2 m h => b2 m (b1 m h)
```

Remove `B2` from the list and `P1` stops compiling: the proof has no `b2` to call.

**The gate** (`SciIR/Harness.lean`). An agent submits steps: assume, assert a claim at a
declared grade, retarget, propose an experiment, report. `gate : State → Step → Verdict`
returns `proceed`, `reject`, `detour` or `ask`. The rules of this first version:

| Situation | Verdict |
|---|---|
| The intention still has open questions | ask |
| An assumption is weaker than the goal's accepted grade and no decision allows it | ask |
| A claim is declared stronger than the grade of its premises | reject |
| A claim uses a premise the ledger does not hold | reject |
| The agent changes goal without a proof that the new goal reaches the old one | detour |
| An experiment is proposed | ask |
| A report rests on a hypothesis that no approved experiment tests | reject |

A `Decision` (a human's reply) has a private constructor, so a module written by the agent
cannot make one.

**Back to the human's language** (`SciIR/Render.lean`). What the human reads is printed from
the IR, so a claim cannot be worded more strongly than its grade.

## What is checked, and what is not

Checked by Lean's kernel:

- every claim's proof from its listed premises, and that it uses no others;
- `Claim.unconditional`: a claim graded `proved` holds with no assumption left;
- `basis_le_gradeOf`: the grade hides nothing, the basis of every premise shows in it;
- the two type errors in `SciIR/Examples/Superconductor.lean` (a model is not a material, an
  energy is not a temperature), kept in the file with `#check_failure`.

`#print axioms` on these gives `propext` only.

Not checked: the science. `Superconducts`, `QuantumEfficient`, `Guided` and the other
predicates of the example are opaque names, and the cited theorems are entered as cited, not
proved. The demo checks the bookkeeping that prose loses: which statement rests on which, at
what grade, and whether a step serves the intention. The human's replies in the episode are
scripted.

## Next

- Replace opaque predicates by definitions, starting where formal work already exists:
  circuits and compilation, then Hamiltonians and complexity classes.
- Let the gate see partial work: abstract interpretation of a plan, to tell early that a goal's
  accepted grade is out of reach on the current route.
- Run the gate inside an agent harness and compare with post-hoc formalization on the same
  tasks.

## Layout

```
SciIR/Basic.lean                    Basis, Assumption, Claim, Grade, and their theorems
SciIR/Syntax.lean                   conjecture, literature, evidence, hypothesis, claim
SciIR/Harness.lean                  Question, Decision, Goal, Step, Verdict, gate
SciIR/Render.lean                   the IR in the human's language
SciIR/Episode.lean                  playing a list of steps through the gate
SciIR/Examples/Superconductor.lean  the worked episode
Main.lean                           lake exe episode
```
