import SciIR.Syntax
import SciIR.Episode

/-!
# A worked episode

The human's intention, verbatim:

> Find a quantum algorithm with advantage over classical algorithms that finds a
> high-temperature superconducting material, and propose a concrete experiment to prove it.

This file writes one research episode on that intention in SciIR: the vocabulary, the things
the agent leans on, the claims with their proofs, and the steps it submits to the gate.

The physics and the complexity theory are *named*, not formalized: `Superconducts`,
`QuantumEfficient` and the rest are opaque predicates.  What Lean checks here is the part that
goes wrong in prose: which statement rests on which, at what grade, and whether a step serves
the intention.  Replacing the opaque predicates by definitions is the work this project is for.
-/

namespace SciIR.Superconductor

/-! ## Vocabulary: different things have different types -/

/-- A temperature. -/
structure Kelvin where
  val : Nat

/-- An energy. -/
structure MilliElectronVolt where
  val : Nat

inductive Pressure where
  | ambient
  | gigapascal (p : Nat)

/-- A compound that can be synthesized and measured. -/
structure Material where
  name : String

/-- A Hamiltonian on paper. -/
structure Model where
  name : String

/-- A computational problem: a family of instances. -/
structure Problem where
  name : String

/-- The material shows zero resistance and expels flux below the given temperature, at the given pressure. -/
opaque Superconducts : Material → Kelvin → Pressure → Prop
/-- A quantum algorithm solves the problem in polynomial time. -/
opaque QuantumEfficient : Problem → Prop
/-- A classical algorithm solves the problem in polynomial time. -/
opaque ClassicallyEfficient : Problem → Prop
/-- No classical method known today solves the problem at polynomial cost with controlled error. -/
opaque NoKnownClassical : Problem → Prop
/-- The instances come with an efficiently preparable state of inverse-polynomial overlap with the ground state. -/
opaque Guided : Problem → Prop
opaque BQPneBPP : Prop
/-- The algorithm, run on the model downfolded from this material, reports d-wave pairing above the threshold. -/
opaque PairsInModel : Material → Prop
/-- The material itself pairs above the threshold. -/
opaque PairsInMaterial : Material → Prop

def hubbard : Model := ⟨"Fermi-Hubbard model with hoppings t, t' and repulsion U on the square lattice"⟩
def guided : Problem := ⟨"guided local Hamiltonian"⟩
def dopedHubbard : Problem := ⟨"pairing in the ground state of the doped two-dimensional Hubbard model"⟩
def chain : Problem := ⟨"ground-state energy of the one-dimensional Hubbard chain"⟩
def liquidNitrogen : Kelvin := ⟨77⟩
def pairingGap : MilliElectronVolt := ⟨0⟩
def candidate : Material := ⟨"the top-ranked compound"⟩

/-- Qubits for an L by L lattice: two spin orbitals per site, one qubit per spin orbital (Jordan-Wigner). -/
def systemQubits (L : Nat) : Nat := 2 * (L * L)

/-! ## Two sentences that prose lets through and the type checker does not -/

-- "The Hubbard model superconducts at 77 K."  A model is not a material.
#check_failure Superconducts hubbard liquidNitrogen .ambient

-- "The gap gives the transition temperature."  An energy is not a temperature.
#check_failure Superconducts candidate pairingGap .ambient

/-! ## What the agent leans on -/

/-- Guided local Hamiltonian is BQP-complete: a quantum computer solves it in polynomial time, and a classical one does not unless BQP = BPP. -/
literature T1 : QuantumEfficient guided ∧ (BQPneBPP → ¬ ClassicallyEfficient guided)
  from "Gharibian and Le Gall, arXiv:2111.09079"

/-- Phase estimation finds the ground-state energy in polynomial time when a guiding state is given. -/
literature T3 : ∀ P, Guided P → QuantumEfficient P
  from "Abrams and Lloyd, Phys. Rev. Lett. 83, 5162"

/-- BQP differs from BPP. -/
conjecture K1 : BQPneBPP

/-- The doped Hubbard instances are as hard as the whole guided class. -/
conjecture X1 : ¬ ClassicallyEfficient guided → ¬ ClassicallyEfficient dopedHubbard

/-- The doped Hubbard instances have guiding states: efficiently preparable, with inverse-polynomial overlap. -/
hypothesis G1 : Guided dopedHubbard
  falsified_by "an overlap that falls exponentially with the lattice size"

/-- No classical method known today solves the doped instances at polynomial cost with controlled error. -/
evidence S1 : NoKnownClassical dopedHubbard
  regime "the lattice sizes and dopings benchmarked to date"

/-- Pairing in the downfolded model means pairing in the material. -/
hypothesis B1 : ∀ m, PairsInModel m → PairsInMaterial m
  falsified_by "a compound whose model pairs while its measured gap is absent or not d-wave"

/-- Pairing above the threshold means a transition at or above 77 K at ambient pressure. -/
hypothesis B2 : ∀ m, PairsInMaterial m → Superconducts m liquidNitrogen .ambient
  falsified_by "a material that pairs above the threshold and has no transition above 77 K"

/-! ## Claims.  Each proof is from the listed assumptions and nothing else. -/

/-- Phase estimation gives an exponential quantum advantage for the Hubbard model. -/
claim C0 : QuantumEfficient dopedHubbard ∧ ¬ ClassicallyEfficient dopedHubbard
  uses [T1, K1, T3, G1, X1] := fun t1 k1 t3 g1 x1 => ⟨t3 _ g1, x1 (t1.2 k1)⟩

/-- On the guided local Hamiltonian problem, a quantum computer is efficient and no classical algorithm is. -/
claim C1 : QuantumEfficient guided ∧ ¬ ClassicallyEfficient guided
  uses [T1, K1] := fun t1 k1 => ⟨t1.1, t1.2 k1⟩

/-- On the doped Hubbard instances, phase estimation is efficient and no known classical method is. -/
claim C2 : QuantumEfficient dopedHubbard ∧ NoKnownClassical dopedHubbard
  uses [T3, G1, S1] := fun t3 g1 s1 => ⟨t3 _ g1, s1⟩

/-- Every material the algorithm selects superconducts at or above 77 K at ambient pressure. -/
claim P1 : ∀ m, PairsInModel m → Superconducts m liquidNitrogen .ambient
  uses [B1, B2] := fun b1 b2 m h => b2 m (b1 m h)

/-- An L by L lattice takes 2 L^2 system qubits. -/
claim Q1 : ∀ L, systemQubits L = 2 * L * L
  uses [] := fun L => by simp [systemQubits, Nat.mul_assoc]

-- Leave a premise out and the claim no longer compiles: the proof has nothing to call `b2`.
-- claim P1' : ∀ m, PairsInModel m → Superconducts m liquidNitrogen .ambient
--   uses [B1] := fun b1 m h => b2 m (b1 m h)

/-! ## The intention, its open questions, and the goals the replies fix -/

def intention : String :=
  "Find a quantum algorithm with advantage over classical algorithms that finds a " ++
  "high-temperature superconducting material, and propose a concrete experiment to prove it."

def qAdvantage : Question where
  id := "advantage"
  ask := "\"advantage\": in which sense?"
  options := ["a proved separation", "conditional on a named conjecture",
    "against the best classical methods known, on stated instances"]

def qHot : Question where
  id := "high-temperature"
  ask := "\"high-temperature\": above which transition temperature, at which pressure?"
  options := ["77 K at ambient pressure", "77 K at any pressure", "room temperature at ambient pressure"]

def qIt : Question where
  id := "prove it"
  ask := "\"prove it\": what must the experiment test?"
  options := ["the advantage", "that the material superconducts", "both"]

/-- Fixed by the reply to `qAdvantage`: conditional on a named conjecture, and on nothing weaker. -/
def advantage : Goal where
  id := "advantage"
  prop := QuantumEfficient dopedHubbard ∧ ¬ ClassicallyEfficient dopedHubbard
  text := "a quantum algorithm for the doped Hubbard model that no classical algorithm matches"
  accept := { cited := true, conjectured := true }

/-- The weaker goal the human allows later, beside the first: against known methods. -/
def advantageKnown : Goal where
  id := "advantage, known methods"
  prop := QuantumEfficient dopedHubbard ∧ NoKnownClassical dopedHubbard
  text := "a quantum algorithm for the doped Hubbard model that no known classical method matches"
  accept := { cited := true, conjectured := true, observed := true, hypothesized := true }

/-- Fixed by the reply to `qHot`.  A statement about the world: hypotheses are allowed, experiments are owed. -/
def material : Goal where
  id := "material"
  prop := ∀ m, PairsInModel m → Superconducts m liquidNitrogen .ambient
  text := "the materials the algorithm selects superconduct at 77 K and ambient pressure"
  accept := { cited := true, conjectured := true, observed := true, hypothesized := true }

def chainGoal : Goal where
  id := "chain"
  prop := QuantumEfficient chain
  text := "reproduce the exact energies of the one-dimensional Hubbard chain"
  accept := .proved

/-! ## The experiments -/

def Emat : Experiment where
  name := "E-mat"
  tests := ["B1", "B2"]
  protocol := "synthesize the top-ranked compound; measure resistivity and magnetic susceptibility against temperature at ambient pressure."
  prediction := "zero resistance and flux expulsion setting in at or above 77 K."
  falsifier := "no transition above 77 K, or a drop in resistance without flux expulsion."
  calibration := "the same measurement on a known cuprate superconductor."

def Eadv : Experiment where
  name := "E-adv"
  tests := ["G1"]
  protocol := "run the algorithm on doped L by L instances of growing L; run the best classical methods on the same instances."
  prediction := "the guiding state's overlap falls no faster than a power of L, and the algorithm keeps its accuracy where the classical cost grows."
  falsifier := "an overlap that falls exponentially with L, or a classical method that matches the accuracy at comparable cost."
  calibration := "the one-dimensional chain, solved exactly, and half filling with t' = 0, where quantum Monte Carlo has no sign problem."

/-! ## The episode -/

def full : Grade := { cited := true, conjectured := true, observed := true, hypothesized := true }

def script : List Entry := [
  .agent "Read the intention"
    "The goal is clear. I will start from the Hubbard model."
    (.assume [B1] material),
  .human (Human.answer qAdvantage "conditional on a named conjecture"),
  .human (Human.answer qHot "77 K at ambient pressure"),
  .human (Human.answer qIt "both"),

  .illTyped "Choose the model"
    "High-temperature superconductors are described by the Hubbard model, so I look for where the Hubbard model superconducts."
    "Superconducts hubbard liquidNitrogen .ambient"
    "`hubbard` is a Model; `Superconducts` takes a Material. The step from one to the other has to be stated.",
  .agent "State the bridge from model to material"
    "Then I state it: pairing in the downfolded model means pairing in the material."
    (.assume [B1] material),

  .agent "Claim the advantage"
    "Ground states are exponentially hard classically and phase estimation finds them, so the advantage is exponential and proved."
    (.assert C0 .proved advantage),
  .agent "Claim what the literature gives"
    "For the guided class, hardness is a theorem and the separation needs one conjecture."
    (.assume [T1, K1] advantage),
  .agent "Claim what the literature gives"
    "So: on the guided class, quantum is efficient and classical is not, given BQP differs from BPP."
    (.assert C1 { cited := true, conjectured := true } advantage),

  .agent "Bring it down to the Hubbard instances"
    "For our instances I need a guiding state, and the comparison is against known methods."
    (.assume [T3, G1, S1] advantage),
  .human (Human.answer
      { id := "accept G1, S1", ask := "", options := [] }
      "accept, and report it beside C1, as what it is")
    (allow := [G1, S1]),
  .agent "Bring it down to the Hubbard instances"
    "Entered, with the human's leave."
    (.assume [T3, G1, S1] advantage),
  .agent "Bring it down to the Hubbard instances"
    "On the doped instances: efficient with a guiding state, against the classical methods known."
    (.assert C2 full advantageKnown),

  .agent "Test on something solvable"
    "The one-dimensional chain is exactly solvable. I reproduce its energies to six digits: the algorithm works, so I continue there."
    (.retarget advantage chainGoal none),

  .illTyped "From pairing to a temperature"
    "The pairing gap gives the transition temperature."
    "Superconducts candidate pairingGap .ambient"
    "`pairingGap` is an energy; `Superconducts` takes a temperature. The relation between the two has to be stated.",
  .agent "From pairing to a temperature"
    "Then I state it: pairing above the threshold means a transition at or above 77 K."
    (.assume [B2] material),
  .agent "From pairing to a temperature"
    "So every material the algorithm selects superconducts at 77 K, given B1 and B2."
    (.assert P1 full material),

  .agent "Count the qubits"
    "Under Jordan-Wigner an L by L lattice takes 2 L^2 system qubits."
    (.assert Q1 .proved advantage),

  .agent "Report"
    "Done: an algorithm with an advantage that finds high-temperature superconductors."
    (.report [C1, C2, P1, Q1]),

  .agent "Propose the experiment on the material"
    "B1 and B2 are untested. Synthesize what the algorithm ranks first and measure it."
    (.propose Emat),
  .human (Human.answer { id := "approve E-mat", ask := "", options := [] } "approve") (approve := [Emat]),
  .agent "Propose the experiment on the advantage"
    "G1 is untested. Run the algorithm against the classical methods as the lattice grows."
    (.propose Eadv),
  .human (Human.answer { id := "approve E-adv", ask := "", options := [] } "approve") (approve := [Eadv]),

  .agent "Report"
    "The report, with what each claim rests on and the two experiments."
    (.report [C1, C2, P1, Q1])
]

/-- What the same episode reports when nothing checks it. -/
def freeProse : String :=
  "We present a quantum algorithm with a proved exponential advantage that finds high-temperature " ++
  "superconductors, validated to six digits on the Hubbard chain."

end SciIR.Superconductor
