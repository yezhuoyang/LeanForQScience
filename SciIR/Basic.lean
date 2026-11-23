/-!
# SciIR: statements that carry what they rest on

In a paper, "we show X" can mean a proof, a proof under a conjecture, a numerical trend or a
prediction.  Here a statement cannot be written down without the list of things it leans on,
and how strongly it is known is computed from that list, never asserted.

* `Basis`: why something may be used without a proof.
* `Assumption`: a named statement used on some basis.
* `Claim`: a statement, the assumptions it uses, and a Lean proof of it from exactly those.
* `Grade`: which kinds of basis a claim rests on.  It is an abstraction of the list of
  assumptions, and the theorems at the end say the abstraction hides nothing.
-/

namespace SciIR

/-- Why a statement may be used without a proof. -/
inductive Basis where
  /-- A published theorem, cited and not yet formalized here. -/
  | cited (source : String)
  /-- Mathematics that is believed and unproved. -/
  | conjectured
  /-- Numerical or physical evidence, valid in the stated regime. -/
  | observed (regime : String)
  /-- A statement about the world.  It has to say which observation would refute it. -/
  | hypothesized (falsifier : String)
  deriving Repr, DecidableEq, Inhabited

/-- Which kinds of basis a claim rests on.  All four `false` means: proved outright. -/
structure Grade where
  cited : Bool := false
  conjectured : Bool := false
  observed : Bool := false
  hypothesized : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Grade

/-- Rests on nothing. -/
def proved : Grade := {}

/-- What a conclusion rests on when it uses both. -/
def join (a b : Grade) : Grade where
  cited := a.cited || b.cited
  conjectured := a.conjectured || b.conjectured
  observed := a.observed || b.observed
  hypothesized := a.hypothesized || b.hypothesized

/-- `a.le b`: everything `a` rests on is allowed by `b`. -/
def le (a b : Grade) : Bool :=
  (!a.cited || b.cited) && (!a.conjectured || b.conjectured) &&
  (!a.observed || b.observed) && (!a.hypothesized || b.hypothesized)

instance : LE Grade := ⟨fun a b => a.le b = true⟩

instance (a b : Grade) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.le b = true))

/-- The one word a reader gets: the weakest kind of support involved. -/
def word (g : Grade) : String :=
  if g.hypothesized then "predicted"
  else if g.observed then "supported by evidence"
  else if g.conjectured then "conditional"
  else if g.cited then "proved, given published theorems"
  else "proved"

end Grade

/-- The grade of leaning on one thing. -/
def Basis.grade : Basis → Grade
  | .cited _ => { cited := true }
  | .conjectured => { conjectured := true }
  | .observed _ => { observed := true }
  | .hypothesized _ => { hypothesized := true }

/-- A named statement that is used without a proof, and why that is allowed. -/
structure Assumption where
  name : String
  basis : Basis
  stmt : Prop
  /-- The statement in the human's language. -/
  text : String

/-- The grade of a list of assumptions: the join of their bases. -/
def gradeOf : List Assumption → Grade
  | [] => .proved
  | a :: rest => a.basis.grade.join (gradeOf rest)

/--
A claim: a statement, the assumptions it uses, and a proof of the statement from exactly
those assumptions.  There is no way to state a claim without its premises.
-/
structure Claim where
  name : String
  stmt : Prop
  /-- The statement in the human's language. -/
  text : String
  premises : List Assumption
  proof : (∀ a ∈ premises, a.stmt) → stmt

/-- How strongly a claim is known.  Computed, never declared. -/
def Claim.grade (c : Claim) : Grade := gradeOf c.premises

/-! ## What the grade guarantees -/

/-- If every premise holds, so does the claim. -/
theorem Claim.holds (c : Claim) (h : ∀ a ∈ c.premises, a.stmt) : c.stmt := c.proof h

/-- The grade hides nothing: the basis of every premise is allowed by the grade. -/
theorem basis_le_gradeOf {a : Assumption} {as : List Assumption} (h : a ∈ as) :
    a.basis.grade ≤ gradeOf as := by
  induction as with
  | nil => cases h
  | cons b rest ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · show (a.basis.grade.le (a.basis.grade.join (gradeOf rest))) = true
      cases a.basis <;> simp [Basis.grade, Grade.le, Grade.join]
    · have := ih h'
      show (a.basis.grade.le (b.basis.grade.join (gradeOf rest))) = true
      have h2 : a.basis.grade.le (gradeOf rest) = true := this
      revert h2
      cases a.basis <;> simp [Basis.grade, Grade.le, Grade.join] <;> intro h2 <;> simp [h2]

/-- A list graded `proved` is empty. -/
theorem nil_of_gradeOf_proved {as : List Assumption} (h : gradeOf as = .proved) : as = [] := by
  cases as with
  | nil => rfl
  | cons a rest =>
    exfalso
    have key : a.basis.grade ≤ gradeOf (a :: rest) := basis_le_gradeOf (List.mem_cons_self ..)
    rw [h] at key
    revert key
    show ¬ (a.basis.grade.le Grade.proved = true)
    cases a.basis <;> simp [Basis.grade, Grade.le, Grade.proved]

/-- A claim graded `proved` holds, with no assumption left. -/
theorem Claim.unconditional (c : Claim) (h : c.grade = .proved) : c.stmt := by
  have hnil : c.premises = [] := nil_of_gradeOf_proved h
  exact c.proof (by rw [hnil]; intro a ha; cases ha)

end SciIR
