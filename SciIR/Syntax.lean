import SciIR.Basic

/-!
# The surface syntax

Four ways to lean on something, and one way to claim something.  The doc comment above each
is its reading in the human's language; it is stored with the statement and printed whenever
the harness has to show the statement to a person.

```
/-- BQP differs from BPP -/
conjecture K1 : BQPneBPP

/-- pairing in the model means pairing in the material -/
hypothesis B1 : ∀ m, PairsInModel m → PairsInMaterial m
  falsified_by "a compound whose model pairs while its measured gap does not"

/-- the algorithm's selections superconduct -/
claim P1 : ∀ m, PairsInModel m → Superconducts m T ambient
  uses [B1, B2] := fun b1 b2 m h => b2 m (b1 m h)
```

The term after `:=` is a proof of the statement from the listed assumptions, in order.
Lean checks it; a claim that needs an assumption it does not list does not compile.
-/

open Lean

namespace SciIR

/-- A doc comment's words on one line. -/
def oneLine (s : String) : String := Id.run do
  let mut out := ""
  let mut gap := false
  for c in s.toList do
    if c.isWhitespace then
      gap := true
    else
      if gap && out != "" then out := out.push ' '
      gap := false
      out := out.push c
  return out

/-- The words of a doc comment: the text of its node, without the two characters that close it. -/
def docText (doc : TSyntax `Lean.Parser.Command.docComment) : String :=
  match doc.raw[1] with
  | .atom _ val =>
    let chars := val.toList
    (chars.take (chars.length - 2)).foldl String.push ""
  | _ => ""

/-- The reading of a statement: its doc comment, or nothing. -/
def readingOf (doc : Option (TSyntax `Lean.Parser.Command.docComment)) : MacroM (TSyntax `str) := do
  match doc with
  | some d => return Syntax.mkStrLit (oneLine (docText d))
  | none => return Syntax.mkStrLit ""

/-- The name as the human sees it. -/
def nameOf (n : Ident) : TSyntax `str := Syntax.mkStrLit n.getId.toString

syntax (docComment)? "conjecture " ident " : " term : command
syntax (docComment)? "literature " ident " : " term " from " str : command
syntax (docComment)? "evidence " ident " : " term " regime " str : command
syntax (docComment)? "hypothesis " ident " : " term " falsified_by " str : command
syntax (docComment)? "claim " ident " : " term " uses " "[" ident,* "]" " := " term : command

macro_rules
  | `($[$doc:docComment]? conjecture $n:ident : $p:term) => do
    let text ← readingOf doc
    `($[$doc:docComment]? def $n : SciIR.Assumption :=
        { name := $(nameOf n), basis := .conjectured, stmt := $p, text := $text })
  | `($[$doc:docComment]? literature $n:ident : $p:term from $src:str) => do
    let text ← readingOf doc
    `($[$doc:docComment]? def $n : SciIR.Assumption :=
        { name := $(nameOf n), basis := .cited $src, stmt := $p, text := $text })
  | `($[$doc:docComment]? evidence $n:ident : $p:term regime $r:str) => do
    let text ← readingOf doc
    `($[$doc:docComment]? def $n : SciIR.Assumption :=
        { name := $(nameOf n), basis := .observed $r, stmt := $p, text := $text })
  | `($[$doc:docComment]? hypothesis $n:ident : $p:term falsified_by $f:str) => do
    let text ← readingOf doc
    `($[$doc:docComment]? def $n : SciIR.Assumption :=
        { name := $(nameOf n), basis := .hypothesized $f, stmt := $p, text := $text })
  | `($[$doc:docComment]? claim $n:ident : $p:term uses [$as,*] := $pf:term) => do
    let text ← readingOf doc
    let premises := as.getElems
    -- the proof's type: each premise's statement, in order, then the claim
    let ty ← premises.foldrM (fun a acc => `(SciIR.Assumption.stmt $a → $acc)) p
    -- each premise is taken out of the context by its membership in the list
    let args ← premises.mapM fun a => `(h $a (by simp))
    `($[$doc:docComment]? def $n : SciIR.Claim :=
        { name := $(nameOf n), stmt := $p, text := $text, premises := [$as,*],
          proof := fun h => ($pf : $ty) $args* })

end SciIR
