import SciIR

open SciIR SciIR.Superconductor

def main : IO Unit := do
  IO.println "INTENTION"
  IO.println s!"  {intention}"
  let final ← play [qAdvantage, qHot, qIt] script
  IO.println "\n\nREPORT, printed from the IR"
  IO.println final.report
  IO.println "\n\nTHE SAME EPISODE IN FREE PROSE"
  IO.println s!"  {freeProse}"
