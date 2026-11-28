/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/
import CslibFrontierTests.Logics.Propositional.VeriPBProducer

/-!
# The producer corpus for VeriPB and CakePB

Writes the 90 instance and proof pairs of
`CslibFrontierTests.Logics.Propositional.VeriPBProducer` to a directory: for each of the 30
random instances `k`, `c{k}-dec` (`SAT : ρ` or `UNSAT`), `c{k}-opt` (`BOUNDS`) and `c{k}-enum`
(`ENUMERATION_COMPLETE`), each as `.opb` and `.pbp`. The proofs are produced by
`Cslib.Logic.PL.VeriPB.solve`, `Cslib.Logic.PL.VeriPB.refute`, `Cslib.Logic.PL.VeriPB.optimize`
and `Cslib.Logic.PL.VeriPB.enumerate`, and printed by the test-only printer
`CslibFrontierTests.Logics.Propositional.VeriPBProofText.pbpText`.

Run it with

```
lake build CslibFrontierTests.Logics.Propositional.VeriPBProducer
lake env lean --run scripts/VeriPBProducerCases.lean DIR
```

then check each pair with `veripb DIR/c0-dec.opb DIR/c0-dec.pbp` and
`cake_pb DIR/c0-dec.opb DIR/c0-dec.pbp`.
-/

/-- Write the corpus to the directory given as the argument (default `veripb-producer-cases`). -/
def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args.headD "veripb-producer-cases"
  IO.FS.createDirAll dir
  CslibFrontierTests.Logics.Propositional.VeriPBProducer.writeCases dir
  IO.println s!"wrote 90 instance and proof pairs to {dir}"
