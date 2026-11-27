/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import all CslibFrontierTests.NetlistText
import CslibFrontier.Languages.Electrical.NetlistPrint

/-! # Tests for printing netlists

* The RC filter read from its exported text (`CslibFrontierTests.NetlistText.rcParsed`) is
  printable; its printed text is shown, read back, and the certificate is accepted against it,
  so the guarantee holds for the netlist itself, without the reader in the statement
  (`Cslib.Electrical.Text.guarantee_of_checkText_print`).
* Netlists outside the printable normal form are not printable: a node numbered out of order of
  first appearance, a value without a decimal expansion, and a branch name with the wrong
  letter.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.NetlistPrint

open Cslib.Electrical Cslib.Electrical.Text CslibFrontierTests.NetlistText

theorem rcParsed_isPrintable : rcParsed.isPrintable = true := by decide +kernel

/-- The printed text of the RC filter. -/
example : print rcParsed = ".title netlist
V1 /in 0 dc 0 ac
R1 /in /out 1000
C1 /out 0 1e-6
.probe v /out 0
.end
" := by decide +kernel

/-- The round trip, by the theorem and by evaluation. -/
example : parse (print rcParsed) = .ok rcParsed := parse_print rcParsed_isPrintable
example : parse (print rcParsed) = .ok rcParsed := eq_ok_of_okOf (by decide +kernel)

theorem rcPrint_check : checkText (print rcParsed) rcCert = true := by decide +kernel

/-- **The guarantee for the RC netlist itself**, from its printed text. -/
example : rcCert.Guarantee rcParsed :=
  guarantee_of_checkText_print rcParsed_isPrintable rcPrint_check

/-- Not printable: node `2` appears before node `1`. -/
example : ({ rcParsed with netlist := { rcParsed.netlist with
    branches := [⟨2, 0, .voltageSource 0 (some 0)⟩, ⟨2, 1, .resistor 1000⟩,
      ⟨1, 0, .capacitor (1/1000000)⟩] } } : ParsedNetlist).isPrintable = false := by
  decide +kernel

/-- Not printable: `1/3` has no decimal expansion. -/
example : ({ rcParsed with netlist := { rcParsed.netlist with
    branches := [⟨1, 0, .voltageSource 0 (some 0)⟩, ⟨1, 2, .resistor (1/3)⟩,
      ⟨2, 0, .capacitor (1/1000000)⟩] } } : ParsedNetlist).isPrintable = false := by
  decide +kernel

/-- Not printable: the resistor is named `C2`. -/
example : ({ rcParsed with branchNames := ["V1".toList, "C2".toList, "C1".toList] } :
    ParsedNetlist).isPrintable = false := by
  decide +kernel

end CslibFrontierTests.NetlistPrint
