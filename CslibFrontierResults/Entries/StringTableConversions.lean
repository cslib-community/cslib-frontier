/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.WordRAM.ZFunction.ToPrefix
import CslibFrontier.Algorithms.WordRAM.ZFunction.FromPrefix

/-!
# Linear conversions between Z-tables and KMP prefix tables
-/

register_result "z-table-to-kmp-prefix-table" where
  title := "Linear-time conversion from a Z-table to the KMP prefix table"
  topic := "string algorithms"
  sources := [
    { paper := BlandKucherovSmyth2013, theorem := "Prefix-table to border-array transformation",
      locator := "IWOCA 2013, published abstract, p. 41" }
  ]
  theorems := [Cslib.Algorithms.WordRAM.ZFunction.toPrefixProgram_executes_zArray]
  scope := "For a word of length n over any alphabet with decidable equality, the standard \
    Word-RAM reads only its zero-based Z-table and writes its KMP table. The library's \
    implementation takes at most 20n + 9 instructions including halt, with 2n + 1 fitting a word."

register_result "kmp-prefix-table-to-z-table" where
  title := "Linear-time conversion from a KMP prefix table to the Z-table"
  topic := "string algorithms"
  sources := [
    { paper := BlandKucherovSmyth2013, theorem := "Border-array to prefix-table transformation",
      locator := "IWOCA 2013, published abstract, p. 41" }
  ]
  theorems := [Cslib.Algorithms.WordRAM.ZFunction.fromPrefixProgram_executes_computePrefix]
  scope := "For a word of length n over any alphabet with decidable equality, the standard \
    Word-RAM reads only its KMP table and writes its zero-based Z-table. The library's \
    implementation takes at most 50n + 19 instructions including halt, with 2n + 1 fitting a word."
