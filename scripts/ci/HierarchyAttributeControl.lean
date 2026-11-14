-- Temporary hosted instrumentation for #4073. DO NOT MERGE.
module

@[expose] public def hierarchyExposedControl (n : Nat) : Nat := n + 1
@[no_expose] public def hierarchyHiddenControl (n : Nat) : Nat := n + 1
