/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Succinct dictionary parameter simplification

The `succinct_param_simps` set substitutes the precomputed layout fields of `mkDictParams`
and `mkCompParams` in fixed-size and resizable dictionary proofs.
-/

public meta section

/-- Rewrite projections from constructed succinct dictionary parameter blocks to their layout
values. -/
register_simp_attr succinct_param_simps

end
