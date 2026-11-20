/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.QMA
public import CslibFrontier.Computability.Complexity.Classes.Oracle

/-!
# Polynomial time with logarithmically many QMA queries

`PQMAlog` uses one deterministic polynomial-time oracle program and one promise problem
in `PromiseQMA`. A total language extending the promise answers each query. The program must
decide the language within the query budget for every such extension, including when queries
outside the promise change the subsequent queries [Gharibian, Yirka][GharibianYirka2019].

## Main definitions

* `PQMAlog`: polynomial time with logarithmically many adaptive queries to a QMA oracle.
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

/-- The class of decision problems solved in deterministic polynomial time with at most
`c log₂ n + c` queries to a promise problem in QMA, for every completion of its promise. -/
def PQMAlog {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ Q ∈ PromiseQMA (fun _ => 2 / 3) (fun _ => 1 / 3) encBits,
    ∃ c : ℕ, ∃ program : α → WordQueryComp Unit Bool,
      IsOraclePPTOn enc encBool (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ A : Set (List Bool), Q.yes ⊆ A → Q.no ⊆ Aᶜ → ∀ a,
        (a ∈ L ↔ OracleComp.interpret (m := Id) (languageOracle A) (program a) = true) ∧
        (OracleComp.queriesWith (languageOracle A) (program a)).length ≤
          c * Nat.log 2 (enc a).length + c}

end Cslib.Complexity
