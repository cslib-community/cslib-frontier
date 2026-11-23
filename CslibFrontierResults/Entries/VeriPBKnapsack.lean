/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Logics.Propositional.PseudoBoolean.Knapsack

/-!
# Collected results: certified 0–1 knapsack by VeriPB proofs of a dynamic program
-/

register_result "demirovic-et-al-certified-knapsack" where
  title := "A VeriPB proof of BOUNDS lb : q lb accepted for the 0–1 knapsack encoding certifies \
    the optimum -lb"
  topic := "proof logging"
  sources := [
    { paper := DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024,
      theorem := "§3.1, knapsack encoding (equations (1)–(3)) and proof-logging method \
        (equations (8)–(23), Algorithm 1); the paper states no theorem about it",
      locator := "LIPIcs 307, §3.1, pp. 9:5–9:9" }
  ]
  theorems := [
    Cslib.Logic.PL.VeriPB.Knapsack.holds_capacity_iff,
    Cslib.Logic.PL.VeriPB.Knapsack.eval_objective,
    Cslib.Logic.PL.VeriPB.Knapsack.selection_surjective,
    Cslib.Logic.PL.VeriPB.Knapsack.bounds_of_checkRed,
    Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed,
    Cslib.Logic.PL.VeriPB.Knapsack.isGreatest_of_checkRed_certify
  ]
  scope := "For every n, weights and profits w p : Fin n → ℕ and capacity B: an assignment \
    satisfies the capacity constraint exactly when its selection fits, and its objective value is \
    the negated profit (the paper's equations (1)–(3), with ∑ wᵢ xᵢ ≤ B written in normal form \
    ∑ wᵢ ¬xᵢ ≥ ∑ wᵢ - B). For every proof P accepted by the verified checker checkRed with the \
    conclusion BOUNDS lb : q ub, every fitting Finset of items has profit at most -lb and some \
    fitting set has profit at least -ub; for lb = ub, -lb is the largest profit (IsGreatest). The \
    paper gives a method, not a theorem: these statements are the guarantee its proofs carry \
    when checked by this library's checker, and they hold for any proof, not only those of the \
    dynamic program certify. That certify's proofs are always accepted is not proved; it is \
    checked per run (decide +kernel on a six-item instance, compiled runs up to 40 items, \
    VeriPB 3.0.2 and CakePB on printed texts). Dominated states are not created: the transition \
    goes to the dominating state, a variant the paper allows, instead of equation (21)."
