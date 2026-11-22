/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Distributed.VectorClock.Basic
import CslibFrontier.Computability.Distributed.VectorClock.Clocks

/-!
# Vector clock and Lamport logical clock results
-/

register_result "lamport-scalar-logical-clocks" where
  title := "Lamport scalar logical clocks satisfy the Clock Condition and extend happens-before \
    to a strict total order"
  topic := "distributed computing"
  sources := [
    { paper := Lamport1978,
      theorem := "Clock Condition (rules IR1–IR2) and tie-breaking total ordering ⇒",
      locator := "\"The Partial Ordering\", \"Logical Clocks\", and \"Ordering the Events \
        Totally\", printed pp. 558–561" }
  ]
  theorems := [
    Cslib.Distributed.VectorClock.Execution.lamportClock_strictMono,
    Cslib.Distributed.VectorClock.Execution.happensBefore_imp_lamportTotalOrder
  ]
  scope := "Operational finite causally well-formed unicast message-passing executions \
    Execution P over any process type P (Step.internal, Step.send, Step.recv with earlier send \
    index recv_valid and at-most-once delivery recv_injective; Footnote 2's multi-recipient \
    single-event sends are not combined into one Step). Instantiates rules IR1 and IR2(a),(b) \
    with unit increments (L p + 1 on internal/send steps and max (L p) L_msg + 1 on receive \
    steps, starting from 0), proving StrictMono E.lamportClock with respect to HappensBefore \
    (and Monotone with respect to HappensBeforeLe) over [DecidableEq P], together with \
    IsStrictTotalOrder E.Event E.lamportTotalOrder and linear extension of HappensBefore over \
    [LinearOrder P]. Companion not_exists_1d_characterization is an original two-process \
    communication-free counterexample witnessing p. 560's remark that the converse of the Clock \
    Condition fails across concurrent events; the distributed mutual exclusion protocol \
    (pp. 561–562) and physical clock synchronization bound (pp. 562–565) are not formalized \
    here. Source check: outside-fleet agent review (reviewer-codex-edemaine) on PR #7258 at \
    3f79747f5389: \
    https://github.com/cslib-community/cslib-frontier/pull/7258#pullrequestreview-6013805833."

register_result "mattern-consistent-cut-sublattice" where
  title := "Consistent cuts of distributed executions are closed under union and intersection \
    and exclude orphan receives"
  topic := "distributed computing"
  sources := [
    { paper := Mattern1989,
      theorem := "Definition 3 and Theorem 2",
      locator := "§3 (\"Consistent cuts\", Definition 3 and Theorem 2), author-edited reprint \
        p. 123 (North-Holland book pp. 215–226)" }
  ]
  theorems := [
    Cslib.Distributed.VectorClock.Execution.IsConsistentCut.union,
    Cslib.Distributed.VectorClock.Execution.IsConsistentCut.inter,
    Cslib.Distributed.VectorClock.Execution.IsConsistentCut.send_mem_of_recv_mem
  ]
  scope := "Downward-closed finite event subsets IsConsistentCut E (C : Finset E.Event) over \
    finite causally well-formed unicast executions Execution P on any process type P (without \
    DecidableEq P), proving closure under Finset union and intersection (alongside ∅ and \
    Finset.univ) and that every receive event in C has its matching earlier send event in C. \
    Checked against Mattern's author-edited reprint PDF (SHA-256 \
    64830b6a039f0e1840e06d1e745b8abe00d2e224b17721e2fff37731116d3bae); the North-Holland book \
    pagination (pp. 215–226) was not separately inspected. Source check: outside-fleet agent \
    review (reviewer-codex-edemaine) on PR #7258 at 3f79747f5389: \
    https://github.com/cslib-community/cslib-frontier/pull/7258#pullrequestreview-6013805833."

register_result "mattern-vector-clocks-causality" where
  title := "Vector clocks induce an order-isomorphism with happens-before and characterize \
    causality by single-coordinate comparison of given timestamps"
  topic := "distributed computing"
  sources := [
    { paper := Mattern1989,
      theorem := "Theorem 10 and Theorem 11",
      locator := "§7 (\"Vector time\"), pp. 126–127, and §8 (\"The structure of vector time\", \
        Theorems 10–11), pp. 127–128 (author-edited reprint PDF)" }
  ]
  theorems := [
    Cslib.Distributed.VectorClock.Execution.happensBeforeLe_iff_vc_le,
    Cslib.Distributed.VectorClock.Execution.happensBefore_iff_vc_lt,
    Cslib.Distributed.VectorClock.Execution.happensBeforeLe_iff_coord_le,
    Cslib.Distributed.VectorClock.Execution.happensBefore_iff_coord_le,
    Cslib.Distributed.VectorClock.Execution.concurrent_iff_vc_incomparable
  ]
  scope := "Operational finite causally well-formed unicast executions Execution P over any \
    [DecidableEq P], where Execution.vc updates VectorClock P := P → ℕ by componentwise sup \
    with the received message timestamp (if any) and + 1 on the executing process's coordinate \
    (yielding the identical vector on every valid execution as ticking before sup by Theorem 5, \
    p. 127, and contrasting with Fidge 1988 Rule RA4's sender-entry increment). Proves exact \
    product-order characterization of HappensBeforeLe and HappensBefore (Theorem 10), \
    single-coordinate comparison of given timestamps at e₁.actor (and for e₁ ≠ e₂ on strict \
    HappensBefore, Theorem 11), and equivalence of irreflexive event concurrency \
    Execution.Concurrent with vector coordinatewise incomparability (agreeing on distinct events \
    with Definition 4's reflexive vector concurrency by vc_injective). Checked against Mattern's \
    author-edited reprint PDF (SHA-256 \
    64830b6a039f0e1840e06d1e745b8abe00d2e224b17721e2fff37731116d3bae). Source check: \
    outside-fleet agent review (reviewer-codex-edemaine) on PR #7258 at 3f79747f5389: \
    https://github.com/cslib-community/cslib-frontier/pull/7258#pullrequestreview-6013805833."

register_result "mattern-consistent-cut-frontier-criterion" where
  title := "Consistent-cut characterization via owner-maximized frontier vector timestamps"
  topic := "distributed computing"
  sources := [
    { paper := Mattern1989,
      theorem := "Definition 5 and Theorem 6",
      locator := "§7 (\"Vector time\", Definition 5 and Theorem 6), author-edited reprint p. 127 \
        (North-Holland book pp. 215–226)" }
  ]
  theorems := [
    Cslib.Distributed.VectorClock.Execution.isConsistentCut_cutOfFrontier_iff
  ]
  scope := "For any finite causally well-formed unicast execution E : Execution P over \
    [DecidableEq P] and per-process frontier frontier : P → E.Event satisfying \
    ∀ p, (frontier p).actor = p (realizing Definition 5's assumption that each process has at \
    least one event in the cut), proves that E.cutOfFrontier frontier is a consistent cut iff \
    ∀ p q : P, E.vc (frontier q) p ≤ E.vc (frontier p) p (equivalent to \
    sup_q C(c_q)[p] = C(c_p)[p] for every p). Checked against Mattern's author-edited reprint \
    PDF (SHA-256 64830b6a039f0e1840e06d1e745b8abe00d2e224b17721e2fff37731116d3bae); the \
    non-FIFO snapshot algorithm (§11, pp. 129–131) is not formalized here. Source check: \
    outside-fleet agent review (reviewer-codex-edemaine) on PR #7258 at 3f79747f5389: \
    https://github.com/cslib-community/cslib-frontier/pull/7258#pullrequestreview-6013805833."
