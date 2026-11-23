/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.Distributed.ConcurrentObjects.Linearizability

/-!
# Result registry entries for Herlihy–Wing linearizability
-/

register_result "herlihy-wing-linearizability-locality" where
  title := "Locality (compositionality) of Herlihy–Wing linearizability across concurrent objects"
  topic := "distributed computing"
  sources := [
    { paper := HerlihyWing1990, theorem := "Theorem 1",
      locator := "§3.1, printed pp. 470–471" },
    { paper := SelaHerlihyPetrank2021, theorem := "Definition 4.1 and Theorem 5.1",
      locator := "§4, p. 6; §5.2, pp. 7–9 (arXiv:2105.06737v2)" }
  ]
  theorems := [
    Cslib.Distributed.ConcurrentObjects.IsLinearizable.objSubhistory,
    Cslib.Distributed.ConcurrentObjects.isLinearizable_iff_forall_obj
  ]
  scope := "Over finite concurrent invocation/response histories History P Op Resp for arbitrary \
    decidable process types P ([DecidableEq P]) and typed object families Obj ([DecidableEq Obj], \
    Op Resp : Obj → Type*), per-process sequential WellFormed, response-append completion \
    extensions History.IsExtension with maximal completed subhistory History.complete, \
    prefix-closed single-object sequential specifications SeqSpec, and irreflexive real-time \
    precedence History.prec (<_H on OpId P): proves a well-formed multi-object history H is \
    IsLinearizable wrt spec iff every per-object subhistory History.objSubhistory H x is \
    IsLinearizable wrt spec. History.prec H e₀ e₁ sees invocations pending in H, and \
    IsLinearizable enforces it on all operations completed in the extension H' \
    (History.IsCompletedOp H', equivalent to <_{H'} ⊆ <_S via History.prec_append_resp_iff), \
    matching the amended L2 of SelaHerlihyPetrank2021 Definition 4.1 rather than HerlihyWing1990's \
    literal printed L2 on operations completed in H (which fails locality and nonblocking). In the \
    same module, IsLinearizable.isSequentiallyConsistent proves §3.3's (printed p. 472) \
    implication IsLinearizable → IsSequentiallyConsistent, while \
    exists_sequentiallyConsistent_not_linearizable and \
    exists_obj_sequentiallyConsistent_not_global are original atomic-register counterparts \
    witnessing §3.3's single-queue and two-queue separations H_7 and H_8. Source check: \
    outside-fleet agent review (reviewer-codex-edemaine) on PR #7585 at 00965df04d6a: \
    https://github.com/cslib-community/cslib-frontier/pull/7585#pullrequestreview-6014437210."

register_result "herlihy-wing-linearizability-nonblocking" where
  title := "Nonblocking completion property of linearizability for pending total operations"
  topic := "distributed computing"
  sources := [
    { paper := HerlihyWing1990, theorem := "Theorem 2",
      locator := "§3.2, printed pp. 471–472" },
    { paper := SelaHerlihyPetrank2021, theorem := "Definition 4.1 and Theorem 5.2",
      locator := "§4, p. 6; §5.3, p. 9 (arXiv:2105.06737v2)" }
  ]
  theorems := [
    Cslib.Distributed.ConcurrentObjects.exists_linearizable_append_resp_of_total
  ]
  scope := "For any linearizable history H (IsLinearizable spec H over [DecidableEq P] \
    [DecidableEq Obj], where History.prec H e₀ e₁ sees invocations pending in H and IsLinearizable \
    applies it to operations completed in the extension H' via History.prec_append_resp_iff, \
    matching SelaHerlihyPetrank2021 Definition 4.1 rather than the literal printed L2 on \
    operations complete in H), if process p has an uncompleted pending invocation Event.inv p x op \
    (History.procSubhistory H p = cs.flatMap OpCall.toEvents ++ [.inv p x op]) of an operation \
    op satisfying SeqSpec.IsTotalOp (every even-length history in (spec x).allowed extends by \
    [.inv p x op, .resp p x res] for some res : Resp x), there exists res : Resp x such that \
    H ++ [.resp p x res] remains IsLinearizable wrt spec (asserting existence of a legal appended \
    response without an implementation step or progress bound). Source check: outside-fleet agent \
    review (reviewer-codex-edemaine) on PR #7585 at 00965df04d6a: \
    https://github.com/cslib-community/cslib-frontier/pull/7585#pullrequestreview-6014437210."
