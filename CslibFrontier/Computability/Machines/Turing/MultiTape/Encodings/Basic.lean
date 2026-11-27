/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Encoding

/-!
# Linear word operations for encodings

This entry point re-exports the word operations and their existing plain degree-one certificates.
`ComputableInDegree.of_frame`, `.of_unframe` and `.of_dropFrame` preserve the framed encoding,
including empty words and incomplete frames. The marker, head, tail and emptiness rules use the
same finite-state transducers. All retain linear time and workspace; their output bound is
independent of workspace.
-/
