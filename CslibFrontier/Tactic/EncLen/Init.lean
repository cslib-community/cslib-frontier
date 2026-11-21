/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Encoded-length normalization attribute

The opt-in `enc_len` simp set expands encodings into their fields for the `enc_len` tactic.
The standard rules are supplied by `CslibFrontier.Tactic.EncLen`; clients can add local or
namespace-scoped equations for their encodings without changing the ordinary simplifier.
Component-to-container inequalities belong to the separate `enc_component` simp set.
-/

public meta section

/-- Equations that expose encoded lengths to linear arithmetic, used only by `enc_len`. -/
register_simp_attr enc_len

end
