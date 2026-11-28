/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Security

/-!
# Statement maps for interactive verifiers

Pullback of a public-coin interactive verifier `V` along a statement map `g : StmtIn' → StmtIn`.
The derived verifier `V.comap g` runs the challenge samplers of `V` unchanged and applies `V.decide`
to `g x`.

## Main definitions

* `Cslib.Interactive.Verifier.comap`: run an interactive verifier through a statement map `g`.

## Main results

* `Cslib.Interactive.Verifier.Sound.comap`: soundness transfers with the same error whenever false
  statements map to false statements (`∀ x, g x ∈ langIn → x ∈ langIn'`).
* `Cslib.Interactive.Verifier.KnowledgeSound.comap`: straight-line knowledge soundness transfers
  for the relation "`w` is a witness of `g x`", running `E` at `g x` with no hypothesis on `g`.
-/

public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV} {s : Spec}
  {StmtIn StmtIn' StmtOut : Type}

/-- Run a verifier for statements `StmtIn` on statements `StmtIn'`, through a statement map `g`:
same challenge samplers, and the decision of `V` at `g x`. -/
@[expose] def Verifier.comap (V : Verifier oV s StmtIn StmtOut) (g : StmtIn' → StmtIn) :
    Verifier oV s StmtIn' StmtOut where
  samplers := V.samplers
  decide x := V.decide (g x)

/-- Soundness transfers along a statement map that sends false statements to false statements,
with the same error. -/
theorem Verifier.Sound.comap {W : World oP oV} {V : Verifier oV s StmtIn StmtOut}
    {langIn : Set StmtIn} {langOut : Set StmtOut} {ε : ℝ≥0∞} (h : V.Sound W langIn langOut ε)
    {g : StmtIn' → StmtIn} {langIn' : Set StmtIn'} (hg : ∀ x, g x ∈ langIn → x ∈ langIn') :
    (V.comap g).Sound W langIn' langOut ε :=
  fun x hx α P => h (g x) (fun hgx => hx (hg x hgx)) α P

/-- Knowledge soundness transfers along a statement map for the relation "`w` is a witness of
`g x`", with the extractor of `V` run on `g x` and the same error. No condition on `g`. -/
theorem Verifier.KnowledgeSound.comap {WitIn WitOut : Type}
    {V : Verifier OracleSpec.empty s StmtIn StmtOut} {relIn : StmtIn → WitIn → Prop}
    {relOut : StmtOut → WitOut → Prop} {E : StmtIn → Transcript s → WitOut → WitIn} {ε : ℝ≥0∞}
    (h : V.KnowledgeSound relIn relOut E ε) (g : StmtIn' → StmtIn) :
    (V.comap g).KnowledgeSound (fun x w => relIn (g x) w) relOut (fun x => E (g x)) ε :=
  fun x P => h (g x) P

end Cslib.Interactive
