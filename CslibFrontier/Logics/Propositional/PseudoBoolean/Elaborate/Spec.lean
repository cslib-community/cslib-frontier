/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Elaborate.Syntax

/-!
# A declarative semantics of the clausal and `pol` fragment of the augmented format

When is a proof in the augmented format of VeriPB [Bogaerts, Gocht, McCreesh and
Nordström][BogaertsGochtMcCreeshNordstrom2023], version 3.0, valid? This file answers for the
fragment that CaDiCaL's `--veripb` modes write, with a relation
`Cslib.Logic.PL.VeriPB.Elab.AugValid`: the proof `P` is valid for the formula `F` with the claim
`c`. The semantics is stated on the abstract syntax of the elaborator's parser
(`Cslib.Logic.PL.VeriPB.Elab.AStep`), with an augmented database of its own, and does not mention
the elaborator. Section numbers are those of the VeriPB/CakePB documentation, 22 June 2026
edition.

**The fragment.**
* `f N;` in the header (§4.1): `N` is the number of constraints of the formula. A later `f N;` is
  a rule without effect (`Cslib.Logic.PL.VeriPB.Elab.AStep.noop`), as in the elaborator.
* `pol` (§5.2.1) with the operations of the kernel format: constraint references, literal axioms,
  addition, multiplication and division by a positive number, saturation and weakening. The
  derived constraint is the one the kernel's rules give
  (`Cslib.Logic.PL.VeriPB.polEval`).
* `rup C;` (§5.2.1): `C` follows from the current database by reverse unit propagation, that is,
  some sequence of unit propagations of the database and of `¬C` reaches a conflict
  (`Cslib.Logic.PL.VeriPB.rup` along some list of hints). `rup C : hints;` with the augmented
  hints, read as a set: the propagated constraints are among the hints, every hint naming a
  constraint of the database. The negation `~` may always be propagated.
* `e C : j;` and `e C;` (§5.11.1): the constraint `j`, or some constraint of the database, is `C`
  after normalization, up to the order of terms, as the kernel's `e` checks it
  (`Cslib.Logic.PL.VeriPB.TopStep.econstr`). It derives nothing.
* `ea C : j;` and `ea C;`: as `e`, and the constraint found is added again under the next number.
  VeriPB 2 had this rule; VeriPB 3.0 dropped it.
* `del id ids;` (§5.7.2): distinct constraints of the database, derived or core, are deleted. The
  typed deletions `deld ids;` and `delc ids;` (§5.7.1) are those of the kernel: `deld` of derived
  constraints, `delc` the unchecked deletion of core constraints.
* `core id ids;` (§5.1): constraints of the database, at least one, join the core set.
* `output NONE;` (§4.2), and the conclusions `UNSAT [: j]` (the constraint `j`, or some constraint
  of the database, is a contradiction), `SAT : ρ` (`ρ` solves the formula) and `NONE` (§4.3).

References are absolute or relative (`-k`, §5); labels, the deletion by specification
`del spec` (VeriPB 2's `del find`) and the rest of the format are outside the fragment, and a
proof using them has no derivation here.

**Soundness from the kernel's.** A derivation of `AugValid` is simulated step by step by the
kernel checker `Cslib.Logic.PL.VeriPB.checkRed`, with the same constraint numbers
(`Cslib.Logic.PL.VeriPB.Elab.exists_checkRed_of_augValid`). So the guarantees of the kernel carry
over: a valid proof of `UNSAT` means the formula has no 0/1 solution
(`Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_of_augValid`), and one of `SAT : ρ` means `ρ`
solves it (`Cslib.Logic.PL.VeriPB.Elab.holds_of_augValid_sat`).

## Main definitions

* `Cslib.Logic.PL.VeriPB.Elab.AProof`: a parsed augmented proof.
* `Cslib.Logic.PL.VeriPB.Elab.Claim`: what a conclusion claims, without its constraint numbers.
* `Cslib.Logic.PL.VeriPB.Elab.AState`, `Cslib.Logic.PL.VeriPB.Elab.AugStep`,
  `Cslib.Logic.PL.VeriPB.Elab.AugRun`: the augmented database and the rules of the fragment.
* `Cslib.Logic.PL.VeriPB.Elab.AugValid`: the validity of a proof of the fragment.

## Main results

* `Cslib.Logic.PL.VeriPB.Elab.exists_checkRed_of_augValid`: a valid proof has a kernel proof with
  the same claim, accepted by the kernel checker.
* `Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_of_augValid`,
  `Cslib.Logic.PL.VeriPB.Elab.not_satisfiable_cnf_of_augValid`,
  `Cslib.Logic.PL.VeriPB.Elab.holds_of_augValid_sat`: soundness of the claims.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
-/

@[expose] public section

namespace Cslib.Logic.PL.VeriPB.Elab

open PBConstr

/-- A parsed proof in the augmented format: the number `N` of its header `f N;`, if given, its
rules, its output section (`none` for `NONE`, else the guarantee and `FILE` (`true`) or
`IMPLICIT`) and its conclusion. -/
structure AProof where
  /-- The number of constraints of the header `f N;`, if given. -/
  header : Option ℕ
  /-- The rules. -/
  steps : List AStep
  /-- The output section. -/
  output : Option (Guarantee × Bool)
  /-- The conclusion. -/
  concl : AConclusion

/-- What a conclusion claims: the conclusion without the constraint numbers that certify it. -/
inductive Claim where
  /-- `UNSAT`. -/
  | unsat
  /-- `SAT [: ρ]`. -/
  | sat (asg : Option (List (Literal ℕ)))
  /-- `BOUNDS lb ub [: ρ]`. -/
  | bounds (lb : Option ℤ) (ub : Option ℤ) (asg : Option (List (Literal ℕ)))
  /-- `NONE`. -/
  | noClaim
  /-- `ENUMERATION_PARTIAL n`. -/
  | enumPartial (n : ℕ)
  /-- `ENUMERATION_COMPLETE n`. -/
  | enumComplete (n : ℕ)
  deriving DecidableEq, Repr

/-- The claim of a kernel conclusion. -/
def _root_.Cslib.Logic.PL.VeriPB.Conclusion.claim : Conclusion → Claim
  | .unsat _ => .unsat
  | .sat asg => .sat asg
  | .bounds lb _ ub asg => .bounds lb ub asg
  | .noClaim => .noClaim
  | .enumPartial n => .enumPartial n
  | .enumComplete n _ => .enumComplete n

/-! ### The augmented database -/

/-- The state of an augmented proof: the database of live constraints with their numbers, latest
first, the core set among them, the next number, and the objective and preserved set. -/
structure AState where
  /-- The live constraints, by number, latest first. -/
  db : List (ℕ × PBConstr)
  /-- The core constraints, by number. -/
  core : List (ℕ × PBConstr)
  /-- The next constraint number. -/
  next : ℕ
  /-- The objective. -/
  obj : Option Objective
  /-- The preserved set. -/
  pres : Option (List ℕ)

namespace AState

/-- The initial state for the formula `F`: its constraints, numbered from `1` and normalized, form
the database and the core set. -/
def init (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) : AState :=
  ⟨initDb F, initDb F, F.length + 1, obj, pres⟩

/-- The number a reference names: `-k` names the `k`-th most recent number (§5). Labels are outside
the fragment. -/
def resolve (A : AState) : Ref → Option ℕ
  | .abs n => some n
  | .rel k => if k ≤ A.next then some (A.next - k) else none
  | .label _ => none

/-- `j` is the constraint named by an optional reference: the one named, if given, else any. -/
def Picks (A : AState) : Option Ref → ℕ → Prop
  | some r, j => A.resolve r = some j
  | none, _ => True

/-- Add a derived constraint under the next number. -/
def push (A : AState) (c : PBConstr) : AState :=
  { A with db := (A.next, c) :: A.db, next := A.next + 1 }

/-- Delete the constraints with the numbers `ids` from the database and the core set. -/
def remove (A : AState) (ids : List ℕ) : AState :=
  { A with db := A.db.filter (fun e => !ids.contains e.1),
           core := A.core.filter (fun e => !ids.contains e.1) }

/-- Move the constraints with the numbers `ids` to the core set, as the kernel's `core id` does. -/
def promote (A : AState) (ids : List ℕ) : AState :=
  { A with core := A.db.filter (fun e => ids.contains e.1 && !A.core.contains e) ++ A.core }

/-- The constraint `n` is in the database. -/
def Live (A : AState) (n : ℕ) : Prop := (lookup A.db n).isSome

/-- The constraint `n` is a core constraint. -/
def IsCore (A : AState) (n : ℕ) : Prop := ∃ e ∈ A.core, e.1 = n

/-- A kernel hint may be propagated for a `rup` step with the augmented hints `hs`: the negation
always, and a constraint if there are no hints or if it is among them. -/
def Allows (A : AState) : Option (List AHint) → Hint → Prop
  | _, .neg => True
  | none, .id _ => True
  | some hs, .id n => ∃ r, AHint.ref r ∈ hs ∧ A.resolve r = some n

/-- Every hint of a `rup` step names a constraint of the database. -/
def HintsLive (A : AState) : Option (List AHint) → Prop
  | none => True
  | some hs => ∀ r, AHint.ref r ∈ hs → ∃ n, A.resolve r = some n ∧ A.Live n

end AState

/-- The kernel operation of a `pol` operation of the fragment, its references resolved in the
state `A`: the operations `c`, `n`, `m` and `-` and the multiplication and division by `0` are
outside the fragment. -/
def AOp.toKernel (A : AState) : AOp → Option PolOp
  | .ref r => (A.resolve r).map .id
  | .lit l => some (.lit l)
  | .add => some .add
  | .mul (k + 1) => some (.mul (k + 1))
  | .div (k + 1) => some (.div (k + 1))
  | .sat => some .sat
  | .weaken v => some (.weaken v)
  | _ => none

/-! ### The rules -/

/-- **A rule of the fragment** takes the state `A` to the state `B`. -/
inductive AugStep : AState → AStep → AState → Prop where
  /-- `pol ops;`: the operations evaluate to one constraint, which is added. -/
  | pol {A : AState} {ops : List AOp} {kops : List PolOp} {c : PBConstr}
      (hops : ops.mapM (AOp.toKernel A) = some kops) (hc : polEval A.db kops [] = some [c]) :
      AugStep A (.pol ops) (A.push c)
  /-- `rup C [: hints];`: some list of allowed hints propagates `¬C` and the database to a
  conflict; the normal form of `C` is added. -/
  | rup {A : AState} {c : PBConstr} {hs : Option (List AHint)} (kh : List Hint)
      (hlive : A.HintsLive hs) (hk : ∀ h ∈ kh, A.Allows hs h) (hr : rup A.db c kh = true) :
      AugStep A (.rup c hs) (A.push c.normalize)
  /-- `e C [: j];`: the constraint `j` is `C` after normalization, up to the order of terms. -/
  | equal {A : AState} {c d : PBConstr} {r : Option Ref} {j : ℕ} (hj : A.Picks r j)
      (hd : lookup A.db j = some d) (he : sameUpToOrder d.normalize c.normalize = true) :
      AugStep A (.equal c r) A
  /-- `ea C [: j];`: as `e`, and the constraint `j` is added again. -/
  | equalAdd {A : AState} {c d : PBConstr} {r : Option Ref} {j : ℕ} (hj : A.Picks r j)
      (hd : lookup A.db j = some d) (he : sameUpToOrder d.normalize c.normalize = true) :
      AugStep A (.equalAdd c r) (A.push d)
  /-- `del id ids;`: distinct constraints of the database are deleted. -/
  | delId {A : AState} {rs : List Ref} {ids : List ℕ} (hids : rs.mapM A.resolve = some ids)
      (hnd : ids.Nodup) (hl : ∀ i ∈ ids, A.Live i) : AugStep A (.delId rs) (A.remove ids)
  /-- `deld ids;`: distinct derived constraints of the database are deleted. -/
  | deld {A : AState} {rs : List Ref} {ids : List ℕ} (hids : rs.mapM A.resolve = some ids)
      (hnd : ids.Nodup) (hl : ∀ i ∈ ids, A.Live i) (hc : ∀ i ∈ ids, ¬ A.IsCore i) :
      AugStep A (.deld rs) (A.remove ids)
  /-- `delc ids;`: distinct core constraints of the database are deleted, unchecked. -/
  | delc {A : AState} {rs : List Ref} {ids : List ℕ} (hids : rs.mapM A.resolve = some ids)
      (hnd : ids.Nodup) (hl : ∀ i ∈ ids, A.Live i) (hc : ∀ i ∈ ids, A.IsCore i) :
      AugStep A (.delc rs) (A.remove ids)
  /-- `core id ids;`: constraints of the database, at least one, join the core set. -/
  | coreId {A : AState} {rs : List Ref} {ids : List ℕ} (hids : rs.mapM A.resolve = some ids)
      (hne : ids ≠ []) (hl : ∀ i ∈ ids, A.Live i) : AugStep A (.coreId rs) (A.promote ids)
  /-- A rule without effect, such as a later `f N;`. -/
  | noop {A : AState} : AugStep A .noop A

/-- **The rules of the fragment, in order**, take the state `A` to the state `B`. -/
inductive AugRun : AState → List AStep → AState → Prop where
  /-- No rule. -/
  | nil {A : AState} : AugRun A [] A
  /-- A rule, then the others. -/
  | cons {A B C : AState} {s : AStep} {ss : List AStep} (h : AugStep A s B) (t : AugRun B ss C) :
      AugRun A (s :: ss) C

/-- **The conclusion of the fragment** holds in the final state `A`, for the formula `F`, with the
claim `c`. -/
inductive ConclValid (F : List PBConstr) (A : AState) : AConclusion → Claim → Prop where
  /-- `UNSAT [: j]`: the constraint `j` is a contradiction. -/
  | unsat {q : Option Ref} {j : ℕ} (hj : A.Picks q j) (hc : namesContra A.db j = true) :
      ConclValid F A (.unsat q) .unsat
  /-- `SAT : ρ`: the assignment `ρ` solves the formula. -/
  | sat {ρ : List (Literal ℕ)} (h : solves ρ (F.map normalize) = true) :
      ConclValid F A (.sat (some ρ)) (.sat (some ρ))
  /-- `NONE`. -/
  | noClaim : ConclValid F A .noClaim .noClaim

/-- **A valid proof of the fragment**, for the formula `F`, the objective `obj` and the preserved
set `pres`, with the claim `c`: its header, if any, gives the number of constraints of `F`, its
output section is `NONE`, its rules run from the formula, and its conclusion holds with the claim
`c` at the end. -/
def AugValid (F : List PBConstr) (obj : Option Objective) (pres : Option (List ℕ)) (P : AProof)
    (c : Claim) : Prop :=
  P.header.all (· == F.length) = true ∧ P.output = none ∧
    ∃ A, AugRun (AState.init F obj pres) P.steps A ∧ ConclValid F A P.concl c

/-! ### Soundness, from the kernel's -/

/-- The kernel state `s` simulates the augmented state `A`: the same database, core set and next
number, no logged solution or `obji` step, strengthening-to-core mode off and no order loaded. -/
private structure Sim (A : AState) (s : State) : Prop where
  db : s.db = A.db
  core : s.core = A.core
  next : s.next = A.next
  dbound : s.dbound = none
  tcb : s.tcb = false
  order : s.order = none

private theorem all_lookup_isSome {db : List (ℕ × PBConstr)} {ids : List ℕ}
    (h : ∀ i ∈ ids, (lookup db i).isSome) : ids.all (fun i => (lookup db i).isSome) = true :=
  List.all_eq_true.2 h

/-- **One rule of the fragment is simulated by kernel steps** with the same numbers. -/
private theorem exists_runTop_of_augStep {F : List PBConstr} {obj : Option Objective}
    {A B : AState} {st : AStep} (h : AugStep A st B) {s : State} (hs : Sim A s) :
    ∃ ts s', runTop F obj s ts = some s' ∧ Sim B s' := by
  obtain ⟨hdb, hcore, hnext, hdbound, htcb, horder⟩ := hs
  cases h with
  | @pol ops kops c hops hc =>
    refine ⟨[.step (.pol kops)], { s with db := (s.next, c) :: s.db, next := s.next + 1 }, ?_, ?_⟩
    · rw [runTop_cons, stepTop_step_of_ne_del _ _ _ (by simp)]
      simp [runStep, hdb, hc, runTop_nil]
    · exact ⟨by simp [AState.push, hdb, hnext], hcore, by simp [AState.push, hnext], hdbound,
        htcb, horder⟩
  | @rup c hs kh _ _ hr =>
    refine ⟨[.step (.rup c kh)],
      { s with db := (s.next, c.normalize) :: s.db, next := s.next + 1 }, ?_, ?_⟩
    · rw [runTop_cons, stepTop_step_of_ne_del _ _ _ (by simp)]
      simp [runStep, hdb, hr, runTop_nil]
    · exact ⟨by simp [AState.push, hdb, hnext], hcore, by simp [AState.push, hnext], hdbound,
        htcb, horder⟩
  | equal => exact ⟨[], s, runTop_nil _ _ _, hdb, hcore, hnext, hdbound, htcb, horder⟩
  | @equalAdd c d r j _ hd _ =>
    refine ⟨[.step (.pol [.id j])], { s with db := (s.next, d) :: s.db, next := s.next + 1 }, ?_,
      ?_⟩
    · rw [runTop_cons, stepTop_step_of_ne_del _ _ _ (by simp)]
      simp [runStep, polEval, hdb, hd, runTop_nil]
    · exact ⟨by simp [AState.push, hdb, hnext], hcore, by simp [AState.push, hnext], hdbound,
        htcb, horder⟩
  | @delId rs ids _ hnd hl =>
    refine ⟨[.step (.del ids)],
      { s with db := s.db.filter (fun e => !ids.contains e.1), next := s.next,
               core := s.core.filter (fun e => !ids.contains e.1),
               chk := s.chk && !s.core.any (fun e => ids.contains e.1) }, ?_, ?_⟩
    · rw [runTop_cons, stepTop_step_del]
      simp [runStep, hdb, hnd, all_lookup_isSome hl, htcb, horder, runTop_nil]
    · exact ⟨by simp [AState.remove, hdb], by simp [AState.remove, hcore], hnext, hdbound, htcb,
        horder⟩
  | @deld rs ids _ hnd hl hc =>
    have hnc : ∀ (a : ℕ) (b : PBConstr), (a, b) ∈ s.core → a ∉ ids :=
      fun a b hab hi => hc a hi ⟨(a, b), hcore ▸ hab, rfl⟩
    refine ⟨[.deld ids], { s with db := s.db.filter fun e => !ids.contains e.1 }, ?_, ?_⟩
    · rw [runTop_cons, stepTop_deld]
      simpa [hdb, hnd, all_lookup_isSome hl, runTop_nil] using hnc
    · refine ⟨by simp [AState.remove, hdb], ?_, hnext, hdbound, htcb, horder⟩
      simp only [AState.remove, ← hcore]
      exact (List.filter_eq_self.2 fun e he => by simpa using hnc e.1 e.2 he).symm
  | @delc rs ids _ hnd _ hc =>
    have hall : ids.all (fun i => s.core.any (·.1 == i)) = true := by
      refine List.all_eq_true.2 fun i hi => ?_
      obtain ⟨e, he, rfl⟩ := hc i hi
      exact List.any_eq_true.2 ⟨e, hcore ▸ he, beq_self_eq_true _⟩
    refine ⟨[.delc ids],
      { s with db := s.db.filter (fun e => !ids.contains e.1),
               core := s.core.filter (fun e => !ids.contains e.1), chk := false }, ?_, ?_⟩
    · rw [runTop_cons, stepTop_delc]
      simp [hnd, hall, htcb, horder, runTop_nil]
    · exact ⟨by simp [AState.remove, hdb], by simp [AState.remove, hcore], hnext, hdbound, htcb,
        horder⟩
  | @coreId rs ids _ hne hl =>
    refine ⟨[.core ids],
      { s with core := s.db.filter (fun e => ids.contains e.1 && !s.core.contains e) ++ s.core },
      ?_, ?_⟩
    · rw [runTop_cons, stepTop_core]
      simp [hdb, all_lookup_isSome hl, hne, runTop_nil]
    · exact ⟨hdb, by simp [AState.promote, hdb, hcore], hnext, hdbound, htcb, horder⟩
  | noop => exact ⟨[], s, runTop_nil _ _ _, hdb, hcore, hnext, hdbound, htcb, horder⟩

/-- **The rules of the fragment are simulated by kernel steps** with the same numbers. -/
private theorem exists_runTop_of_augRun {F : List PBConstr} {obj : Option Objective}
    {A B : AState} {ss : List AStep} (h : AugRun A ss B) :
    ∀ {s : State}, Sim A s → ∃ ts s', runTop F obj s ts = some s' ∧ Sim B s' := by
  induction h with
  | nil => exact fun hs => ⟨[], _, runTop_nil _ _ _, hs⟩
  | cons h _ ih =>
    intro s hs
    obtain ⟨ts, s', h₁, hs'⟩ := exists_runTop_of_augStep (F := F) (obj := obj) h hs
    obtain ⟨us, s'', h₂, hs''⟩ := ih hs'
    exact ⟨ts ++ us, s'', by rw [runTop_append, h₁, Option.bind_some, h₂], hs''⟩

/-- **A valid proof of the fragment gives an accepted kernel proof** with the same claim: the
kernel steps simulating its rules, with the same constraint numbers. -/
theorem exists_checkRed_of_augValid {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {P : AProof} {c : Claim} (h : AugValid F obj pres P c) :
    ∃ K : RedProof, checkRed F obj K pres = true ∧ K.conclusion.claim = c := by
  obtain ⟨_, steps, _, concl⟩ := P
  obtain ⟨-, -, A, hrun, hc⟩ := h
  have hinit : Sim (AState.init F obj pres) (State.init F obj pres) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨ts, s, hts, hs⟩ := exists_runTop_of_augRun (F := F) (obj := obj) hrun hinit
  cases hc with
  | @unsat q j _ hj =>
    refine ⟨⟨ts, .unsat j⟩, ?_, rfl⟩
    simp [checkRed, hts, checkConclusion, hs.dbound, hs.db, hj]
  | @sat ρ hρ =>
    refine ⟨⟨ts, .sat (some ρ)⟩, ?_, rfl⟩
    simp [checkRed, hts, checkConclusion, hρ]
  | noClaim =>
    refine ⟨⟨ts, .noClaim⟩, ?_, rfl⟩
    simp [checkRed, hts, checkConclusion]

/-- **Soundness of `UNSAT`**: a valid proof of `UNSAT` of the fragment means that the formula has
no 0/1 solution. -/
theorem not_satisfiable_of_augValid {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {P : AProof} (h : AugValid F obj pres P .unsat) (σ : ℕ → Bool) :
    ¬ ∀ c ∈ F, c.Holds σ := by
  obtain ⟨K, hK, hc⟩ := exists_checkRed_of_augValid h
  cases hK' : K.conclusion with
  | unsat q => exact not_satisfiable_of_checkRed hK hK' σ
  | _ => simp [hK', Conclusion.claim] at hc

/-- **Soundness of `UNSAT` for a CNF formula**, its clauses read as constraints. -/
theorem not_satisfiable_cnf_of_augValid {φ : CNF ℕ} {obj : Option Objective}
    {pres : Option (List ℕ)} {P : AProof} (h : AugValid (φ.map Clause.toPB) obj pres P .unsat) :
    ¬ φ.Satisfiable := by
  obtain ⟨K, hK, hc⟩ := exists_checkRed_of_augValid h
  cases hK' : K.conclusion with
  | unsat q => exact not_satisfiable_cnf_of_checkRed hK hK'
  | _ => simp [hK', Conclusion.claim] at hc

/-- **Soundness of `SAT : ρ`**: a valid proof of the fragment concluding `SAT : ρ` means that `ρ`
solves the formula. -/
theorem holds_of_augValid_sat {F : List PBConstr} {obj : Option Objective}
    {pres : Option (List ℕ)} {P : AProof} {ρ : List (Literal ℕ)}
    (h : AugValid F obj pres P (.sat (some ρ))) : ∀ c ∈ F, c.Holds (assignOf ρ) := by
  obtain ⟨K, hK, hc⟩ := exists_checkRed_of_augValid h
  cases hK' : K.conclusion with
  | sat asg =>
    simp only [hK', Conclusion.claim, Claim.sat.injEq] at hc
    exact holds_of_checkRed_sat hK (hK'.trans (by rw [hc]))
  | _ => simp [hK', Conclusion.claim] at hc

end Cslib.Logic.PL.VeriPB.Elab

end
