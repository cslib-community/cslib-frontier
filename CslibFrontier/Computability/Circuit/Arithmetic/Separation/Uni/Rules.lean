/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.PM
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Basic

/-!
# The rules of the universal machine

The universal machine (`Uni.universalMachine θ supp`) is a weighted pointer machine (M1's
`Uni.Mach`) that evaluates the interpreter's formulas on trees stored in its heap. Its records have
the kinds `Uni.RecKind` (trees, and the frames of an evaluation), its control modes are
`Uni.Mode`, and its rules `Uni.Rule supp` are the 38 rules of `Uni.BaseRule`, which need no
names, and four families of rules that read a name of `θ` from the heap bit by bit: names are
the prefixes of the support `supp` of `θ` (`Uni.Name`).

## Main definitions

* `Uni.RecKind`, `Uni.Mode`, `Uni.prefixes`, `Uni.Name`, `Uni.BaseRule`, `Uni.Rule`,
  `Uni.Rule.equivSum` (the rules as a sum, for their `Fintype` instance), `Uni.consOrNil`.
* `Uni.RuleData`, `Uni.RuleData.basic`, `Uni.baseRule`, `Uni.rule`, `Uni.universalMachine`.
* `Uni.loadReg`: the register that holds the address of the loaded record, by mode.

## Main results

* `Uni.mem_prefixes`, `Uni.la_eq`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Nc.Uni.Rules`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset

/-- The kinds of records: trees (`nil`, `cons`), unused records, and the frames of an
evaluation. -/
inductive RecKind where
  /-- the empty tree -/
  | nil
  /-- a tree with two subtrees -/
  | cons
  /-- a record that is never loaded -/
  | garbage
  /-- the frame of the final result -/
  | halt
  /-- the end of the parsed input -/
  | parseEnd
  /-- a parse frame, first part -/
  | parseA
  /-- a parse frame, second part -/
  | parseB
  /-- the frame of `hd` -/
  | head
  /-- the frame of `tl` -/
  | tail
  /-- the first frame of `cons` -/
  | cons₁
  /-- the second frame of `cons` -/
  | cons₂
  /-- the frame of `ite` -/
  | ite
  /-- the first frame of `run` -/
  | run₁
  /-- the second frame of `run` -/
  | run₂
  /-- the frame of `θ` -/
  | theta
  deriving DecidableEq

instance : Fintype RecKind :=
  ⟨{.nil, .cons, .garbage, .halt, .parseEnd, .parseA, .parseB, .head, .tail, .cons₁, .cons₂, .ite,
    .run₁, .run₂, .theta}, fun x => by cases x <;> simp⟩

/-- The prefixes of the words in `supp`. -/
@[expose] def prefixes (supp : Finset (List Bool)) : Finset (List Bool) :=
  supp.biUnion fun q => q.inits.toFinset

theorem mem_prefixes {supp : Finset (List Bool)} {p : List Bool} :
    p ∈ prefixes supp ↔ ∃ q ∈ supp, p <+: q := by
  simp [prefixes]

/-- The names that the machine reads: prefixes of the words in `supp`. -/
abbrev Name (supp : Finset (List Bool)) := {p : List Bool // p ∈ prefixes supp}

/-- The control modes. -/
inductive Mode (N : Type) where
  /-- the first two setup steps -/
  | start₀
  | start₁
  /-- the step after parsing -/
  | start₂
  /-- reading the input -/
  | parse
  /-- building the parsed tree -/
  | parseRec
  /-- evaluating a formula -/
  | eval
  /-- reading the opcode, `j` steps in -/
  | decode (j : Fin 11)
  /-- pushing the frame of `cons`, `ite` or `run` -/
  | frameCons
  | frameIte
  | frameRun
  /-- returning a value to the frame on top -/
  | ret
  /-- taking the head or the tail of a value -/
  | head
  | tail
  /-- choosing a branch of `ite` -/
  | ite
  | ite₁
  | ite₂
  /-- reading the name `p` of `θ` -/
  | thetaHead (p : N)
  | thetaBit (p : N)
  /-- the end -/
  | halt
  deriving DecidableEq, Fintype

/-- The rules that read no name. -/
inductive BaseRule where
  | start₀ | start₁ | readEnd | readBit | parseA | parseB | parseEnd | start₂ (b : Bool)
  | evalNil | evalCons | decodeStep (j : Fin 10)
  | decode₀ | decode₁ | decode₂ | decode₃ | decode₄ | decode₅ | decode₆ | decodeGuess (b : Bool)
  | decodeTheta | frameCons (b : Bool) | frameIte (b : Bool) | frameRun (b : Bool)
  | retHead | retTail | head (b : Bool) | tail (b : Bool) | retCons₁ | retCons₂ | retIte
  | iteCons | iteNil | ite₁ (b : Bool) | ite₂ (b : Bool) | retRun₁ | retRun₂ | retHalt
  deriving DecidableEq, Fintype

/-- All rules: those without names, and those that read a name of `θ` from the heap. -/
inductive Rule (supp : Finset (List Bool)) where
  /-- a rule that reads no name -/
  | base (r : BaseRule)
  /-- start reading a name, if the empty word is a prefix -/
  | thetaStart (h : [] ∈ prefixes supp)
  /-- the name `p` is read: apply `θ` -/
  | thetaRead (p : Name supp)
  /-- one more bit of the name follows -/
  | thetaNext (p : Name supp)
  /-- the bit `b` extends `p` to `p'` -/
  | thetaBit (p p' : Name supp) (b : Bool) (h : p'.1 = p.1 ++ [b])
  deriving DecidableEq

/-- `Rule` as a sum. -/
@[expose] def Rule.equivSum (supp : Finset (List Bool)) : Rule supp ≃
    BaseRule ⊕ ({_u : Unit // [] ∈ prefixes supp} ⊕ (Name supp ⊕ (Name supp ⊕
      {x : Name supp × Name supp × Bool // match x with | (p, p', b) => p'.val = p.val ++ [b]})))
    where
  toFun
    | .base r => .inl r
    | .thetaStart h => .inr (.inl ⟨(), h⟩)
    | .thetaRead p => .inr (.inr (.inl p))
    | .thetaNext p => .inr (.inr (.inr (.inl p)))
    | .thetaBit p p' b h => .inr (.inr (.inr (.inr ⟨(p, p', b), h⟩)))
  invFun
    | .inl r => .base r
    | .inr (.inl u) => .thetaStart u.2
    | .inr (.inr (.inl p)) => .thetaRead p
    | .inr (.inr (.inr (.inl p))) => .thetaNext p
    | .inr (.inr (.inr (.inr ⟨(p, p', b), h⟩))) => .thetaBit p p' b h
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with _ | _ | _ | _ | ⟨⟨_, _, _⟩, _⟩ <;> rfl

instance (supp : Finset (List Bool)) : Fintype (Rule supp) :=
  Fintype.ofEquiv _ (Rule.equivSum supp).symm

/-- `cons` or `nil`. -/
@[expose] def consOrNil (b : Bool) : RecKind := if b then .cons else .nil

/-- The data of a rule, with the fields of M1's `Uni.Mach`. -/
structure RuleData (A N : Type) where
  /-- the mode before the step -/
  src : Mode N
  /-- the mode after the step -/
  dst : Mode N
  /-- the input bit read, if any -/
  rd : Option Bool
  /-- the kind of the loaded record -/
  lk : RecKind
  /-- the register with the address of the loaded record -/
  la : Fin 5
  /-- the kind of the allocated record -/
  ak : RecKind
  /-- the variables that fill the allocated record -/
  af : Fin 3 → Fin 9
  /-- the variables that become the registers -/
  dr : Fin 5 → Fin 9
  /-- the weight -/
  wt : A

variable {A : Type} [CommRing A] (θ : List Bool → A) (supp : Finset (List Bool))

/-- A rule that reads no input and has weight `1`: from mode `src` to `dst`, loading a record of
kind `lk` through register `la`, allocating a record of kind `ak` with fields `f₀ f₁ f₂`, and
setting registers `1` to `4` to `d₁ d₂ d₃ d₄` (register `0` stays `0`). -/
@[expose] def RuleData.basic {N : Type} (src dst : Mode N) (lk : RecKind) (la : Fin 5)
    (ak : RecKind) (f₀ f₁ f₂ : Fin 9) (d₁ d₂ d₃ d₄ : Fin 9) : RuleData A N :=
  ⟨src, dst, none, lk, la, ak, ![f₀, f₁, f₂], ![0, d₁, d₂, d₃, d₄], 1⟩

/-- The rules that read no name. -/
@[expose] def baseRule {N : Type} : BaseRule → RuleData A N
  | .start₀ => .basic .start₀ .start₁ .nil 0 .halt 0 0 0 8 0 0 0
  | .start₁ => .basic .start₁ .parse .nil 0 .parseEnd 1 0 0 8 0 0 0
  | .readEnd => { (.basic .parse .parseRec .nil 0 .garbage 0 0 0 0 1 0 0 : RuleData A N) with
      rd := some false }
  | .readBit => { (.basic .parse .parse .nil 0 .parseA 1 0 0 8 0 0 0 : RuleData A N) with
      rd := some true }
  | .parseA => .basic .parseRec .parse .parseA 2 .parseB 1 5 0 8 0 0 0
  | .parseB => .basic .parseRec .parseRec .parseB 2 .cons 5 1 0 8 6 0 0
  | .parseEnd => .basic .parseRec .start₂ .parseEnd 2 .garbage 0 0 0 1 5 0 0
  | .start₂ b => .basic .start₂ .eval (consOrNil b) 1 .garbage 0 0 0 5 6 2 0
  | .evalNil => .basic .eval .ret .nil 1 .garbage 0 0 0 1 3 0 0
  | .evalCons => .basic .eval (.decode 0) .cons 1 .garbage 0 0 0 5 6 2 3
  | .decodeStep j => .basic (.decode j.castSucc) (.decode j.succ) .cons 1 .garbage 0 0 0 6 2 3 4
  | .decode₀ => .basic (.decode 0) .ret .nil 1 .garbage 0 0 0 2 4 0 0
  | .decode₁ => .basic (.decode 1) .ret .nil 1 .garbage 0 0 0 3 4 0 0
  | .decode₂ => .basic (.decode 2) .eval .nil 1 .head 4 0 0 2 3 8 0
  | .decode₃ => .basic (.decode 3) .eval .nil 1 .tail 4 0 0 2 3 8 0
  | .decode₄ => .basic (.decode 4) .frameCons .nil 1 .garbage 0 0 0 2 3 4 0
  | .decode₅ => .basic (.decode 5) .frameIte .nil 1 .garbage 0 0 0 2 3 4 0
  | .decode₆ => .basic (.decode 6) .frameRun .nil 1 .garbage 0 0 0 2 3 4 0
  | .decodeGuess b =>
    if b then .basic (.decode 7) .ret .nil 1 .cons 0 0 0 8 4 0 0
    else .basic (.decode 7) .ret .nil 1 .garbage 0 0 0 0 4 0 0
  | .decodeTheta => .basic (.decode 9) .eval .nil 1 .theta 4 0 0 2 3 8 0
  | .frameCons b => .basic .frameCons .eval (consOrNil b) 1 .cons₁ 6 2 3 5 2 8 0
  | .frameIte b => .basic .frameIte .eval (consOrNil b) 1 .ite 6 2 3 5 2 8 0
  | .frameRun b => .basic .frameRun .eval (consOrNil b) 1 .run₁ 6 2 3 5 2 8 0
  | .retHead => .basic .ret .head .head 2 .garbage 0 0 0 1 5 0 0
  | .retTail => .basic .ret .tail .tail 2 .garbage 0 0 0 1 5 0 0
  | .head b => .basic .head .ret (consOrNil b) 1 .garbage 0 0 0 5 2 0 0
  | .tail b => .basic .tail .ret (consOrNil b) 1 .garbage 0 0 0 6 2 0 0
  | .retCons₁ => .basic .ret .eval .cons₁ 2 .cons₂ 1 7 0 5 6 8 0
  | .retCons₂ => .basic .ret .ret .cons₂ 2 .cons 5 1 0 8 6 0 0
  | .retIte => .basic .ret .ite .ite 2 .garbage 0 0 0 1 5 6 7
  | .iteCons => .basic .ite .ite₁ .cons 1 .garbage 0 0 0 2 3 4 0
  | .iteNil => .basic .ite .ite₂ .nil 1 .garbage 0 0 0 2 3 4 0
  | .ite₁ b => .basic .ite₁ .eval (consOrNil b) 1 .garbage 0 0 0 5 2 3 0
  | .ite₂ b => .basic .ite₂ .eval (consOrNil b) 1 .garbage 0 0 0 6 2 3 0
  | .retRun₁ => .basic .ret .eval .run₁ 2 .run₂ 1 7 0 5 6 8 0
  | .retRun₂ => .basic .ret .eval .run₂ 2 .garbage 0 0 0 5 1 6 0
  | .retHalt => .basic .ret .halt .halt 2 .garbage 0 0 0 0 0 0 0

/-- The rules. -/
@[expose] def rule : Rule supp → RuleData A (Name supp)
  | .base r => baseRule r
  | .thetaStart h => .basic .ret (.thetaHead ⟨[], h⟩) .theta 2 .garbage 0 0 0 1 5 0 0
  | .thetaRead p => { (.basic (.thetaHead p) .ret .nil 1 .garbage 0 0 0 0 2 0 0 :
      RuleData A (Name supp)) with wt := θ p.1 }
  | .thetaNext p => .basic (.thetaHead p) (.thetaBit p) .cons 1 .garbage 0 0 0 5 6 2 0
  | .thetaBit p p' b _ =>
    .basic (.thetaBit p) (.thetaHead p') (consOrNil b) 1 .garbage 0 0 0 2 3 0 0

/-- **The universal machine.** -/
@[expose] noncomputable def universalMachine : Mach A (Mode (Name supp)) RecKind where
  Rl := Rule supp
  src r := (rule θ supp r).src
  dst r := (rule θ supp r).dst
  rd r := (rule θ supp r).rd
  lk r := (rule θ supp r).lk
  la r := (rule θ supp r).la
  ak r := (rule θ supp r).ak
  af r := (rule θ supp r).af
  dr r := (rule θ supp r).dr
  wt r := (rule θ supp r).wt
  m0 := .start₀
  mh := .halt
  kN := .nil

/-- The register that holds the address of the loaded record depends on the mode only. -/
@[expose] def loadReg {N : Type} : Mode N → Fin 5
  | .start₀ => 0
  | .start₁ => 0
  | .parse => 0
  | .parseRec => 2
  | .ret => 2
  | _ => 1

theorem la_eq (r : Rule supp) : (rule θ supp r).la = loadReg (rule θ supp r).src := by
  cases r with
  | base r => cases r <;> first | rfl | (rename_i b; cases b <;> rfl)
  | _ => rfl

end Cslib.Circuits.Arithmetic.Separation.Uni
