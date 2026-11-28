/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Exact fixed-point interval certificate checker for matched-pair Gaussian majorants

This module defines the pure-integer fixed-point interval arithmetic (`Ival` at scale `10 ^ 8`),
polynomial `arccos` majorant tables (`starQI`, `crossQI`), and balanced-tree stack-machine
certificate verifier (`Prog`, `runProg`, `checkBox`) used to certify
`pairCost u 0 ≤ 27735 / 100000` across the `6`-dimensional admissible Gram space. Splitting
interval evaluations into short strict stages returning `Option` records pops intermediate WHNF
reduction frames so kernel verification runs well within default recursion and heartbeat limits
while avoiding analytic imports in the certificate shards.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.certScale`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.sminI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.cminI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.maxoI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.c2I`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.piLoI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.piHiI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.targetI`: fixed-point scale `10 ^ 8` and rational
  problem constants.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.forceNat`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.bindInt`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ible`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.iblt`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.intEq`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.natLt`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.natEq`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.imax`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.imin`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.cdiv`: strict `Int`/`Bool` arithmetic helpers.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.Ival`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.bindIval`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivConst`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivPi`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivAdd`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivSub`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivNeg`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivMax`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivAbs`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivMul`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivSq`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivDivPos`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivScaleInt`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivDivInt`: outward-rounded fixed-point interval
  operations.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.QuadI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.starQI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.crossQI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivQeval`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.ivQslope`: quadratic `arccos` majorant tables and
  interval evaluators.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.BoxI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.boxEq`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.bindBox`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.evalBox`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.rootBoxI`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.SubTree`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.lookupSub`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.SubTreeAll`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.PlanarStep`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.Step`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.Prog`: `6`-dimensional fixed-point boxes,
  balanced lookup trees, certificate instructions, and balanced binary step trees.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.calcSchurRhsHi`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.clampBox`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.isEmptyBox`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.splitBox`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.chkSchur`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.chkGram`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.chkShep`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.bound1dPt`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.bound1dIv`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.chkPlanar`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.stepOne`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.runProg`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.checkBox`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.Certified1`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.Certified2`: staged leaf checkers and
  balanced-tree stack-machine verifier.
-/

public section

namespace Cslib.Circuits.Frontier.Gaussian.PairBound.Cert

/-- Fixed-point scale `10 ^ 8` for interval endpoints and certificate witnesses. -/
@[expose] def certScale : Int := 100000000

/-- Fixed-point intra-edge switching threshold `0.9428 * 10 ^ 8`. -/
@[expose] def sminI : Int := 94280000

/-- Fixed-point cross-edge correlation floor `0.79998 * 10 ^ 8`. -/
@[expose] def cminI : Int := 79998000

/-- Fixed-point antisymmetric coordinate cap `0.10001 * 10 ^ 8`. -/
@[expose] def maxoI : Int := 10001000

/-- Fixed-point Schur offset constant `1.322905 * 10 ^ 8`. -/
@[expose] def c2I : Int := 132290500

/-- Rigorous lower integer enclosure of `π * 10 ^ 8`. -/
@[expose] def piLoI : Int := 314159200

/-- Rigorous upper integer enclosure of `π * 10 ^ 8`. -/
@[expose] def piHiI : Int := 314159300

/-- Fixed-point pair-cost target `0.27735 * 10 ^ 8 = 5547 / 20000 * 10 ^ 8`. -/
@[expose] def targetI : Int := 27735000

/-- Force a `Nat` to a literal in kernel WHNF before continuing (`forceNat n k = k n`). -/
@[expose] def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn n (k 0) (fun m => k (Nat.succ m))

/-- Force an `Int` to a literal in kernel WHNF before continuing (`bindInt x k = k x`). -/
@[expose] def bindInt {α : Type} (x : Int) (k : Int → α) : α :=
  Int.casesOn x (fun n => forceNat n fun n' => k (.ofNat n'))
    (fun n => forceNat n fun n' => k (.negSucc n'))

/-- Pure `Bool` order `a ≤ b` on `Int` without constructing propositional proof terms. -/
@[expose] def ible (a b : Int) : Bool :=
  Int.casesOn (Int.sub b a) (fun _ => true) (fun _ => false)

/-- Pure `Bool` strict order `a < b` on `Int` without constructing propositional proof terms. -/
@[expose] def iblt (a b : Int) : Bool :=
  Int.casesOn (Int.sub b a) (fun n => Nat.casesOn n false (fun _ => true)) (fun _ => false)

/-- Pure `Bool` equality on `Int` without constructing propositional proof terms. -/
@[expose] def intEq (a b : Int) : Bool :=
  ible a b && ible b a

/-- Pure `Bool` strict order on `Nat` via `iblt`. -/
@[expose] def natLt (a b : Nat) : Bool :=
  iblt (.ofNat a) (.ofNat b)

/-- Pure `Bool` equality on `Nat` via `intEq`. -/
@[expose] def natEq (a b : Nat) : Bool :=
  intEq (.ofNat a) (.ofNat b)

/-- Pure `Bool`-dispatched integer maximum without propositional proof terms. -/
@[expose] def imax (a b : Int) : Int :=
  if ible a b then b else a

/-- Pure `Bool`-dispatched integer minimum without propositional proof terms. -/
@[expose] def imin (a b : Int) : Int :=
  if ible a b then a else b

/-- Ceiling Euclidean division for `b > 0`: `(a + b - 1) / b`. -/
@[expose] def cdiv (a b : Int) : Int :=
  bindInt a fun a' => bindInt b fun b' =>
  Int.ediv (Int.sub (Int.add a' b') 1) b'

/-- Closed real interval `[lo / 10 ^ 8, hi / 10 ^ 8]`. -/
structure Ival where
  /-- Scaled lower endpoint `lo` representing `lo / 10 ^ 8`. -/
  lo : Int
  /-- Scaled upper endpoint `hi` representing `hi / 10 ^ 8`. -/
  hi : Int
  deriving DecidableEq, Repr

/-- Force both endpoints of an `Ival` to literals in kernel WHNF (`bindIval v k = k v`). -/
@[expose] def bindIval {α : Type} (v : Ival) (k : Ival → α) : α :=
  Ival.casesOn v fun lo hi =>
    bindInt lo fun lo' => bindInt hi fun hi' => k ⟨lo', hi'⟩

/-- Point interval `[n / 10 ^ 8, n / 10 ^ 8]`. -/
@[expose] def ivConst (n : Int) : Ival := ⟨n, n⟩

/-- Verified enclosure `[piLoI / 10 ^ 8, piHiI / 10 ^ 8]` of `π`. -/
@[expose] def ivPi : Ival := ⟨piLoI, piHiI⟩

/-- Exact interval sum `a + b` at fixed-point scale `10 ^ 8`. -/
@[expose] def ivAdd (a b : Ival) : Ival :=
  Ival.casesOn a fun alo ahi => Ival.casesOn b fun blo bhi =>
  ⟨Int.add alo blo, Int.add ahi bhi⟩

/-- Exact interval difference `a - b` at fixed-point scale `10 ^ 8`. -/
@[expose] def ivSub (a b : Ival) : Ival :=
  Ival.casesOn a fun alo ahi => Ival.casesOn b fun blo bhi =>
  ⟨Int.sub alo bhi, Int.sub ahi blo⟩

/-- Exact interval negation `-a` at fixed-point scale `10 ^ 8`. -/
@[expose] def ivNeg (a : Ival) : Ival :=
  Ival.casesOn a fun alo ahi => ⟨Int.neg ahi, Int.neg alo⟩

/-- Pointwise interval maximum `max a b`. -/
@[expose] def ivMax (a b : Ival) : Ival :=
  Ival.casesOn a fun alo ahi => Ival.casesOn b fun blo bhi =>
  ⟨imax alo blo, imax ahi bhi⟩

/-- Exact interval absolute value `|a|`. -/
@[expose] def ivAbs (a : Ival) : Ival :=
  Ival.casesOn a fun alo ahi =>
  if ible 0 alo then ⟨alo, ahi⟩
  else if ible ahi 0 then ⟨Int.neg ahi, Int.neg alo⟩
  else ⟨0, imax (Int.neg alo) ahi⟩

/-- Outward-rounded interval product `a * b` at fixed-point scale `10 ^ 8`. -/
@[expose] def ivMul (a b : Ival) : Ival :=
  bindIval a fun a' => bindIval b fun b' =>
  -- Fast-path nonnegative intervals (covers >85% of all multiplications in chkPlanar!):
  if ible 0 a'.lo && ible 0 b'.lo then
    ⟨Int.ediv (Int.mul a'.lo b'.lo) certScale, cdiv (Int.mul a'.hi b'.hi) certScale⟩
  else
    bindInt (Int.mul a'.lo b'.lo) fun p1 =>
    bindInt (Int.mul a'.lo b'.hi) fun p2 =>
    bindInt (Int.mul a'.hi b'.lo) fun p3 =>
    bindInt (Int.mul a'.hi b'.hi) fun p4 =>
    bindInt (imin p1 p2) fun m12 => bindInt (imin p3 p4) fun m34 =>
    bindInt (imax p1 p2) fun x12 => bindInt (imax p3 p4) fun x34 =>
    ⟨Int.ediv (imin m12 m34) certScale, cdiv (imax x12 x34) certScale⟩

/-- Outward-rounded interval square `a ^ 2` exploiting sign of `0` in `a`. -/
@[expose] def ivSq (a : Ival) : Ival :=
  bindIval a fun a' =>
  if ible 0 a'.lo then
    ⟨Int.ediv (Int.mul a'.lo a'.lo) certScale, cdiv (Int.mul a'.hi a'.hi) certScale⟩
  else if ible a'.hi 0 then
    ⟨Int.ediv (Int.mul a'.hi a'.hi) certScale, cdiv (Int.mul a'.lo a'.lo) certScale⟩
  else
    bindInt (imax (Int.neg a'.lo) a'.hi) fun mx =>
    ⟨0, cdiv (Int.mul mx mx) certScale⟩

/-- Outward-rounded interval quotient `a / b` when `0 < b.lo`. -/
@[expose] def ivDivPos (a b : Ival) : Ival :=
  bindIval a fun a' => bindIval b fun b' =>
  let loDen := if ible 0 a'.lo then b'.hi else b'.lo
  let hiDen := if ible 0 a'.hi then b'.lo else b'.hi
  ⟨Int.ediv (Int.mul a'.lo certScale) loDen, cdiv (Int.mul a'.hi certScale) hiDen⟩

/-- Exact multiplication of an interval `a` by an integer scalar `k`. -/
@[expose] def ivScaleInt (k : Int) (a : Ival) : Ival :=
  Ival.casesOn a fun alo ahi =>
  if ible 0 k then ⟨Int.mul k alo, Int.mul k ahi⟩ else ⟨Int.mul k ahi, Int.mul k alo⟩

/-- Outward-rounded division of an interval `a` by a positive integer `k`. -/
@[expose] def ivDivInt (a : Ival) (k : Int) : Ival :=
  Ival.casesOn a fun alo ahi =>
  ⟨Int.ediv alo k, cdiv ahi k⟩

/-- Coefficients of a concave quadratic upper bound
`c0 / S - (c1 / S) * (r - r0 / S) - (c2 / S) * (r - r0 / S) ^ 2` valid on `[rmin / S, 1]`. -/
structure QuadI where
  /-- Scaled value `c0` at expansion point `r0`. -/
  c0 : Int
  /-- Scaled downward linear slope `c1` at expansion point `r0`. -/
  c1 : Int
  /-- Scaled concave quadratic curvature `c2`. -/
  c2 : Int
  /-- Scaled expansion point `r0`. -/
  r0 : Int
  /-- Scaled left validity endpoint `rmin`. -/
  rmin : Int
  deriving DecidableEq, Repr

/-- Lookup table of certified concave quadratic upper bounds for intra-star `arccos`. -/
@[expose] def starQI : Nat → Option QuadI
  | 0 => some ⟨29398200, 345260000, 1270000000, 95710000, 94280000⟩
  | 1 => some ⟨33389176, 305150117, 1244769255, 94477500, 94240000⟩
  | 2 => some ⟨29808893, 340500824, 1552028216, 95590000, 94240000⟩
  | 3 => some ⟨24812415, 407195833, 2189826429, 96937500, 94240000⟩
  | 4 => some ⟨18410793, 546243484, 3708490192, 98310000, 94240000⟩
  | 5 => some ⟨12028074, 833397986, 7351200833, 99277500, 94240000⟩
  | 6 => some ⟨5657614, 1768475148, 21045918365, 99840000, 94240000⟩
  | _ => none

/-- Lookup table of certified concave quadratic upper bounds for cross-pair `arccos`. -/
@[expose] def crossQI : Nat → Option QuadI
  | 0 => some ⟨54806500, 192007000, 185000000, 85355000, 79998000⟩
  | 1 => some ⟨63279698, 169134424, 189370027, 80640000, 79998000⟩
  | 2 => some ⟨60310053, 176348911, 207613760, 82360000, 79998000⟩
  | 3 => some ⟨54411024, 193217208, 252118172, 85560000, 79998000⟩
  | 4 => some ⟨50018837, 208545143, 294642855, 87750000, 79998000⟩
  | 5 => some ⟨44200486, 233806679, 368599765, 90390000, 79998000⟩
  | 6 => some ⟨36980342, 276694788, 503563088, 93240000, 79998000⟩
  | 7 => some ⟨28379547, 357150300, 781065086, 96000000, 79998000⟩
  | 8 => some ⟨18410793, 546243484, 1509192351, 98310000, 79998000⟩
  | 9 => some ⟨8487836, 1179574054, 4229142635, 99640000, 79998000⟩
  | 10 => some ⟨50018837, 208545143, 326474077, 87750000, 83190000⟩
  | 11 => some ⟨36980342, 276694788, 565484858, 93240000, 83190000⟩
  | 12 => some ⟨28379547, 357150300, 886858369, 96000000, 83190000⟩
  | 13 => some ⟨36980342, 276694788, 660369805, 93240000, 87040000⟩
  | 14 => some ⟨28379547, 357150300, 1052295916, 96000000, 87040000⟩
  | 15 => some ⟨18410793, 546243484, 2745766940, 98310000, 91000000⟩
  | 16 => some ⟨18410793, 546243484, 3708490192, 98310000, 94240000⟩
  | 17 => some ⟨8487836, 1179574054, 12222222220, 99640000, 94240000⟩
  | _ => none

/-- Outward-rounded evaluation of concave quadratic model `q` on interval `r`. -/
@[expose] def ivQeval (q : QuadI) (r : Ival) : Ival :=
  bindIval (ivSub r (ivConst q.r0)) fun d =>
  ivSub (ivSub (ivConst q.c0) (ivMul (ivConst q.c1) d)) (ivMul (ivConst q.c2) (ivSq d))

/-- Outward-rounded negative derivative `-q'(r) = c1 + 2 * c2 * (r - r0)` on interval `r`. -/
@[expose] def ivQslope (q : QuadI) (r : Ival) : Ival :=
  bindIval (ivSub r (ivConst q.r0)) fun d =>
  ivAdd (ivConst q.c1) (ivScaleInt 2 (ivMul (ivConst q.c2) d))

/-- Fixed-point `6`-dimensional box `(sab, scd, rb, o1, o2, tau0)` at scale `10 ^ 8`. -/
structure BoxI where
  /-- Lower endpoint of `sab`. -/
  a0 : Int
  /-- Upper endpoint of `sab`. -/
  a1 : Int
  /-- Lower endpoint of `scd`. -/
  b0 : Int
  /-- Upper endpoint of `scd`. -/
  b1 : Int
  /-- Lower endpoint of `rb`. -/
  r0 : Int
  /-- Upper endpoint of `rb`. -/
  r1 : Int
  /-- Lower endpoint of `o1`. -/
  o10 : Int
  /-- Upper endpoint of `o1`. -/
  o11 : Int
  /-- Lower endpoint of `o2`. -/
  o20 : Int
  /-- Upper endpoint of `o2`. -/
  o21 : Int
  /-- Lower endpoint of `tau0`. -/
  t0 : Int
  /-- Upper endpoint of `tau0`. -/
  t1 : Int
  deriving DecidableEq, Repr

/-- Pure `Bool` equality on `BoxI` across modules without `DecidableEq` proof terms. -/
@[expose] def boxEq (a b : BoxI) : Bool :=
  BoxI.casesOn a fun a0 a1 b0 b1 r0 r1 o10 o11 o20 o21 t0 t1 =>
  BoxI.casesOn b fun a0' a1' b0' b1' r0' r1' o10' o11' o20' o21' t0' t1' =>
    intEq a0 a0' && intEq a1 a1' && intEq b0 b0' && intEq b1 b1' &&
    intEq r0 r0' && intEq r1 r1' && intEq o10 o10' && intEq o11 o11' &&
    intEq o20 o20' && intEq o21 o21' && intEq t0 t0' && intEq t1 t1'

/-- Balanced binary search tree of indexed sub-boxes for `O(log N)` WHNF lookup. -/
inductive SubTree
  | empty
  | leaf (k : Nat) (b : BoxI)
  | node (mid : Nat) (left right : SubTree)
  deriving Repr

/-- Lookup sub-box `idx` in a `SubTree` in `O(log N)` pure `Bool` comparisons. -/
@[expose] def lookupSub : SubTree → Nat → Option BoxI
  | .empty, _ => none
  | .leaf k b, idx => if natEq idx k then some b else none
  | .node mid l r, idx => if natLt idx mid then lookupSub l idx else lookupSub r idx

/-- Conjunction of `P` over all leaf boxes stored in a `SubTree`. -/
@[expose] def SubTreeAll (P : BoxI → Prop) : SubTree → Prop
  | .empty => True
  | .leaf _ b => P b
  | .node _ l r => SubTreeAll P l ∧ SubTreeAll P r

/-- Force all `12` coordinates of a `BoxI` to literals in kernel WHNF (`bindBox b k = k b`). -/
@[expose] def bindBox {α : Type} (b : BoxI) (k : BoxI → α) : α :=
  BoxI.casesOn b fun a0 a1 b0 b1 r0 r1 o10 o11 o20 o21 t0 t1 =>
    bindInt a0 fun a0' => bindInt a1 fun a1' =>
    bindInt b0 fun b0' => bindInt b1 fun b1' =>
    bindInt r0 fun r0' => bindInt r1 fun r1' =>
    bindInt o10 fun o10' => bindInt o11 fun o11' =>
    bindInt o20 fun o20' => bindInt o21 fun o21' =>
    bindInt t0 fun t0' => bindInt t1 fun t1' =>
    k ⟨a0', a1', b0', b1', r0', r1', o10', o11', o20', o21', t0', t1'⟩

/-- Force all `12` coordinates of `b` and wrap in `some`, popping `bindBox` stack frames. -/
@[expose] def evalBox (b : BoxI) : Option BoxI :=
  bindBox b some

/-- Root `6`-dimensional box covering the entire symmetry-reduced hard Gram domain. -/
@[expose] def rootBoxI : BoxI :=
  ⟨sminI, certScale, sminI, certScale, cminI, certScale, 0, maxoI, 0, maxoI, -maxoI, maxoI⟩

/-- Witness parameters for a planar-volume leaf (`volume_planarRectSet_le_out` or `_in`). -/
structure PlanarStep where
  /-- Whether to use the interior (`true`) or exterior (`false`) planar volume bound. -/
  isIn : Bool
  /-- Index in `starQI` for `sab`. -/
  ia : Nat
  /-- Index in `starQI` for `scd`. -/
  ib : Nat
  /-- Index in `crossQI` for `sac`. -/
  ic0 : Nat
  /-- Index in `crossQI` for `sbd`. -/
  ic1 : Nat
  /-- Index in `crossQI` for `sad`. -/
  ic2 : Nat
  /-- Index in `crossQI` for `sbc`. -/
  ic3 : Nat
  /-- Mode (`0`, `1`, or `2`) for bounding the planar Gaussian expectation factor `cex`. -/
  cexMode : Nat
  /-- Nonnegative Lagrange multiplier for positive-sign Schur penalty. -/
  lam : Int
  /-- Nonnegative Lagrange multiplier for negative-sign Schur penalty. -/
  lamM : Int
  /-- Positive AM-GM balancing ratio `rxy`. -/
  rxy : Int
  /-- Certified lower bound `slo` on `√D`. -/
  slo : Int
  /-- Certified upper bound `shi` on `√D`. -/
  shi : Int
  /-- Midpoint expansion parameter `sm` for `D ^ (-3 / 2)`. -/
  sm : Int
  /-- Certified upper bound `cex` on the planar Gaussian factor. -/
  cex : Int
  /-- Certified lower bound on `|ρ|` in `cexMode = 2`. -/
  rhoLo : Int
  /-- Certified upper bound on `|ρ|` in `cexMode = 2`. -/
  rhoHi : Int
  /-- Certified lower bound on `(det K) ^ (-1 / 2)` when `isIn = true`. -/
  invSdetK : Int
  deriving DecidableEq, Repr

/-- Certificate stack-machine instruction. -/
inductive Step
  | clamp
  | split (d : Nat) (m : Int)
  | empty
  | schur (sigPos : Bool)
  | gram
  | shep (mode ia ib ic0 ic1 ic2 ic3 : Nat)
  | planar (p : PlanarStep)
  | subbox (idx : Nat)
  deriving DecidableEq, Repr

/-- Balanced binary tree of certificate instructions (`O(log N)` recursion depth). -/
inductive Prog
  | step (s : Step)
  | seq (p1 p2 : Prog)
  deriving DecidableEq, Repr

/-- Validated first stage of `calcSchurRhsHi`. -/
structure SchurPre where
  /-- Interval enclosure of `c2 - sab`. -/
  a1 : Ival
  /-- Interval enclosure of `c2 + sab`. -/
  a2 : Ival
  /-- Interval enclosure of `c2 + scd`. -/
  d2 : Ival
  /-- Interval enclosure of `15 * rb + 16 * sig * tau0`. -/
  m11 : Ival
  /-- Interval enclosure of `15 * tau0 + 16 * sig * rb`. -/
  m22 : Ival
  /-- Interval enclosure of `15 * o2 + 16 * sig * o1`. -/
  m12 : Ival
  /-- Interval enclosure of `15 * o1 + 16 * sig * o2`. -/
  m21 : Ival

/-- Precompute and validate positivity side conditions for `calcSchurRhsHi`. -/
@[expose] def schurPre (b : BoxI) (sig : Int) : Option SchurPre :=
  let rb : Ival := ⟨b.r0, b.r1⟩
  let o1 : Ival := ⟨b.o10, b.o11⟩
  let o2 : Ival := ⟨b.o20, b.o21⟩
  let t : Ival := ⟨b.t0, b.t1⟩
  bindIval ⟨c2I - b.a1, c2I - b.a0⟩ fun a1 =>
  bindIval ⟨c2I + b.a0, c2I + b.a1⟩ fun a2 =>
  bindIval ⟨c2I + b.b0, c2I + b.b1⟩ fun d2 =>
  if ible a1.lo 0 || ible a2.lo 0 || ible d2.lo 0 then none
  else
    bindIval (ivAdd (ivScaleInt 15 rb) (ivScaleInt (sig * 16) t)) fun m11 =>
    if ible m11.lo 0 then none
    else
      bindIval (ivAdd (ivScaleInt 15 t) (ivScaleInt (sig * 16) rb)) fun m22 =>
      bindIval (ivAdd (ivScaleInt 15 o2) (ivScaleInt (sig * 16) o1)) fun m12 =>
      bindIval (ivAdd (ivScaleInt 15 o1) (ivScaleInt (sig * 16) o2)) fun m21 =>
      some ⟨a1, a2, d2, m11, m22, m12, m21⟩

/-- Upper bound on the nonlinear Schur remainder (or `-1` if side conditions do not hold). -/
@[expose] def calcSchurRhsHi (b : BoxI) (sig : Int) : Int :=
  match schurPre b sig with
  | none => -1
  | some sp =>
    let sab : Ival := ⟨b.a0, b.a1⟩
    let scd : Ival := ⟨b.b0, b.b1⟩
    bindIval (ivSub (ivMul sp.a2 (ivSub (ivMul sp.a1 sp.d2) (ivDivInt (ivSq sp.m12) 1225)))
      (ivMul sp.a1 (ivDivInt (ivSq sp.m22) 1225))) fun x2 =>
    if ible x2.lo 0 then -1
    else
      bindIval (ivDivInt (ivAdd (ivMul sp.a2 (ivMul (ivAbs sp.m11) (ivAbs sp.m12)))
        (ivMul sp.a1 (ivMul (ivAbs sp.m21) (ivAbs sp.m22)))) 1225) fun y =>
      bindIval (ivDivInt (ivSub sab scd) 2) fun smBox =>
      bindIval (ivDivInt (ivAdd sab scd) 2) fun spBox =>
      bindIval (ivAdd (ivSub (ivConst c2I) spBox) (ivDivInt sp.m11 35)) fun denom =>
      bindIval (ivMul sp.a2 x2) fun a2x2 =>
      if ible denom.lo 0 || ible a2x2.lo 0 then -1
      else
        bindIval (ivAdd (ivSq smBox)
          (ivAdd (ivDivPos (ivMul sp.a1 (ivDivInt (ivSq sp.m21) 1225)) sp.a2)
            (ivDivPos (ivSq y) a2x2))) fun num =>
        (ivDivPos num denom).hi

/-- Check whether any coordinate interval of `b` is strictly inverted (`hi < lo`). -/
@[expose] def isEmptyBox (b : BoxI) : Bool :=
  iblt b.a1 b.a0 || iblt b.b1 b.b0 || iblt b.r1 b.r0 || iblt b.o11 b.o10 ||
    iblt b.o21 b.o20 || iblt b.t1 b.t0

/-- Stage 1 of `clampBox`: tighten `o1 ≤ o2` symmetry and linear cross-correlation bounds. -/
@[expose] def clampStep1 (b0 : BoxI) : Option BoxI :=
  bindInt (imax b0.o20 b0.o10) fun o20 =>
  bindInt (imin b0.o11 b0.o21) fun o11 =>
  bindInt (imax 0 (o20 - o11)) fun dlo =>
  bindInt (imin b0.t1 (imin (certScale - b0.r0 - b0.o10 - o20) (b0.r1 - cminI - dlo))) fun t1a =>
  bindInt (imax b0.t0 (imax (cminI - b0.r1 + b0.o10 + o20) (b0.r0 - certScale + dlo))) fun t0a =>
  some { b0 with o20 := o20, o11 := o11, t0 := t0a, t1 := t1a }

/-- Intermediate state after Schur `t`-clamping in `clampBox`. -/
structure ClampS2 where
  /-- Box with Schur-tightened `tau0` bounds. -/
  b : BoxI
  /-- Upper bound on negative-sign Schur remainder (`-1` if inactive). -/
  srM : Int
  /-- Upper bound on positive-sign Schur remainder (`-1` if inactive). -/
  srP : Int

/-- Stage 2 of `clampBox`: tighten `tau0` using both Schur remainder inequalities. -/
@[expose] def clampStep2 (b1 : BoxI) : Option ClampS2 :=
  bindInt (calcSchurRhsHi b1 (-1)) fun srM =>
  bindInt (calcSchurRhsHi b1 1) fun srP =>
  bindInt (cdiv (b1.a1 + b1.b1) 2) fun spHi =>
  bindInt (if ible 0 srM then
      imin b1.t1 (cdiv (35 * (spHi + cdiv (3 * b1.r1) 7 - c2I + srM)) 16)
    else b1.t1) fun t1b =>
  bindInt (if ible 0 srP then
      imax b1.t0 (-cdiv (35 * (spHi + cdiv (3 * b1.r1) 7 - c2I + srP)) 16)
    else b1.t0) fun t0b =>
  some ⟨{ b1 with t0 := t0b, t1 := t1b }, srM, srP⟩

/-- Intermediate Gram diagonal intervals in `clampBox`. -/
structure ClampS3 where
  /-- Interval enclosure of `(1 + sab) / 2`. -/
  vx : Ival
  /-- Interval enclosure of `(1 + scd) / 2`. -/
  vy : Ival
  /-- Interval enclosure of `vx * vy - rb ^ 2`. -/
  dIv : Ival
  /-- Interval enclosure of the first Schur-complement diagonal entry `K_{00}`. -/
  k00 : Ival
  /-- Interval enclosure of the second Schur-complement diagonal entry `K_{11}`. -/
  k11 : Ival

/-- Stage 3 of `clampBox`: enclose the Schur-complement diagonal entries `K_{00}` and `K_{11}`. -/
@[expose] def clampStep3 (b2 : BoxI) : Option ClampS3 :=
  bindIval (ivDivInt (ivAdd (ivConst certScale) ⟨b2.a0, b2.a1⟩) 2) fun vx =>
  bindIval (ivDivInt (ivAdd (ivConst certScale) ⟨b2.b0, b2.b1⟩) 2) fun vy =>
  bindIval (ivSub (ivMul vx vy) (ivSq ⟨b2.r0, b2.r1⟩)) fun dIv =>
  if ible dIv.lo 0 then none
  else
    let o1 : Ival := ⟨b2.o10, b2.o11⟩
    let o2 : Ival := ⟨b2.o20, b2.o21⟩
    bindIval (ivSub (ivDivInt (ivSub (ivConst certScale) ⟨b2.a0, b2.a1⟩) 2)
      (ivDivPos (ivMul (ivSq o1) vx) dIv)) fun k00 =>
    bindIval (ivSub (ivDivInt (ivSub (ivConst certScale) ⟨b2.b0, b2.b1⟩) 2)
      (ivDivPos (ivMul (ivSq o2) vy) dIv)) fun k11 =>
    some ⟨vx, vy, dIv, k00, k11⟩

/-- Stage 4 of `clampBox`: tighten `tau0` via `det K ≥ 0` AM-GM and combined Gram-Schur bounds. -/
@[expose] def clampStep4 (b1 : BoxI) (cs2 : ClampS2) (cs3 : ClampS3) : Option BoxI :=
  let b2 := cs2.b
  if iblt cs3.k00.hi 0 || iblt cs3.k11.hi 0 then some { b2 with t0 := 1, t1 := 0 }
  else
    let o1 : Ival := ⟨b2.o10, b2.o11⟩
    let o2 : Ival := ⟨b2.o20, b2.o21⟩
    let rb : Ival := ⟨b2.r0, b2.r1⟩
    bindInt (cdiv (cs3.k00.hi + cs3.k11.hi) 2) fun sKKAmgm =>
    bindIval (ivDivPos (ivMul (ivMul o1 o2) rb) cs3.dIv) fun prod =>
    bindInt (imin b2.t1 (sKKAmgm - prod.lo)) fun t1c =>
    bindInt (imax b2.t0 (-sKKAmgm - prod.hi)) fun t0c =>
    bindInt (ivDivInt (ivAdd (ivDivPos (ivMul (ivSq o1) cs3.vx) cs3.dIv)
      (ivDivPos (ivMul (ivSq o2) cs3.vy) cs3.dIv)) 2).lo fun uqLo =>
    bindInt (certScale / 2 - uqLo) fun gramC =>
    bindInt (if ible 0 cs2.srM then
        imin t1c (cdiv (35 * (cdiv (3 * b1.r1) 7 - c2I + cs2.srM)) 86 +
          cdiv (35 * (gramC - prod.lo)) 43)
      else t1c) fun t1d =>
    bindInt (if ible 0 cs2.srP then
        imax t0c (-cdiv (35 * (cdiv (3 * b1.r1) 7 - c2I + cs2.srP)) 86 -
          cdiv (35 * (gramC + prod.hi)) 43)
      else t0c) fun t0d =>
    some { b2 with t0 := t0d, t1 := t1d }

/-- Sound domain tightening using cross-correlation bounds, Schur inequalities, and Gram PSD. -/
@[expose] def clampBox (b0 : BoxI) : Option BoxI :=
  match evalBox b0 with
  | none => none
  | some b0' =>
    match clampStep1 b0' with
    | none => none
    | some b1 =>
      if isEmptyBox b1 then some b1
      else
        match clampStep2 b1 with
        | none => none
        | some cs2 =>
          if iblt cs2.b.t1 cs2.b.t0 then some cs2.b
          else
            match clampStep3 cs2.b with
            | none => some cs2.b
            | some cs3 => clampStep4 b1 cs2 cs3

/-- Bisect box `b` along coordinate axis `d ∈ {0, .., 5}` at split point `m`. -/
@[expose] def splitBox (b : BoxI) (d : Nat) (m : Int) : BoxI × BoxI :=
  match d with
  | 0 => ({ b with a1 := m }, { b with a0 := m })
  | 1 => ({ b with b1 := m }, { b with b0 := m })
  | 2 => ({ b with r1 := m }, { b with r0 := m })
  | 3 => ({ b with o11 := m }, { b with o10 := m })
  | 4 => ({ b with o21 := m }, { b with o20 := m })
  | _ => ({ b with t1 := m }, { b with t0 := m })

/-- Certify that box `b` violates the quadratic Schur pair inequality for sign `sigPos`. -/
@[expose] def chkSchur (b : BoxI) (sigPos : Bool) : Bool :=
  let sig : Int := if sigPos then 1 else -1
  let a1 : Ival := ⟨c2I - b.a1, c2I - b.a0⟩
  let d1 : Ival := ⟨c2I - b.b1, c2I - b.b0⟩
  let a2 : Ival := ⟨c2I + b.a0, c2I + b.a1⟩
  let d2 : Ival := ⟨c2I + b.b0, c2I + b.b1⟩
  let rb : Ival := ⟨b.r0, b.r1⟩
  let t : Ival := ⟨b.t0, b.t1⟩
  let o1 : Ival := ⟨b.o10, b.o11⟩
  let o2 : Ival := ⟨b.o20, b.o21⟩
  bindIval (ivAdd (ivScaleInt 15 rb) (ivScaleInt (sig * 16) t)) fun m11 =>
  bindIval (ivAdd (ivScaleInt 15 t) (ivScaleInt (sig * 16) rb)) fun m22 =>
  bindIval (ivAdd (ivScaleInt 15 o2) (ivScaleInt (sig * 16) o1)) fun m12 =>
  bindIval (ivAdd (ivScaleInt 15 o1) (ivScaleInt (sig * 16) o2)) fun m21 =>
  bindIval (ivSub (ivMul a2 (ivSub (ivMul a1 d1) (ivDivInt (ivSq m11) 1225)))
    (ivMul a1 (ivDivInt (ivSq m21) 1225))) fun x1 =>
  bindIval (ivSub (ivMul a2 (ivSub (ivMul a1 d2) (ivDivInt (ivSq m12) 1225)))
    (ivMul a1 (ivDivInt (ivSq m22) 1225))) fun x2 =>
  bindIval (ivDivInt (ivAdd (ivMul a2 (ivMul (ivAbs m11) (ivAbs m12)))
    (ivMul a1 (ivMul (ivAbs m21) (ivAbs m22)))) 1225) fun y =>
  iblt 0 x1.lo && iblt 0 x2.lo && iblt (ivSq y).hi (ivMul x1 x2).lo

/-- Certify that no `4`-vector unit Gram matrix realizes any point in box `b`. -/
@[expose] def chkGram (b : BoxI) : Bool :=
  let sab : Ival := ⟨b.a0, b.a1⟩
  let scd : Ival := ⟨b.b0, b.b1⟩
  let rb : Ival := ⟨b.r0, b.r1⟩
  let o1 : Ival := ⟨b.o10, b.o11⟩
  let o2 : Ival := ⟨b.o20, b.o21⟩
  let t : Ival := ⟨b.t0, b.t1⟩
  bindIval (ivDivInt (ivAdd (ivConst certScale) sab) 2) fun vx =>
  bindIval (ivDivInt (ivAdd (ivConst certScale) scd) 2) fun vy =>
  bindIval (ivSub (ivMul vx vy) (ivSq rb)) fun dIv =>
  if iblt dIv.hi 0 then true
  else
    bindIval (ivDivInt (ivSub (ivConst certScale) sab) 2) fun h1a =>
    bindIval (ivDivInt (ivSub (ivConst certScale) scd) 2) fun h1b =>
    if iblt (ivMul h1a dIv).hi (ivMul (ivSq o1) vx).lo then true
    else if iblt (ivMul h1b dIv).hi (ivMul (ivSq o2) vy).lo then true
    else if iblt 0 dIv.lo then
      bindIval (ivSub h1a (ivDivPos (ivMul (ivSq o1) vx) dIv)) fun k00 =>
      bindIval (ivSub h1b (ivDivPos (ivMul (ivSq o2) vy) dIv)) fun k11 =>
      if iblt k00.hi 0 || iblt k11.hi 0 then true
      else
        bindIval (ivAdd t (ivDivPos (ivMul (ivMul o1 o2) rb) dIv)) fun k01 =>
        bindIval (ivMul ⟨imax 0 k00.lo, k00.hi⟩ ⟨imax 0 k11.lo, k11.hi⟩) fun prodK =>
        iblt prodK.hi (ivSq k01).lo
    else false

/-- Intermediate cross-correlation evaluations for `chkShep`. -/
structure ShepPre where
  /-- Upper bound on `arccos sab`. -/
  vaHi : Int
  /-- Upper bound on `arccos scd`. -/
  vbHi : Int
  /-- Lower bound on `sac` clamped to `[cminI, 1]`. -/
  s0 : Int
  /-- Lower bound on `sbd` clamped to `[cminI, 1]`. -/
  s1 : Int
  /-- Lower bound on `sad` clamped to `[cminI, 1]`. -/
  s2 : Int
  /-- Lower bound on `sbc` clamped to `[cminI, 1]`. -/
  s3 : Int
  /-- Upper bound on `arccos sac`. -/
  vc0 : Int
  /-- Upper bound on `arccos sbd`. -/
  vc1 : Int
  /-- Upper bound on `arccos sad`. -/
  vc2 : Int
  /-- Upper bound on `arccos sbc`. -/
  vc3 : Int

/-- Evaluate and validate monotone quadratic `arccos` bounds at lower endpoints of `b`. -/
@[expose] def shepPre (b : BoxI) (qa qb qc0 qc1 qc2 qc3 : QuadI) : Option ShepPre :=
  if iblt b.a0 qa.rmin || iblt b.b0 qb.rmin then none
  else if iblt (ivQslope qa (ivConst b.a0)).lo 0 ||
          iblt (ivQslope qb (ivConst b.b0)).lo 0 then none
  else
    bindIval (ivQeval qa (ivConst b.a0)) fun va =>
    bindIval (ivQeval qb (ivConst b.b0)) fun vb =>
    bindInt (imax 0 (b.o20 - b.o11)) fun dlo =>
    bindInt (imin certScale (imax cminI (b.r0 + b.o10 + b.o20 + b.t0))) fun s0 =>
    bindInt (imin certScale (imax cminI (b.r0 - b.o11 - b.o21 + b.t0))) fun s1 =>
    bindInt (imin certScale (imax cminI (b.r0 - (b.o21 - b.o10) - b.t1))) fun s2 =>
    bindInt (imin certScale (imax cminI (b.r0 + dlo - b.t1))) fun s3 =>
    if iblt s0 qc0.rmin || iblt (ivQslope qc0 (ivConst s0)).lo 0 ||
       iblt s1 qc1.rmin || iblt (ivQslope qc1 (ivConst s1)).lo 0 ||
       iblt s2 qc2.rmin || iblt (ivQslope qc2 (ivConst s2)).lo 0 ||
       iblt s3 qc3.rmin || iblt (ivQslope qc3 (ivConst s3)).lo 0 then none
    else
      bindInt (ivQeval qc0 (ivConst s0)).hi fun vc0 =>
      bindInt (ivQeval qc1 (ivConst s1)).hi fun vc1 =>
      bindInt (ivQeval qc2 (ivConst s2)).hi fun vc2 =>
      bindInt (ivQeval qc3 (ivConst s3)).hi fun vc3 =>
      some ⟨va.hi, vb.hi, s0, s1, s2, s3, vc0, vc1, vc2, vc3⟩

/-- Certify the matched-pair bound on `b` via one of the `12` linear Sheppard/inclusion modes. -/
@[expose] def chkShep (b : BoxI) (mode ia ib ic0 ic1 ic2 ic3 : Nat) : Bool :=
  match starQI ia, starQI ib, crossQI ic0, crossQI ic1, crossQI ic2, crossQI ic3 with
  | some qa, some qb, some qc0, some qc1, some qc2, some qc3 =>
    match shepPre b qa qb qc0 qc1 qc2 qc3 with
    | none => false
    | some sp =>
      bindInt (sp.vc0 + sp.vc1 + sp.vc2 + sp.vc3) fun c4 =>
      let lhsOpt : Option Int :=
        match mode with
        | 0 =>
          let sminAll := imin (imin sp.s0 sp.s1) (imin sp.s2 sp.s3)
          if iblt sminAll qc0.rmin || iblt certScale b.r0 ||
             iblt (ivQslope qc0 (ivConst b.r0)).lo 0 then none
          else
            bindIval (ivAdd (ivAdd (ivSq ⟨b.o10, b.o11⟩) (ivSq ⟨b.o20, b.o21⟩))
              (ivSq ⟨b.t0, b.t1⟩)) fun var4 =>
            bindIval (ivScaleInt 4 (ivSub (ivQeval qc0 (ivConst b.r0))
              (ivMul (ivConst qc0.c2) var4))) fun had =>
            some (3 * (sp.vaHi + sp.vbHi) + had.hi)
        | 1 => some (3 * (sp.vaHi + sp.vbHi) + c4)
        | 2 => some (4 * sp.vaHi + 2 * sp.vbHi + c4)
        | 3 => some (2 * sp.vaHi + 4 * sp.vbHi + c4)
        | 4 => some (3 * (sp.vaHi + sp.vbHi) + 2 * sp.vc1 + sp.vc2 + sp.vc3)
        | 5 => some (3 * (sp.vaHi + sp.vbHi) + 2 * sp.vc0 + sp.vc2 + sp.vc3)
        | 6 => some (3 * (sp.vaHi + sp.vbHi) + 2 * sp.vc3 + sp.vc0 + sp.vc1)
        | 7 => some (3 * (sp.vaHi + sp.vbHi) + 2 * sp.vc2 + sp.vc0 + sp.vc1)
        | 8 => some (4 * (sp.vaHi + sp.vbHi + sp.vc0))
        | 9 => some (4 * (sp.vaHi + sp.vbHi + sp.vc1))
        | 10 => some (4 * (sp.vaHi + sp.vbHi + sp.vc2))
        | 11 => some (4 * (sp.vaHi + sp.vbHi + sp.vc3))
        | _ => none
      match lhsOpt with
      | some lhs => ible (ivDivPos (ivConst lhs) (ivScaleInt 4 ivPi)).hi targetI
      | none => false
  | _, _, _, _, _, _ => false

/-- Maximize `sl * δ - curvLo * δ ^ 2` over `|δ| ≤ dmaxHi` for fixed integer slope `sl`. -/
@[expose] def bound1dPt (sl curvLo dmaxHi : Int) : Int :=
  bindInt (Int.natAbs sl) fun absSl =>
  bindInt (ivMul (ivConst absSl) (ivConst dmaxHi)).hi fun linHi =>
  if ible curvLo 0 then
    linHi + (ivMul (ivConst (-curvLo)) (ivSq (ivConst dmaxHi))).hi
  else
    bindInt (ivDivPos (ivSq (ivConst absSl)) (ivScaleInt 4 (ivConst curvLo))).hi fun vertHi =>
    imin linHi vertHi

/-- Maximize `s * δ - c * δ ^ 2` over `s ∈ sl`, `c ∈ curv`, and `|δ| ≤ dmaxHi`. -/
@[expose] def bound1dIv (sl curv : Ival) (dmaxHi : Int) : Int :=
  imax (bound1dPt sl.lo curv.lo dmaxHi) (bound1dPt sl.hi curv.lo dmaxHi)

/-- Validated stage-1a output (polynomial table lookups and `D` enclosure). -/
structure PlanarS1a where
  /-- Quadratic upper bound model for `arccos sab`. -/
  qa : QuadI
  /-- Quadratic upper bound model for `arccos scd`. -/
  qb : QuadI
  /-- Quadratic upper bound model for `arccos sac`. -/
  qc0 : QuadI
  /-- Quadratic upper bound model for `arccos sbd`. -/
  qc1 : QuadI
  /-- Quadratic upper bound model for `arccos sad`. -/
  qc2 : QuadI
  /-- Quadratic upper bound model for `arccos sbc`. -/
  qc3 : QuadI
  /-- Interval enclosure of `(1 + sab) / 2`. -/
  vx : Ival
  /-- Interval enclosure of `(1 + scd) / 2`. -/
  vy : Ival
  /-- Validated positive interval enclosure of `D = vx * vy - rb ^ 2`. -/
  dIv : Ival

/-- Validated stage-1 output (basic domain, `D`, `K_{ij}`, and `c_ex` check). -/
structure PlanarS1 where
  /-- Quadratic upper bound model for `arccos sab`. -/
  qa : QuadI
  /-- Quadratic upper bound model for `arccos scd`. -/
  qb : QuadI
  /-- Quadratic upper bound model for `arccos sac`. -/
  qc0 : QuadI
  /-- Quadratic upper bound model for `arccos sbd`. -/
  qc1 : QuadI
  /-- Quadratic upper bound model for `arccos sad`. -/
  qc2 : QuadI
  /-- Quadratic upper bound model for `arccos sbc`. -/
  qc3 : QuadI
  /-- Interval enclosure of `(1 + sab) / 2`. -/
  vx : Ival
  /-- Interval enclosure of `(1 + scd) / 2`. -/
  vy : Ival
  /-- Validated positive interval enclosure of `D`. -/
  dIv : Ival
  /-- Nonnegative-clamped enclosure of `K_{00}`. -/
  k00 : Ival
  /-- Nonnegative-clamped enclosure of `K_{11}`. -/
  k11 : Ival
  /-- Interval enclosure of `|K_{01}|`. -/
  absK01 : Ival
  /-- Interval enclosure of `K_{00} * K_{11}`. -/
  kk : Ival

/-- Validated stage-2a output (basic planar geometry before `cxU`/`ceU`). -/
structure PlanarS2a where
  /-- Interval enclosure of `o1 / D`. -/
  u1 : Ival
  /-- Interval enclosure of `o2 / D`. -/
  u2 : Ival
  /-- Interval enclosure of `u1 * rb`. -/
  x1 : Ival
  /-- Interval enclosure of `u2 * rb`. -/
  x2 : Ival
  /-- Interval enclosure of `u1 * u2 * vx * vy`. -/
  pIv : Ival
  /-- Interval enclosure of `1 - x1`. -/
  omx1 : Ival
  /-- Interval enclosure of `1 - x2`. -/
  omx2 : Ival
  /-- Interval enclosure of `1 + x1`. -/
  opx1 : Ival
  /-- Interval enclosure of `1 + x2`. -/
  opx2 : Ival
  /-- Positive interval enclosure of `(1 - x1) * (1 - x2) - pIv`. -/
  detM : Ival

/-- Validated stage-2 output (planar quadrilateral coefficients `cxU`, `ceU`, `cAB`). -/
structure PlanarS2 where
  /-- Interval enclosure of `o1 / D`. -/
  u1 : Ival
  /-- Interval enclosure of `o2 / D`. -/
  u2 : Ival
  /-- Interval enclosure of `u1 * rb`. -/
  x1 : Ival
  /-- Interval enclosure of `u2 * rb`. -/
  x2 : Ival
  /-- Interval enclosure of `u1 * u2 * vx * vy`. -/
  pIv : Ival
  /-- Interval enclosure of `1 - x1`. -/
  omx1 : Ival
  /-- Interval enclosure of `1 - x2`. -/
  omx2 : Ival
  /-- Positive interval enclosure of `(1 - x1) * (1 - x2) - pIv`. -/
  detM : Ival
  /-- Interval enclosure of `pairCxMax / o2`. -/
  cxU : Ival
  /-- Interval enclosure of swapped `pairCxMax / o1`. -/
  ceU : Ival
  /-- Interval enclosure of `1 - x1 ^ 2`. -/
  omx1sq : Ival
  /-- Interval enclosure of `(1 - x1 ^ 2) * (1 - x2 ^ 2)`. -/
  denX12 : Ival
  /-- Interval enclosure of `(1 - x1) * (1 - x2) * detM`. -/
  denO12 : Ival
  /-- Interval enclosure of `pairCAB`. -/
  cAB : Ival

/-- Box midpoint intervals and coordinate half-widths. -/
structure PlanarMid where
  /-- Midpoint interval of `sab`. -/
  aM : Ival
  /-- Midpoint interval of `scd`. -/
  bM : Ival
  /-- Midpoint interval of `rb`. -/
  rM : Ival
  /-- Midpoint interval of `o1`. -/
  o1M : Ival
  /-- Midpoint interval of `o2`. -/
  o2M : Ival
  /-- Midpoint interval of `tau0`. -/
  tM : Ival
  /-- Upper half-width of `sab`. -/
  daHi : Int
  /-- Upper half-width of `scd`. -/
  dbHi : Int
  /-- Upper half-width of `rb`. -/
  drHi : Int
  /-- Upper half-width of `o1`. -/
  do1Hi : Int
  /-- Upper half-width of `o2`. -/
  do2Hi : Int
  /-- Upper half-width of `tau0`. -/
  dtHi : Int

/-- Validated stage-3b output (`D` midpoint and `D^{-1/2}` secant bound). -/
structure PlanarS3b where
  /-- Midpoint interval of `(1 + sab) / 2`. -/
  vxM : Ival
  /-- Midpoint interval of `(1 + scd) / 2`. -/
  vyM : Ival
  /-- Midpoint interval of `D`. -/
  dM : Ival
  /-- Nonnegative secant slope bound `cInv` for `D ^ (-1 / 2)`. -/
  cInv : Ival
  /-- Secant upper bound value at `dM` for `D ^ (-1 / 2)`. -/
  invM : Ival
  /-- Maximum variation `cInv * |D - dM|` across the box. -/
  dLMax : Int

/-- Validated stage-3 output (box midpoints, `D^{-1/2}` secant, and `D^{-3/2}` tangent). -/
structure PlanarS3 where
  /-- Midpoint interval of `sab`. -/
  aM : Ival
  /-- Midpoint interval of `scd`. -/
  bM : Ival
  /-- Midpoint interval of `rb`. -/
  rM : Ival
  /-- Midpoint interval of `o1`. -/
  o1M : Ival
  /-- Midpoint interval of `o2`. -/
  o2M : Ival
  /-- Midpoint interval of `tau0`. -/
  tM : Ival
  /-- Upper half-width of `sab`. -/
  daHi : Int
  /-- Upper half-width of `scd`. -/
  dbHi : Int
  /-- Upper half-width of `rb`. -/
  drHi : Int
  /-- Upper half-width of `o1`. -/
  do1Hi : Int
  /-- Upper half-width of `o2`. -/
  do2Hi : Int
  /-- Upper half-width of `tau0`. -/
  dtHi : Int
  /-- Midpoint interval of `(1 + sab) / 2`. -/
  vxM : Ival
  /-- Midpoint interval of `(1 + scd) / 2`. -/
  vyM : Ival
  /-- Midpoint interval of `D`. -/
  dM : Ival
  /-- Secant slope bound for `D ^ (-1 / 2)`. -/
  cInv : Ival
  /-- Secant midpoint bound for `D ^ (-1 / 2)`. -/
  invM : Ival
  /-- Maximum secant variation `cInv * |D - dM|`. -/
  dLMax : Int
  /-- Tangent lower bound at `dM` for `D ^ (-3 / 2)`. -/
  gM : Ival
  /-- Tangent slope `3 / (2 * sm ^ 5)` for `D ^ (-3 / 2)`. -/
  gSl : Ival
  /-- Maximum deviation of `D ^ (-3 / 2)` from `gM`. -/
  gVarMax : Int

/-- Validated planar model (`out` or `in`) coefficients. -/
structure PlanarModel where
  /-- Midpoint coefficient of `K_{00}` in the planar volume bound. -/
  bK0M : Ival
  /-- Midpoint coefficient of `K_{11}` in the planar volume bound. -/
  bK1M : Ival
  /-- Midpoint bilinear cross-term coefficient in the planar volume bound. -/
  cExM : Ival
  /-- Linear slope of `K_{00}` term with respect to `o2`. -/
  bK0Sl : Ival
  /-- Linear slope of `K_{11}` term with respect to `o1`. -/
  bK1Sl : Ival
  /-- Remainder bound for `K_{00}` variation with `o2`. -/
  bK0Rem : Int
  /-- Remainder bound for `K_{11}` variation with `o1`. -/
  bK1Rem : Int
  /-- Linear slope of `cEx` with respect to `o1`. -/
  cExSl1 : Ival
  /-- Linear slope of `cEx` with respect to `o2`. -/
  cExSl2 : Ival
  /-- Quadratic curvature upper bound of `cEx` in `(o1, o2)`. -/
  cExCurv : Ival

/-- Certify that `st.cex` upper-bounds the correlated planar Gaussian expectation factor. -/
@[expose] def checkCexOk (st : PlanarStep) (absK01 kk : Ival) : Bool :=
  let one := ivConst certScale
  match st.cexMode with
  | 0 => ible certScale st.cex
  | 1 =>
    let kkLo := ivConst kk.lo
    bindIval (ivSub kkLo (ivConst (ivSq absK01).hi)) fun detKLo =>
    if ible detKLo.lo 0 then false
    else
      bindIval (ivMul (ivSq (ivDivPos (ivConst (2 * certScale)) ivPi)) kkLo) fun lhs =>
      bindIval (ivMul (ivSq (ivConst st.cex)) detKLo) fun rhs =>
      ible lhs.hi rhs.lo
  | 2 =>
    if iblt st.rhoLo 0 || iblt st.rhoHi st.rhoLo || iblt certScale st.rhoHi ||
       ible kk.lo 0 then false
    else if iblt (ivSq absK01).lo (ivMul (ivSq (ivConst st.rhoLo)) kk).hi ||
            iblt (ivMul (ivSq (ivConst st.rhoHi)) kk).lo (ivSq absK01).hi then false
    else
      bindIval (ivDivPos (ivConst (8 * certScale)) (ivScaleInt 3 ivPi)) fun c83pi =>
      let hCub (ri : Int) : Ival :=
        let r := ivConst ri
        let omr := ivSub one r
        bindIval (ivAdd omr (ivDivInt (ivSq r) 2)) fun q =>
        ivAdd r (ivMul c83pi (ivMul omr q))
      ible (hCub st.rhoLo).hi st.cex && ible (hCub st.rhoHi).hi st.cex
  | _ => false

/-- Stage 1a of `chkPlanar`: validate domain bounds, polynomial lookups, and `D` enclosure. -/
@[expose] def planarStage1a (b : BoxI) (st : PlanarStep) : Option PlanarS1a :=
  if iblt b.o10 0 || iblt b.o20 0 || iblt b.r0 cminI || iblt certScale b.a1 ||
     iblt certScale b.b1 || iblt certScale b.r1 then none
  else if iblt st.lam 0 || iblt st.lamM 0 || ible st.rxy 0 || ible st.slo 0 ||
          ible st.shi 0 || ible st.sm 0 || iblt st.cex 0 then none
  else
    match starQI st.ia, starQI st.ib, crossQI st.ic0, crossQI st.ic1,
          crossQI st.ic2, crossQI st.ic3 with
    | some qa, some qb, some qc0, some qc1, some qc2, some qc3 =>
      bindInt (imax 0 (b.o20 - b.o11)) fun dloB =>
      bindInt (imin certScale (imax cminI (b.r0 + b.o10 + b.o20 + b.t0))) fun s0 =>
      bindInt (imin certScale (imax cminI (b.r0 - b.o11 - b.o21 + b.t0))) fun s1 =>
      bindInt (imin certScale (imax cminI (b.r0 - (b.o21 - b.o10) - b.t1))) fun s2 =>
      bindInt (imin certScale (imax cminI (b.r0 + dloB - b.t1))) fun s3 =>
      if iblt b.a0 qa.rmin || iblt b.b0 qb.rmin || iblt s0 qc0.rmin || iblt s1 qc1.rmin ||
         iblt s2 qc2.rmin || iblt s3 qc3.rmin then none
      else
        let one := ivConst certScale
        let sab : Ival := ⟨b.a0, b.a1⟩
        let scd : Ival := ⟨b.b0, b.b1⟩
        let rb : Ival := ⟨b.r0, b.r1⟩
        bindIval (ivDivInt (ivAdd one sab) 2) fun vx =>
        bindIval (ivDivInt (ivAdd one scd) 2) fun vy =>
        if iblt (ivScaleInt 2 (ivSq rb)).lo (ivMul vx vy).hi then none
        else
          bindIval (ivSub (ivMul vx vy) (ivSq rb)) fun dIv =>
          let sloIv := ivConst st.slo
          let shiIv := ivConst st.shi
          let smIv := ivConst st.sm
          if ible dIv.lo 0 || iblt dIv.lo (ivSq sloIv).hi || iblt (ivSq shiIv).lo dIv.hi ||
             iblt (ivScaleInt 5 (ivSq smIv)).lo (ivScaleInt 3 dIv).hi then none
          else some ⟨qa, qb, qc0, qc1, qc2, qc3, vx, vy, dIv⟩
    | _, _, _, _, _, _ => none

/-- Stage 1 of `chkPlanar`: enclose `K_{ij}` and validate `checkCexOk`. -/
@[expose] def planarStage1 (b : BoxI) (st : PlanarStep) : Option PlanarS1 :=
  match planarStage1a b st with
  | none => none
  | some s1a =>
    let one := ivConst certScale
    let sab : Ival := ⟨b.a0, b.a1⟩
    let scd : Ival := ⟨b.b0, b.b1⟩
    let rb : Ival := ⟨b.r0, b.r1⟩
    let o1 : Ival := ⟨b.o10, b.o11⟩
    let o2 : Ival := ⟨b.o20, b.o21⟩
    let t : Ival := ⟨b.t0, b.t1⟩
    bindIval (ivDivInt (ivSub one sab) 2) fun h1a =>
    bindIval (ivDivInt (ivSub one scd) 2) fun h1b =>
    bindIval (ivMax (ivConst 0) (ivSub h1a (ivDivPos (ivMul (ivSq o1) s1a.vx) s1a.dIv))) fun k00 =>
    bindIval (ivMax (ivConst 0) (ivSub h1b (ivDivPos (ivMul (ivSq o2) s1a.vy) s1a.dIv))) fun k11 =>
    bindIval (ivAdd t (ivDivPos (ivMul (ivMul o1 o2) rb) s1a.dIv)) fun k01 =>
    bindIval (ivAbs k01) fun absK01 =>
    bindIval (ivMul k00 k11) fun kk =>
    if checkCexOk st absK01 kk then
      some ⟨s1a.qa, s1a.qb, s1a.qc0, s1a.qc1, s1a.qc2, s1a.qc3,
        s1a.vx, s1a.vy, s1a.dIv, k00, k11, absK01, kk⟩
    else none

/-- Stage 2a of `chkPlanar`: enclose reduced planar slopes `u1, u2, x1, x2` and `detM > 0`. -/
@[expose] def planarStage2a (b : BoxI) (s1 : PlanarS1) : Option PlanarS2a :=
  let one := ivConst certScale
  let rb : Ival := ⟨b.r0, b.r1⟩
  let o1 : Ival := ⟨b.o10, b.o11⟩
  let o2 : Ival := ⟨b.o20, b.o21⟩
  bindIval (ivDivPos o1 s1.dIv) fun u1 =>
  bindIval (ivDivPos o2 s1.dIv) fun u2 =>
  bindIval (ivMul u1 rb) fun x1 =>
  bindIval (ivMul u2 rb) fun x2 =>
  if ible certScale x1.hi || ible certScale x2.hi then none
  else
    bindIval (ivMul (ivMul u1 u2) (ivMul s1.vx s1.vy)) fun pIv =>
    bindIval (ivSub one x1) fun omx1 =>
    bindIval (ivSub one x2) fun omx2 =>
    bindIval (ivAdd one x1) fun opx1 =>
    bindIval (ivAdd one x2) fun opx2 =>
    bindIval (ivSub (ivMul omx1 omx2) pIv) fun detM =>
    if ible detM.lo 0 then none
    else some ⟨u1, u2, x1, x2, pIv, omx1, omx2, opx1, opx2, detM⟩

/-- Validated denominators for `calcCuOpt`. -/
structure CuDenoms where
  /-- Positive enclosure of `(1 + xb) * (1 - xa) ^ 2`. -/
  d1 : Ival
  /-- Positive enclosure of `(1 - xb) * (1 + xa) ^ 2`. -/
  d2 : Ival
  /-- Positive enclosure of `detM ^ 2`. -/
  d3 : Ival
  /-- Positive enclosure of `(1 - xa) * detM`. -/
  d4 : Ival

/-- Validate and enclose the four rational denominators of `pairCxp` and `pairCxm`. -/
@[expose] def calcCuDenoms (detM omxa omxb opxa opxb : Ival) : Option CuDenoms :=
  if ible opxa.lo 0 || ible opxb.lo 0 then none
  else
    bindIval (ivMul opxb (ivSq omxa)) fun d1 =>
    bindIval (ivMul omxb (ivSq opxa)) fun d2 =>
    bindIval (ivSq detM) fun d3 =>
    bindIval (ivMul omxa detM) fun d4 =>
    if ible d1.lo 0 || ible d2.lo 0 || ible d3.lo 0 || ible d4.lo 0 then none
    else some ⟨d1, d2, d3, d4⟩

/-- Enclose the normalized linear rational envelope `pairCxMax / o`. -/
@[expose] def calcCuOpt (vIv dIv detM omxa omxb opxa opxb : Ival) : Option Ival :=
  match calcCuDenoms detM omxa omxb opxa opxb with
  | none => none
  | some cd =>
    let one := ivConst certScale
    bindIval (ivAdd (ivAdd (ivDivPos one cd.d1) (ivDivPos one cd.d2))
      (ivAdd (ivDivPos omxb cd.d3) (ivDivPos one opxa))) fun wp =>
    bindIval (ivAdd (ivAdd (ivDivPos one cd.d2) (ivDivPos one cd.d1))
      (ivAdd (ivDivPos one opxb) (ivDivPos one cd.d4))) fun wm =>
    bindIval (ivDivPos (ivMul (ivDivInt vIv 2) (ivMax wp wm)) dIv) some

/-- Stage 2 of `chkPlanar`: enclose `cxU`, `ceU`, and `cAB = pairCAB`. -/
@[expose] def planarStage2 (b : BoxI) (s1 : PlanarS1) : Option PlanarS2 :=
  match planarStage2a b s1 with
  | none => none
  | some s2a =>
    match calcCuOpt s1.vy s1.dIv s2a.detM s2a.omx1 s2a.omx2 s2a.opx1 s2a.opx2,
          calcCuOpt s1.vx s1.dIv s2a.detM s2a.omx2 s2a.omx1 s2a.opx2 s2a.opx1 with
    | some cxU, some ceU =>
      let one := ivConst certScale
      bindIval (ivSub one (ivSq s2a.x1)) fun omx1sq =>
      bindIval (ivSub one (ivSq s2a.x2)) fun omx2sq =>
      bindIval (ivMul omx1sq omx2sq) fun denX12 =>
      bindIval (ivMul (ivMul s2a.omx1 s2a.omx2) s2a.detM) fun denO12 =>
      if ible denX12.lo 0 || ible denO12.lo 0 then none
      else
        bindIval (ivAdd (ivDivPos (ivConst (4 * certScale)) denX12)
          (ivDivPos s2a.pIv denO12)) fun cAB =>
        some ⟨s2a.u1, s2a.u2, s2a.x1, s2a.x2, s2a.pIv, s2a.omx1, s2a.omx2,
          s2a.detM, cxU, ceU, omx1sq, denX12, denO12, cAB⟩
    | _, _ => none

/-- Box midpoint intervals (first half of `PlanarMid`). -/
structure PlanarMidIv where
  /-- Midpoint interval of `sab`. -/
  aM : Ival
  /-- Midpoint interval of `scd`. -/
  bM : Ival
  /-- Midpoint interval of `rb`. -/
  rM : Ival
  /-- Midpoint interval of `o1`. -/
  o1M : Ival
  /-- Midpoint interval of `o2`. -/
  o2M : Ival
  /-- Midpoint interval of `tau0`. -/
  tM : Ival

/-- Enclose the six midpoint coordinates of box `b`. -/
@[expose] def planarMidCoords (b : BoxI) : Option PlanarMidIv :=
  bindIval (ivDivInt (ivConst (b.a0 + b.a1)) 2) fun aM =>
  bindIval (ivDivInt (ivConst (b.b0 + b.b1)) 2) fun bM =>
  bindIval (ivDivInt (ivConst (b.r0 + b.r1)) 2) fun rM =>
  bindIval (ivDivInt (ivConst (b.o10 + b.o11)) 2) fun o1M =>
  bindIval (ivDivInt (ivConst (b.o20 + b.o21)) 2) fun o2M =>
  bindIval (ivDivInt (ivConst (b.t0 + b.t1)) 2) fun tM =>
  some ⟨aM, bM, rM, o1M, o2M, tM⟩

/-- Enclose midpoints and upper half-widths of all six coordinates of box `b`. -/
@[expose] def planarMid (b : BoxI) : Option PlanarMid :=
  match planarMidCoords b with
  | none => none
  | some mc =>
    bindInt (cdiv (b.a1 - b.a0) 2) fun daHi =>
    bindInt (cdiv (b.b1 - b.b0) 2) fun dbHi =>
    bindInt (cdiv (b.r1 - b.r0) 2) fun drHi =>
    bindInt (cdiv (b.o11 - b.o10) 2) fun do1Hi =>
    bindInt (cdiv (b.o21 - b.o20) 2) fun do2Hi =>
    bindInt (cdiv (b.t1 - b.t0) 2) fun dtHi =>
    some ⟨mc.aM, mc.bM, mc.rM, mc.o1M, mc.o2M, mc.tM, daHi, dbHi, drHi, do1Hi, do2Hi, dtHi⟩

/-- Stage 3b of `chkPlanar`: enclose `dM` and secant parameters for `D ^ (-1 / 2)`. -/
@[expose] def planarStage3b (st : PlanarStep) (s1 : PlanarS1) (pm : PlanarMid) : Option PlanarS3b :=
  let one := ivConst certScale
  let sloIv := ivConst st.slo
  let shiIv := ivConst st.shi
  bindIval (ivDivInt (ivAdd one pm.aM) 2) fun vxM =>
  bindIval (ivDivInt (ivAdd one pm.bM) 2) fun vyM =>
  bindIval (ivSub (ivMul vxM vyM) (ivSq pm.rM)) fun dM =>
  bindInt (ivDivPos one (ivMul (ivMul sloIv shiIv) (ivAdd sloIv shiIv))).lo fun cInvLo =>
  let cInv := ivConst (imax 0 cInvLo)
  bindIval (ivSub (ivDivPos one sloIv) (ivMul cInv (ivSub dM (ivConst s1.dIv.lo)))) fun invM =>
  bindInt (ivMul cInv (ivAbs (ivSub s1.dIv dM))).hi fun dLMax =>
  some ⟨vxM, vyM, dM, cInv, invM, dLMax⟩

/-- Stage 3 of `chkPlanar`: combine box midpoints with `D ^ (-1 / 2)` and `D ^ (-3 / 2)` models. -/
@[expose] def planarStage3 (b : BoxI) (st : PlanarStep) (s1 : PlanarS1) : Option PlanarS3 :=
  match planarMid b with
  | none => none
  | some pm =>
    match planarStage3b st s1 pm with
    | none => none
    | some sb =>
      let one := ivConst certScale
      let smIv := ivConst st.sm
      bindIval (ivSq smIv) fun sm2 =>
      bindIval (ivMul (ivMul sm2 sm2) smIv) fun sm5 =>
      if ible sm5.hi 0 then none
      else
        bindInt (ivDivPos one (ivScaleInt 2 sm5)).lo fun inv2sm5Lo =>
        let inv2sm5 := ivConst (imax 0 inv2sm5Lo)
        bindIval (ivMul inv2sm5 (ivSub (ivScaleInt 5 sm2) (ivScaleInt 3 sb.dM))) fun gM =>
        bindIval (ivScaleInt 3 inv2sm5) fun gSl =>
        if iblt gM.lo 0 then none
        else
          let sRange : Ival := ⟨st.slo, st.shi⟩
          bindIval (ivMul (ivSq sRange) sRange) fun sRange3 =>
          if ible sRange3.lo 0 then none
          else
            bindIval (ivDivPos one sRange3) fun gRange =>
            bindInt (ivAbs (ivSub gRange gM)).hi fun gVarMax =>
            some ⟨pm.aM, pm.bM, pm.rM, pm.o1M, pm.o2M, pm.tM,
              pm.daHi, pm.dbHi, pm.drHi, pm.do1Hi, pm.do2Hi, pm.dtHi,
              sb.vxM, sb.vyM, sb.dM, sb.cInv, sb.invM, sb.dLMax, gM, gSl, gVarMax⟩

/-- First half of `planarModelOut`. -/
structure ModelOut1 where
  /-- Midpoint enclosure of `cxU.hi * o2M`. -/
  bK0M : Ival
  /-- Midpoint enclosure of `ceU.hi * o1M`. -/
  bK1M : Ival
  /-- Midpoint of `K_{00} / √D`. -/
  mK0 : Int
  /-- Half-width of `K_{00} / √D`. -/
  vK0 : Int
  /-- Midpoint of `K_{11} / √D`. -/
  mK1 : Int
  /-- Half-width of `K_{11} / √D`. -/
  vK1 : Int

/-- First stage of exterior planar model (`isIn = false`). -/
@[expose] def planarModelOut1 (st : PlanarStep) (s1 : PlanarS1) (s2 : PlanarS2)
    (s3 : PlanarS3) : Option ModelOut1 :=
  let sRange : Ival := ⟨st.slo, st.shi⟩
  bindIval (ivMul (ivConst s2.cxU.hi) s3.o2M) fun bK0M =>
  bindIval (ivMul (ivConst s2.ceU.hi) s3.o1M) fun bK1M =>
  bindIval (ivDivPos s1.k00 sRange) fun k0S =>
  bindIval (ivDivPos s1.k11 sRange) fun k1S =>
  bindInt ((k0S.lo + k0S.hi) / 2) fun mK0 =>
  bindInt (cdiv (k0S.hi - k0S.lo) 2) fun vK0 =>
  bindInt ((k1S.lo + k1S.hi) / 2) fun mK1 =>
  bindInt (cdiv (k1S.hi - k1S.lo) 2) fun vK1 =>
  some ⟨bK0M, bK1M, mK0, vK0, mK1, vK1⟩

/-- Second half of `planarModelOut`. -/
structure ModelOut2 where
  /-- Linear slope of exterior `K_{00}` term in `o2`. -/
  bK0Sl : Ival
  /-- Linear slope of exterior `K_{11}` term in `o1`. -/
  bK1Sl : Ival
  /-- Bilinear remainder for `K_{00}` variation with `o2`. -/
  bK0Rem : Int
  /-- Bilinear remainder for `K_{11}` variation with `o1`. -/
  bK1Rem : Int
  /-- Upper bound on quadratic `(o1 ^ 2 + o2 ^ 2)` coefficient of `pairCAB`. -/
  cXsqHi : Int
  /-- Upper bound on bilinear `o1 * o2` coefficient of `pairCAB`. -/
  cO12Hi : Int

/-- Second stage of exterior planar model (`isIn = false`). -/
@[expose] def planarModelOut2 (b : BoxI) (s1 : PlanarS1) (s2 : PlanarS2) (s3 : PlanarS3)
    (m1 : ModelOut1) : Option ModelOut2 :=
  let fourPi := ivScaleInt 4 ivPi
  let rb : Ival := ⟨b.r0, b.r1⟩
  bindIval (ivDivPos (ivMul (ivConst s2.cxU.hi) (ivConst m1.mK0)) fourPi) fun bK0Sl =>
  bindIval (ivDivPos (ivMul (ivConst s2.ceU.hi) (ivConst m1.mK1)) fourPi) fun bK1Sl =>
  bindInt (ivDivPos (ivMul (ivMul (ivConst s2.cxU.hi) (ivConst m1.vK0))
    (ivConst s3.do2Hi)) fourPi).hi fun bK0Rem =>
  bindInt (ivDivPos (ivMul (ivMul (ivConst s2.ceU.hi) (ivConst m1.vK1))
    (ivConst s3.do1Hi)) fourPi).hi fun bK1Rem =>
  bindIval (ivSq s1.dIv) fun dSq =>
  if ible dSq.lo 0 then none
  else
    bindInt (ivDivPos (ivMul (ivDivPos (ivConst (4 * certScale)) s2.denX12) (ivSq rb)) dSq).hi
      fun cXsqHi =>
    bindInt (ivDivPos (ivDivPos (ivMul s1.vx s1.vy) dSq) s2.denO12).hi fun cO12Hi =>
    some ⟨bK0Sl, bK1Sl, bK0Rem, bK1Rem, cXsqHi, cO12Hi⟩

/-- Assemble validated exterior planar volume model (`volume_planarRectSet_le_out`). -/
@[expose] def planarModelOut (b : BoxI) (st : PlanarStep) (s1 : PlanarS1) (s2 : PlanarS2)
    (s3 : PlanarS3) : Option PlanarModel :=
  match planarModelOut1 st s1 s2 s3 with
  | none => none
  | some m1 =>
    match planarModelOut2 b s1 s2 s3 m1 with
    | none => none
    | some m2 =>
      let cXsq := ivConst m2.cXsqHi
      let cO12 := ivConst m2.cO12Hi
      bindIval (ivAdd (ivConst (4 * certScale))
        (ivAdd (ivMul cXsq (ivAdd (ivSq s3.o1M) (ivSq s3.o2M)))
          (ivMul cO12 (ivMul s3.o1M s3.o2M)))) fun cExM =>
      bindIval (ivAdd (ivScaleInt 2 (ivMul cXsq s3.o1M)) (ivMul cO12 s3.o2M)) fun cExSl1 =>
      bindIval (ivAdd (ivScaleInt 2 (ivMul cXsq s3.o2M)) (ivMul cO12 s3.o1M)) fun cExSl2 =>
      bindIval (ivAdd cXsq (ivDivInt cO12 2)) fun cExCurv =>
      some ⟨m1.bK0M, m1.bK1M, cExM, m2.bK0Sl, m2.bK1Sl, m2.bK0Rem, m2.bK1Rem,
        cExSl1, cExSl2, cExCurv⟩

/-- First stage of `planarModelIn`. -/
structure ModelIn1 where
  /-- Positive enclosure of `detM - pIv`. -/
  detM2 : Ival
  /-- Positive enclosure of `pairQp * pairQm`. -/
  qpQm : Ival
  /-- Upper bound on `pairCxe`. -/
  cExMHi : Int

/-- First stage of interior planar model (`isIn = true`). -/
@[expose] def planarModelIn1 (b : BoxI) (st : PlanarStep) (s1 : PlanarS1)
    (s2 : PlanarS2) : Option ModelIn1 :=
  let one := ivConst certScale
  let rb : Ival := ⟨b.r0, b.r1⟩
  let o1 : Ival := ⟨b.o10, b.o11⟩
  bindIval (ivSub s2.detM s2.pIv) fun detM2 =>
  bindIval (ivSub s1.kk (ivSq s1.absK01)) fun detK =>
  if ible detM2.lo 0 || ible detK.lo 0 || ible st.invSdetK 0 then none
  else if iblt (ivMul (ivSq (ivConst st.invSdetK)) detK).lo one.lo then none
  else
    bindIval (ivMul (ivSq s2.u2) (ivSq (ivAdd rb o1))) fun s2Iv =>
    bindIval (ivSub (ivSq s2.omx1) s2Iv) fun qp =>
    bindIval (ivSub (ivSq s2.omx1sq)
      (ivScaleInt 2 (ivMul (ivAdd one (ivSq s2.x1)) s2Iv))) fun qpQm =>
    if ible qp.lo 0 || ible qpQm.lo 0 then none
    else
      bindIval (ivMax (ivConst 0) (ivSub rb (ivConst b.o11))) fun rbo1Pos =>
      bindIval (ivSub (ivScaleInt 4 s2.omx1sq)
        (ivScaleInt 4 (ivMul (ivConst (ivSq s2.u2).lo) (ivConst (ivSq rbo1Pos).lo))))
        fun numCxe =>
      bindInt (ivDivPos numCxe qpQm).hi fun cExMHi =>
      some ⟨detM2, qpQm, cExMHi⟩

/-- Second stage of `planarModelIn`. -/
structure ModelIn2 where
  /-- Interval enclosure of `pairAbsCx2`. -/
  acx : Ival
  /-- Interval enclosure of `pairAbsCe2`. -/
  ace : Ival
  /-- Interval enclosure of interior `ξ` cutoff ratio `k2`. -/
  k2 : Ival
  /-- Interval enclosure of interior `η` cutoff ratio `k1`. -/
  k1 : Ival
  /-- Interval enclosure of `cxU * o2`. -/
  cxmB : Ival
  /-- Interval enclosure of `ceU * o1`. -/
  cemB : Ival
  /-- Nonnegative-clamped enclosure of `cAB - 4`. -/
  cabM4 : Ival

/-- Second stage of interior planar model (`isIn = true`). -/
@[expose] def planarModelIn2 (b : BoxI) (s1 : PlanarS1) (s2 : PlanarS2)
    (mi1 : ModelIn1) : Option ModelIn2 :=
  let one := ivConst certScale
  let rb : Ival := ⟨b.r0, b.r1⟩
  let o1 : Ival := ⟨b.o10, b.o11⟩
  let o2 : Ival := ⟨b.o20, b.o21⟩
  bindIval (ivMul s2.u1 s2.u2) fun u1u2 =>
  bindIval (ivDivPos (ivScaleInt 4
    (ivMul (ivMul u1u2 (ivMul rb s1.vy)) (ivAdd one (ivMul (ivSq s2.u2) s1.dIv)))) mi1.qpQm)
    fun acx =>
  bindIval (ivDivPos (ivScaleInt 4
    (ivMul (ivMul u1u2 (ivMul rb s1.vx)) (ivAdd one (ivMul (ivSq s2.u1) s1.dIv)))) mi1.qpQm)
    fun ace =>
  bindIval (ivDivPos (ivMul (ivMul s2.u2 s1.vy) s2.omx2) mi1.detM2) fun k2 =>
  bindIval (ivDivPos (ivMul (ivMul s2.u1 s1.vx) s2.omx1) mi1.detM2) fun k1 =>
  bindIval (ivMul s2.cxU o2) fun cxmB =>
  bindIval (ivMul s2.ceU o1) fun cemB =>
  bindIval (ivMax (ivConst 0) (ivSub s2.cAB (ivConst (4 * certScale)))) fun cabM4 =>
  some ⟨acx, ace, k2, k1, cxmB, cemB, cabM4⟩

/-- Assemble validated interior planar volume model (`volume_planarRectSet_le_in`). -/
@[expose] def planarModelIn (b : BoxI) (st : PlanarStep) (s1 : PlanarS1)
    (s2 : PlanarS2) : Option PlanarModel :=
  match planarModelIn1 b st s1 s2 with
  | none => none
  | some mi1 =>
    match planarModelIn2 b s1 s2 mi1 with
    | none => none
    | some mi2 =>
      bindIval (ivAdd mi2.cxmB (ivAdd (ivMul mi2.cabM4 mi2.k2)
        (ivMul mi2.cemB (ivSq mi2.k2)))) fun tcx =>
      bindIval (ivAdd mi2.cemB (ivAdd (ivMul mi2.cabM4 mi2.k1)
        (ivMul mi2.cxmB (ivSq mi2.k1)))) fun tce =>
      bindIval (ivMul (ivDivPos (ivScaleInt 4 (ivMul mi2.k2 s1.k00)) ivPi)
        (ivConst st.invSdetK)) fun facX =>
      bindIval (ivMul (ivDivPos (ivScaleInt 4 (ivMul mi2.k1 s1.k11)) ivPi)
        (ivConst st.invSdetK)) fun facE =>
      bindInt (ivAdd mi2.acx (ivMul tcx facX)).hi fun bK0MHi =>
      bindInt (ivAdd mi2.ace (ivMul tce facE)).hi fun bK1MHi =>
      let zIv := ivConst 0
      some ⟨ivConst bK0MHi, ivConst bK1MHi, ivConst mi1.cExMHi,
        zIv, zIv, 0, 0, zIv, zIv, zIv⟩

/-- Dispatch to `planarModelOut` (`isIn = false`) or `planarModelIn` (`isIn = true`). -/
@[expose] def planarStageModel (b : BoxI) (st : PlanarStep) (s1 : PlanarS1) (s2 : PlanarS2)
    (s3 : PlanarS3) : Option PlanarModel :=
  if !st.isIn then planarModelOut b st s1 s2 s3
  else planarModelIn b st s1 s2

/-- First half of `planarStage4`. -/
structure PlanarS4a where
  /-- Point interval upper-bounding `1 / rxy`. -/
  invRxyIv : Ival
  /-- Combined AM-GM weight `ck0` on `K_{00}`. -/
  ck0 : Ival
  /-- Combined AM-GM weight `ck1` on `K_{11}`. -/
  ck1 : Ival
  /-- Midpoint enclosure of `o1M ^ 2 * vxM`. -/
  f1M : Ival
  /-- Midpoint enclosure of `o2M ^ 2 * vyM`. -/
  f2M : Ival
  /-- Midpoint planar rectangle contribution divided by `4π`. -/
  rectM : Ival
  /-- Sensitivity coefficient `cD` with respect to `D - dM`. -/
  cD : Ival

/-- Validated stage-4 output. -/
structure PlanarS4 where
  /-- Combined AM-GM weight `ck0` on `K_{00}`. -/
  ck0 : Ival
  /-- Combined AM-GM weight `ck1` on `K_{11}`. -/
  ck1 : Ival
  /-- Midpoint planar rectangle contribution divided by `4π`. -/
  rectM : Ival
  /-- Sensitivity coefficient `cD` with respect to `D - dM`. -/
  cD : Ival
  /-- Total higher-order bilinear remainder across box `b`. -/
  remBilin : Int
  /-- Interval `[0, cSKK]` multiplying signed `cEx` slopes. -/
  cSKKIv : Ival
  /-- Point interval `[cSKK, cSKK]` multiplying quadratic `cEx` curvature. -/
  cSKKHi : Ival

/-- Stage 4a of `chkPlanar`: assemble midpoint rectangle weight `rectM` and `D`-slope `cD`. -/
@[expose] def planarStage4a (st : PlanarStep) (s3 : PlanarS3)
    (md : PlanarModel) : Option PlanarS4a :=
  let one := ivConst certScale
  let fourPi := ivScaleInt 4 ivPi
  let rxyIv := ivConst st.rxy
  bindInt (ivDivPos one rxyIv).hi fun invRxy =>
  let invRxyIv := ivConst invRxy
  bindInt (ivMul (ivConst md.cExM.hi) (ivConst st.cex)).hi fun cExP =>
  let cExProd := ivConst cExP
  bindInt (ivAdd md.bK0M (ivDivInt (ivMul cExProd rxyIv) 2)).hi fun ck0H =>
  bindInt (ivAdd md.bK1M (ivDivInt (ivMul cExProd invRxyIv) 2)).hi fun ck1H =>
  let ck0 := ivConst ck0H
  let ck1 := ivConst ck1H
  bindIval (ivAdd (ivMul ck0 (ivDivInt (ivSub one s3.aM) 2))
    (ivMul ck1 (ivDivInt (ivSub one s3.bM) 2))) fun nM =>
  bindIval (ivMul (ivSq s3.o1M) s3.vxM) fun f1M =>
  bindIval (ivMul (ivSq s3.o2M) s3.vyM) fun f2M =>
  bindIval (ivAdd (ivMul ck0 f1M) (ivMul ck1 f2M)) fun fM =>
  bindIval (ivDivPos (ivSub (ivMul nM s3.invM) (ivMul fM s3.gM)) fourPi) fun rectM =>
  bindIval (ivDivPos (ivSub (ivMul fM s3.gSl) (ivMul nM s3.cInv)) fourPi) fun cD =>
  some ⟨invRxyIv, ck0, ck1, f1M, f2M, rectM, cD⟩

/-- Stage 4 of `chkPlanar`: bound bilinear remainders and AM-GM cross factor `cSKK`. -/
@[expose] def planarStage4 (b : BoxI) (st : PlanarStep) (s1 : PlanarS1) (s3 : PlanarS3)
    (md : PlanarModel) : Option PlanarS4 :=
  match planarStage4a st s3 md with
  | none => none
  | some s4a =>
    let fourPi := ivScaleInt 4 ivPi
    let o1 : Ival := ⟨b.o10, b.o11⟩
    let o2 : Ival := ⟨b.o20, b.o21⟩
    let rxyIv := ivConst st.rxy
    bindInt (ivAbs (ivSub (ivMul (ivSq o1) s1.vx) s4a.f1M)).hi fun f1Var =>
    bindInt (ivAbs (ivSub (ivMul (ivSq o2) s1.vy) s4a.f2M)).hi fun f2Var =>
    bindInt (ivAbs (ivSub (ivSq o1) (ivSq s3.o1M))).hi fun o1SqVar =>
    bindInt (ivAbs (ivSub (ivSq o2) (ivSq s3.o2M))).hi fun o2SqVar =>
    bindIval (ivAdd (ivMul (ivDivInt (ivConst s3.daHi) 2) (ivConst s3.dLMax))
      (ivAdd (ivMul (ivConst f1Var) (ivConst s3.gVarMax))
        (ivMul (ivMul (ivDivInt (ivConst s3.daHi) 2) (ivConst o1SqVar)) s3.gM))) fun rem0 =>
    bindIval (ivAdd (ivMul (ivDivInt (ivConst s3.dbHi) 2) (ivConst s3.dLMax))
      (ivAdd (ivMul (ivConst f2Var) (ivConst s3.gVarMax))
        (ivMul (ivMul (ivDivInt (ivConst s3.dbHi) 2) (ivConst o2SqVar)) s3.gM))) fun rem1 =>
    bindInt ((ivDivPos (ivAdd (ivMul s4a.ck0 rem0) (ivMul s4a.ck1 rem1)) fourPi).hi +
      (ivMul (ivAbs s4a.cD) (ivDivInt (ivMul (ivConst s3.daHi) (ivConst s3.dbHi)) 4)).hi +
      md.bK0Rem + md.bK1Rem) fun remBilin =>
    bindInt (ivDivInt (ivAdd (ivMul rxyIv (ivConst s1.k00.hi))
      (ivMul s4a.invRxyIv (ivConst s1.k11.hi))) 2).hi fun sKKHi =>
    bindInt (ivDivPos (ivMul (ivConst st.cex) (ivConst sKKHi))
      (ivMul fourPi (ivConst st.slo))).hi fun cSKK =>
    some ⟨s4a.ck0, s4a.ck1, s4a.rectM, s4a.cD, remBilin, ⟨0, cSKK⟩, ivConst cSKK⟩

/-- Stage-5a output (Schur penalties and star midpoint evaluations). -/
structure PlanarS5a where
  /-- Upper bound on combined Schur Lagrange penalty at box midpoint. -/
  schPenHi : Int
  /-- Upper bound on `(qa(aM) + qb(bM)) / (2π)`. -/
  starMHi : Int
  /-- Negative derivative interval `-qa'(aM)`. -/
  saM : Ival
  /-- Negative derivative interval `-qb'(bM)`. -/
  sbM : Ival

/-- Stage 5a of `chkPlanar`: evaluate Schur penalties and intra-star midpoint values/slopes. -/
@[expose] def planarStage5a (b : BoxI) (st : PlanarStep) (s1 : PlanarS1)
    (s3 : PlanarS3) : Option PlanarS5a :=
  let twoPi := ivScaleInt 2 ivPi
  bindInt (if iblt 0 st.lam then calcSchurRhsHi b 1 else 0) fun srP =>
  bindInt (if iblt 0 st.lamM then calcSchurRhsHi b (-1) else 0) fun srM =>
  if (iblt 0 st.lam && iblt srP 0) || (iblt 0 st.lamM && iblt srM 0) then none
  else
    bindInt (if iblt 0 st.lam then
        let linP := ivAdd
          (ivSub (ivAdd (ivDivInt (ivAdd s3.aM s3.bM) 2)
            (ivAdd (ivDivInt (ivScaleInt 3 s3.rM) 7)
              (ivDivInt (ivScaleInt 16 s3.tM) 35))) (ivConst c2I))
          (ivConst srP)
        (ivMul (ivConst st.lam) linP).hi
      else 0) fun schP =>
    bindInt (if iblt 0 st.lamM then
        let linM := ivAdd
          (ivSub (ivAdd (ivDivInt (ivAdd s3.aM s3.bM) 2)
            (ivAdd (ivDivInt (ivScaleInt 3 s3.rM) 7)
              (ivDivInt (ivScaleInt (-16) s3.tM) 35))) (ivConst c2I))
          (ivConst srM)
        (ivMul (ivConst st.lamM) linM).hi
      else 0) fun schM =>
    bindInt (schP + schM) fun schPenHi =>
    bindInt (ivDivPos (ivAdd (ivQeval s1.qa s3.aM) (ivQeval s1.qb s3.bM)) twoPi).hi
      fun starMHi =>
    bindIval (ivQslope s1.qa s3.aM) fun saM =>
    bindIval (ivQslope s1.qb s3.bM) fun sbM =>
    some ⟨schPenHi, starMHi, saM, sbM⟩

/-- Stage-5b1 output (cross-correlation midpoints and value sum). -/
structure PlanarS5b1 where
  /-- Midpoint interval of `sac`. -/
  sacM : Ival
  /-- Midpoint interval of `sbd`. -/
  sbdM : Ival
  /-- Midpoint interval of `sad`. -/
  sadM : Ival
  /-- Midpoint interval of `sbc`. -/
  sbcM : Ival
  /-- Upper bound on `(qc0(sacM) + qc1(sbdM) + qc2(sadM) + qc3(sbcM)) / (4π)`. -/
  crossMHi : Int

/-- Stage 5b1 of `chkPlanar`: evaluate cross-edge quadratic models at box midpoints. -/
@[expose] def planarStage5b1 (s1 : PlanarS1) (s3 : PlanarS3) : Option PlanarS5b1 :=
  let fourPi := ivScaleInt 4 ivPi
  bindIval (ivAdd (ivAdd s3.rM s3.o1M) (ivAdd s3.o2M s3.tM)) fun sacM =>
  bindIval (ivAdd (ivSub s3.rM s3.o1M) (ivSub s3.tM s3.o2M)) fun sbdM =>
  bindIval (ivSub (ivAdd s3.rM s3.o1M) (ivAdd s3.o2M s3.tM)) fun sadM =>
  bindIval (ivSub (ivSub s3.rM s3.o1M) (ivSub s3.tM s3.o2M)) fun sbcM =>
  bindIval (ivAdd (ivAdd (ivQeval s1.qc0 sacM) (ivQeval s1.qc1 sbdM))
    (ivAdd (ivQeval s1.qc2 sadM) (ivQeval s1.qc3 sbcM))) fun crossSum =>
  bindInt (ivDivPos crossSum fourPi).hi fun crossMHi =>
  some ⟨sacM, sbdM, sadM, sbcM, crossMHi⟩

/-- Stage-5b output (cross-correlation slopes and minimum curvature). -/
structure PlanarS5b where
  /-- Upper bound on midpoint cross-edge `arccos` sum divided by `4π`. -/
  crossMHi : Int
  /-- Minimum quadratic curvature `min(qc0.c2, qc1.c2, qc2.c2, qc3.c2)`. -/
  c2Min : Int
  /-- Negative derivative interval `-qc0'(sacM)`. -/
  slc0 : Ival
  /-- Negative derivative interval `-qc1'(sbdM)`. -/
  slc1 : Ival
  /-- Negative derivative interval `-qc2'(sadM)`. -/
  slc2 : Ival
  /-- Negative derivative interval `-qc3'(sbcM)`. -/
  slc3 : Ival

/-- Stage 5b of `chkPlanar`: enclose cross-edge slopes and minimum concavity `c2Min`. -/
@[expose] def planarStage5b (s1 : PlanarS1) (s3 : PlanarS3) : Option PlanarS5b :=
  match planarStage5b1 s1 s3 with
  | none => none
  | some sb1 =>
    bindIval (ivQslope s1.qc0 sb1.sacM) fun slc0 =>
    bindIval (ivQslope s1.qc1 sb1.sbdM) fun slc1 =>
    bindIval (ivQslope s1.qc2 sb1.sadM) fun slc2 =>
    bindIval (ivQslope s1.qc3 sb1.sbcM) fun slc3 =>
    bindInt (imin (imin s1.qc0.c2 s1.qc1.c2) (imin s1.qc2.c2 s1.qc3.c2)) fun c2Min =>
    some ⟨sb1.crossMHi, c2Min, slc0, slc1, slc2, slc3⟩

/-- Stage-5c output (directional slope intervals along all `6` coordinates). -/
structure PlanarS5c where
  /-- Total directional slope interval with respect to `sab - aM`. -/
  slA : Ival
  /-- Total directional slope interval with respect to `scd - bM`. -/
  slB : Ival
  /-- Total directional slope interval with respect to `rb - rM`. -/
  slR : Ival
  /-- Total directional slope interval with respect to `o1 - o1M`. -/
  slO1 : Ival
  /-- Total directional slope interval with respect to `o2 - o2M`. -/
  slO2 : Ival
  /-- Total directional slope interval with respect to `tau0 - tM`. -/
  slT : Ival

/-- Stage 5c of `chkPlanar`: assemble directional slope intervals along all `6` coordinates. -/
@[expose] def planarStage5c (st : PlanarStep) (s3 : PlanarS3) (md : PlanarModel)
    (s4 : PlanarS4) (s5a : PlanarS5a) (s5b : PlanarS5b) : Option PlanarS5c :=
  let twoPi := ivScaleInt 2 ivPi
  let fourPi := ivScaleInt 4 ivPi
  let lamSum := ivConst (st.lam + st.lamM)
  let lamDiff := ivConst (st.lam - st.lamM)
  bindIval (ivAdd (ivNeg (ivDivPos s5a.saM twoPi))
    (ivAdd (ivNeg (ivDivPos (ivDivInt (ivAdd (ivMul s4.ck0 s3.invM)
      (ivMul (ivMul s4.ck0 (ivSq s3.o1M)) s3.gM)) 2) fourPi))
      (ivAdd (ivMul s4.cD (ivDivInt s3.vyM 2)) (ivDivInt lamSum 2)))) fun slA =>
  bindIval (ivAdd (ivNeg (ivDivPos s5a.sbM twoPi))
    (ivAdd (ivNeg (ivDivPos (ivDivInt (ivAdd (ivMul s4.ck1 s3.invM)
      (ivMul (ivMul s4.ck1 (ivSq s3.o2M)) s3.gM)) 2) fourPi))
      (ivAdd (ivMul s4.cD (ivDivInt s3.vxM 2)) (ivDivInt lamSum 2)))) fun slB =>
  bindIval (ivAdd (ivSub (ivNeg (ivDivPos
    (ivAdd (ivAdd s5b.slc0 s5b.slc1) (ivAdd s5b.slc2 s5b.slc3)) fourPi))
    (ivScaleInt 2 (ivMul s4.cD s3.rM)))
    (ivDivInt (ivScaleInt 3 lamSum) 7)) fun slR =>
  bindIval (ivAdd (ivSub (ivNeg (ivDivPos
    (ivAdd (ivSub s5b.slc0 s5b.slc1) (ivSub s5b.slc2 s5b.slc3)) fourPi))
    (ivDivPos (ivScaleInt 2 (ivMul s4.ck0 (ivMul s3.o1M (ivMul s3.vxM s3.gM)))) fourPi))
    (ivAdd md.bK1Sl (ivMul md.cExSl1 s4.cSKKIv))) fun slO1 =>
  bindIval (ivAdd (ivSub (ivNeg (ivDivPos
    (ivSub (ivSub s5b.slc0 s5b.slc1) (ivSub s5b.slc2 s5b.slc3)) fourPi))
    (ivDivPos (ivScaleInt 2 (ivMul s4.ck1 (ivMul s3.o2M (ivMul s3.vyM s3.gM)))) fourPi))
    (ivAdd md.bK0Sl (ivMul md.cExSl2 s4.cSKKIv))) fun slO2 =>
  bindIval (ivAdd (ivNeg (ivDivPos
    (ivSub (ivAdd s5b.slc0 s5b.slc1) (ivAdd s5b.slc2 s5b.slc3)) fourPi))
    (ivDivInt (ivScaleInt 16 lamDiff) 35)) fun slT =>
  some ⟨slA, slB, slR, slO1, slO2, slT⟩

/-- Stage 5 of `chkPlanar`: sum midpoint value, remainders, and `1`D coordinate variations. -/
@[expose] def planarStage5 (b : BoxI) (st : PlanarStep) (s1 : PlanarS1) (s3 : PlanarS3)
    (md : PlanarModel) (s4 : PlanarS4) : Bool :=
  match planarStage5a b st s1 s3 with
  | none => false
  | some s5a =>
    match planarStage5b s1 s3 with
    | none => false
    | some s5b =>
      match planarStage5c st s3 md s4 s5a s5b with
      | none => false
      | some s5c =>
        let twoPi := ivScaleInt 2 ivPi
        bindIval (ivDivPos (ivConst s5b.c2Min) ivPi) fun c2Pi =>
        bindIval (ivAdd c2Pi s4.cD) fun aR =>
        bindIval (ivSub c2Pi (ivMul md.cExCurv s4.cSKKHi)) fun aO =>
        bindInt (bound1dIv s5c.slA (ivDivPos (ivConst s1.qa.c2) twoPi) s3.daHi) fun mDa =>
        bindInt (bound1dIv s5c.slB (ivDivPos (ivConst s1.qb.c2) twoPi) s3.dbHi) fun mDb =>
        bindInt (bound1dIv s5c.slR aR s3.drHi) fun mDr =>
        bindInt (bound1dIv s5c.slO1 aO s3.do1Hi) fun mDo1 =>
        bindInt (bound1dIv s5c.slO2 aO s3.do2Hi) fun mDo2 =>
        bindInt (bound1dIv s5c.slT c2Pi s3.dtHi) fun mDt =>
        bindInt (s5a.starMHi + s5b.crossMHi + s4.rectM.hi + s4.remBilin + s5a.schPenHi +
          mDa + mDb + mDr + mDo1 + mDo2 + mDt) fun total =>
        ible total targetI

/-- Full staged verifier for a planar-volume leaf (`Step.planar st`) on box `b`. -/
@[expose] def chkPlanar (b : BoxI) (st : PlanarStep) : Bool :=
  match planarStage1 b st with
  | none => false
  | some s1 =>
    match planarStage2 b s1 with
    | none => false
    | some s2 =>
      match planarStage3 b st s1 with
      | none => false
      | some s3 =>
        match planarStageModel b st s1 s2 s3 with
        | none => false
        | some md =>
          match planarStage4 b st s1 s3 md with
          | none => false
          | some s4 => planarStage5 b st s1 s3 md s4

/-- Execute one certificate step on the box stack, popping all intermediate WHNF frames. -/
@[expose] def stepOne (subs : SubTree) (st : Step) : List BoxI → Option (List BoxI)
  | [] => none
  | cur :: stk =>
    match st with
    | .subbox idx =>
      match lookupSub subs idx with
      | some target => if boxEq cur target then some stk else none
      | none => none
    | .clamp =>
      match clampBox cur with
      | some cur' => some (cur' :: stk)
      | none => none
    | .empty => if isEmptyBox cur then some stk else none
    | .split d m =>
      if isEmptyBox cur then none
      else
        let (bL, bR) := splitBox cur d m
        match evalBox bL, evalBox bR with
        | some bL', some bR' => some (bL' :: bR' :: stk)
        | _, _ => none
    | .schur sigPos =>
      if isEmptyBox cur then none
      else if chkSchur cur sigPos then some stk else none
    | .gram =>
      if isEmptyBox cur then none
      else if chkGram cur then some stk else none
    | .shep mode ia ib ic0 ic1 ic2 ic3 =>
      if isEmptyBox cur then none
      else if chkShep cur mode ia ib ic0 ic1 ic2 ic3 then some stk else none
    | .planar p =>
      if isEmptyBox cur then none
      else if chkPlanar cur p then some stk else none

/-- Execute a balanced binary tree of certificate steps on the obligation stack. -/
@[expose] def runProg (subs : SubTree) : Prog → List BoxI → Option (List BoxI)
  | .step s, stk => stepOne subs s stk
  | .seq p1 p2, stk =>
    match runProg subs p1 stk with
    | some stk2 => runProg subs p2 stk2
    | none => none

/-- Verify that `p` discharges `[b]` using only certified sub-boxes from `subs`. -/
@[expose] def checkBox (subs : SubTree) (p : Prog) (b : BoxI) : Bool :=
  match evalBox b with
  | none => false
  | some b' =>
    match runProg subs p [b'] with
    | some [] => true
    | _ => false

/-- Direct certificate witness for `b` using no sub-boxes. -/
@[expose] def Certified1 (b : BoxI) : Prop :=
  ∃ p : Prog, checkBox .empty p b = true

/-- Two-level certificate witness for `b` discharging into `Certified1` sub-boxes. -/
@[expose] def Certified2 (b : BoxI) : Prop :=
  ∃ (subs : SubTree) (p : Prog),
    SubTreeAll Certified1 subs ∧ checkBox subs p b = true

end Cslib.Circuits.Frontier.Gaussian.PairBound.Cert
