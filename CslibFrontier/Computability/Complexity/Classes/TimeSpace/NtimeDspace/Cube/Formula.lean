/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Chain
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Codes
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.FirstClique
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Gen
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Transport

/-!
# The formula (§6.2)

The recursion of §6.2 unfolds into a formula, described here by the states of an `AGen`:

* `cl chs`: the value of the clique `chainAt fw C₀ chs` (the path `chs` of choice codes, latest
  first). While the clique has `g × g ≥ 4` nodes, a sum node over the choice codes (width
  `choiceWidth g fw`); the child of a valid code is the clique one level down, of an invalid code
  the leaf `0`. With two nodes, a sum node over the codes of the one label (width `codeWidth a`);
  the child of a code of a label of exact weight is `last chs i`.
* `last chs i`: the product of the two table entries at the label coded by `i`.
* `ent chs v args`: the entry of the table of node `v` of the clique at `chs`, at the labels coded
  by `args` (the codes of the labels to the other nodes, in increasing order of the other node,
  each of width `codeWidth` of its budget).
  - At the first clique (`chs = []`), a balanced product `rng0` over the leaf factors of
    Lemma 4.3 (b): the encoding test, and the vertex functions or the equality tests.
  - Higher up, the leaf `0` if a packed label is invalid; otherwise a sum node over the codes `ξ`
    of the copies held in the row (or column) of the parent, with the child `rng` over the factors
    of (eq:table).
* `rng chs v args ξ lo hi`: the product of the factors `lo ≤ f < hi` of the summand of `ξ`, as a
  balanced binary product. A single factor is an old table entry (`ent` one level up), a test
  (`lit`), or a rectangle factor `Ψ_R` (the leaf `0` if the weight test fails, else a transport
  state).
* `tr up x y m lo hi T c`: the coefficient `[z^c]` of the transport sum of the sources `lo ≤ ν < hi`
  of the source list of `N↑(x, y; m)` (`up = true`) or `N↓(x, y; m)` (`up = false`) into the targets
  `T`. Empty source interval: the leaf `[T = 0][c = 0]`. Otherwise a sum node over the pivot index
  of Lemma 5.6, `(ν, t, T₁, c₁, c₀)`, with child `trm`: the product of the coefficient of the first
  half and `trr`, itself the product of the rule coefficient and the coefficient of the second half.
* `lit v`, `zero`: leaves.

`mean` is the meaning of a state (the value, entry or coefficient it stands for); `Sound.lean` gives
a decreasing rank and proves the local soundness and `formula_value`, the value
`Z(G) mod 2^P` of the unfolded tree. The index lengths along paths are bounded in `Paths.lean`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset NtimeDspace.Cross

/-! ### Parameters -/

/-- The data of a formula: a network, the number `K` of vertex groups of the first clique, the
field width of choice codes, and the precision. -/
structure Setup where
  V : ℕ
  G : EdgeNet ℤ (Fin V)
  K : ℕ
  fw : ℕ
  P : ℕ

namespace Setup

variable (S : Setup)

/-- The first clique. -/
def C₀ : Clique := firstClique S.G S.K

/-- The clique at a path of choice codes. -/
noncomputable def clique (chs : List ℕ) : Clique := chainAt S.fw S.C₀ chs

end Setup

/-! ### Codes of argument tuples -/

/-- The offset of the code of the label to node `u` in the argument code of node `v`: the widths of
the codes of the labels to the nodes before `u`. -/
def argOffset (C : Clique) (v u : ℕ) : ℕ :=
  ∑ u' ∈ range u, if h : u' < C.q ∧ v < C.q then
    (if u' = v then 0 else codeWidth (budget C.a ⟨v, h.2⟩ ⟨u', h.1⟩)) else 0

/-- The labels coded by an argument code of node `v` (the empty label where decoding fails). -/
def decodeArgs (C : Clique) (v : Fin C.q) (args : ℕ) : Fin C.q → Label := fun u =>
  if u = v then (0, 0) else
  let w := codeWidth (budget C.a v u)
  match decodeLabel (budget C.a v u) ((args / 2 ^ argOffset C v u) % 2 ^ w) with
  | some l => l
  | none => (0, 0)

/-! ### The source lists of the half-routings -/

/-- The sources of `N↑(x, y; m)` (`up`) or of `N↓(x, y; m)` (`¬ up`, with `x, y` the lower corners
`u, v`), in the order: first corner, second corner, message; each by type. -/
def srcList (up : Bool) (x y m : Label) : List (HPlace × ℕ) :=
  if up then
    (x.1.sort (· ≤ ·)).map (fun i => (some Corner.x, i)) ++
      (y.1.sort (· ≤ ·)).map (fun i => (some Corner.y, i)) ++ (m.2.sort (· ≤ ·)).map
          (fun i => (none, i))
  else
    (x.1.sort (· ≤ ·)).map (fun i => (some Corner.u, i)) ++
      (y.1.sort (· ≤ ·)).map (fun i => (some Corner.v, i)) ++ (m.1.sort (· ≤ ·)).map
          (fun i => (none, i))

/-- The targets of `N↑(x, y; m)` or `N↓(x, y; m)`. -/
def tgtMs (up : Bool) (x y m : Label) : Multiset (HPlace × ℕ) :=
  if up then located (some Corner.x) x.2 + located (some Corner.y) y.2 + located none m.1
  else located (some Corner.u) x.2 + located (some Corner.v) y.2 + located none m.2

/-- The rules of the half-routing. -/
noncomputable def hRule (up : Bool) : HPlace → ℕ → HPlace → ℕ → Lp := if
    up then upRule else downRule

/-- The sublist `lo ≤ ν < hi` of the sources. -/
def srcSub (up : Bool) (x y m : Label) (lo hi : ℕ) : List (HPlace × ℕ) :=
  ((srcList up x y m).drop lo).take (hi - lo)

/-! ### States -/

/-- The states of the formula. -/
inductive St where
  | zero
  | lit (v : ℤ)
  | cl (chs : List ℕ)
  | last (chs : List ℕ) (i : ℕ)
  | ent (chs : List ℕ) (v args : ℕ)
  | rng (chs : List ℕ) (v args ξ lo hi : ℕ)
  | rng0 (v args lo hi : ℕ)
  | tr (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ)) (c : ℤ)
  | trm (up : Bool) (x y m : Label) (lo ν hi : ℕ) (t : HPlace × ℕ) (T₁ T₂ : Multiset (HPlace × ℕ))
      (c₁ c₀ c₂ : ℤ)
  | trr (up : Bool) (x y m : Label) (ν hi : ℕ) (t : HPlace × ℕ) (T₂ : Multiset (HPlace × ℕ))
      (c₀ c₂ : ℤ)

/-! ### Copies, factors and pivot codes -/

/-- The width of the argument code of node `w`: the code widths of its labels. -/
def argWidth (C : Clique) (w : ℕ) : ℕ := argOffset C w C.q

/-- The offset of the slice of position `p` in a code of copies held by the nodes `nodes 0, …`. -/
def sliceOffset (C : Clique) (nodes : ℕ → ℕ) (p : ℕ) : ℕ := ∑ p' ∈ range p, argWidth C (nodes p')

/-- The slice of position `p` of a code of copies. -/
def slice (C : Clique) (nodes : ℕ → ℕ) (ξ p : ℕ) : ℕ :=
  (ξ / 2 ^ sliceOffset C nodes p) % 2 ^ argWidth C (nodes p)

/-- The width of a code of copies held by `g` nodes. -/
def copiesWidth (C : Clique) (nodes : ℕ → ℕ) (g : ℕ) : ℕ := sliceOffset C nodes g

/-- The label of the copy held by node `nodes p` of the pair with `u`. -/
def copyAt (C : Clique) (nodes : ℕ → ℕ) (ξ p u : ℕ) : Label :=
  if h : nodes p < C.q ∧ u < C.q then decodeArgs C ⟨nodes p, h.1⟩ (slice C nodes ξ p) ⟨u, h.2⟩
  else (0, 0)

/-- All copies decode to labels of exact weight. -/
def CopiesValid (C : Clique) (nodes : ℕ → ℕ) (g ξ : ℕ) : Prop :=
  ∀ p < g, ∀ (w u : Fin C.q), w.val = nodes p → u ≠ w →
    ∃ l, decodeLabel (budget C.a w u)
        ((slice C nodes ξ p / 2 ^ argOffset C w u) % 2 ^ codeWidth (budget C.a w u)) = some l ∧
      labelWt l = budget C.a w u

/-- The number of factors of a summand of (eq:table) on a `g × g` grid. -/
def nFac (g : ℕ) : ℕ := g + g * g + g * g + g ^ 4

/-- The four digits base `g` of a quadruple index. -/
def quad (g t : ℕ) : ℕ × ℕ × ℕ × ℕ := (t / g ^ 3 % g, t / g ^ 2 % g, t / g % g, t % g)

/-- The place of a target or source of a half-routing by its index `0, 1, 2`. -/
def placeOf (up : Bool) (p : ℕ) : HPlace :=
  if p = 0 then some (if up then Corner.x else Corner.u)
  else if p = 1 then some (if up then Corner.y else Corner.v) else none

/-- The index of a place. -/
def placeIdx (up : Bool) (pl : HPlace) : ℕ :=
  if pl = some (if up then Corner.x else Corner.u) then 0
  else if pl = some (if up then Corner.y else Corner.v) then 1 else 2

/-- The field widths of a pivot code at weight `W`: the pivot position, the target (`place + 3 ·
type`), the three multisets of `T₁`, and the two exponents (offset by `W`). -/
def pivWidths (W : ℕ) : ℕ × ℕ × ℕ × ℕ :=
    (Nat.size W, Nat.size (3 * W + 3), codeWidth W, Nat.size (2 * W))

/-- The width of a pivot code. -/
def pivWidth (W : ℕ) : ℕ :=
  let (wn, wt, wT, wc) := pivWidths W; wn + wt + 3 * wT + 2 * wc

/-- The decoded fields of a pivot code: position, target, `T₁`, `c₁`, `c₀`. -/
def decodePivot (up : Bool) (W i : ℕ) : ℕ × (HPlace × ℕ) × Multiset (HPlace × ℕ) × ℤ × ℤ :=
  let (wn, wt, wT, wc) := pivWidths W
  let fld (off w : ℕ) : ℕ := (i / 2 ^ off) % 2 ^ w
  let ν := fld 0 wn
  let tc := fld wn wt
  let ms (p : ℕ) : Multiset (HPlace × ℕ) :=
    match decodeLabel W (fld (wn + wt + p * wT) wT) with
    | some l => located (placeOf up p) l.1
    | none => 0
  (ν, (placeOf up (tc % 3), tc / 3), ms 0 + ms 1 + ms 2,
    (fld (wn + wt + 3 * wT) wc : ℤ) - W, (fld (wn + wt + 3 * wT + wc) wc : ℤ) - W)

/-- The code of the fields of a pivot index. -/
noncomputable def pivotCode (up : Bool) (W : ℕ) (ν : ℕ) (t : HPlace × ℕ)
    (T₁ : Multiset (HPlace × ℕ))
    (c₁ c₀ : ℤ) : ℕ :=
  let (wn, wt, wT, wc) := pivWidths W
  let part (p : ℕ) : ℕ :=
    labelCode W (((T₁.filter fun s => s.1 = placeOf up p).map Prod.snd), 0)
  ν + 2 ^ wn * (placeIdx up t.1 + 3 * t.2) +
    2 ^ (wn + wt) * (part 0 + 2 ^ wT * part 1 + 2 ^ (2 * wT) * part 2) +
    2 ^ (wn + wt + 3 * wT) * ((c₁ + W).toNat + 2 ^ wc * (c₀ + W).toNat)

/-- A pivot index is valid: canonical, with a pivot position in the interval, a target of `T`,
`T₁ ≤ T - {t}`, the pivot condition, and exponents in `[-W, W]`. -/
def PivotValid (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ)) (i : ℕ) : Prop :=
  let l := srcSub up x y m lo hi
  let W := tWt l T
  let (ν, t, T₁, c₁, c₀) := decodePivot up W i
  pivotCode up W ν t T₁ c₁ c₀ = i ∧ ν < l.length ∧ t ∈ T ∧ T₁ ≤ T - {t} ∧ PivotCond l T ν t T₁ ∧
    |c₁| ≤ W ∧ |c₀| ≤ W

/-! ### The generator -/

namespace Setup

variable (S : Setup)

/-- The parent of the clique at `i :: rest` on its grid, if its node count is a square: the side
`g`, the budgets and tables, the choice, and whether the rows are merged. -/
noncomputable def parentGrid (rest : List ℕ) (i : ℕ) :
    Option ((g : ℕ) × (Fin (g * g) → Fin (g * g) → ℕ) × (Fin (g * g) → (Fin (g * g) → Label) → ℤ) ×
      (Rect g → ℤ × ℤ) × Bool) :=
  let C := S.clique rest
  let g := Nat.sqrt C.q
  if h : C.q = g * g then
    let C' := C.recast (g * g) h
    let ι := decodeChoice g S.fw i
    some ⟨g, C'.a, C'.T, ι, orientRow C'.a fun r => (ι r).1⟩
  else none

/-- The nodes of the parent holding the copies of node `v` of the child: the row `v`
(`node v p`) or the column `v` (`node p v`). -/
def holders (g v : ℕ) (row : Bool) : ℕ → ℕ := fun p => if row then v * g + p else p * g + v

/-- The state of a single factor `f` of the summand of `ξ` in the entry of node `v` at `i :: rest`.
-/
noncomputable def factorSt (rest : List ℕ) (i v args ξ f : ℕ) : St :=
  match S.parentGrid rest i with
  | none => .zero
  | some ⟨g, a, _, ι, row⟩ =>
    let P := S.clique rest
    let nodes := holders g v row
    let Θ : ℕ → Label := fun A' =>
      if h : A' < (S.clique (i :: rest)).q ∧ v < (S.clique (i :: rest)).q then
        decodeArgs (S.clique (i :: rest)) ⟨v, h.2⟩ args ⟨A', h.1⟩ else (0, 0)
    let cp := copyAt P nodes ξ
    let nd : ℕ → ℕ → ℕ := fun A B => A * g + B
    if f < g then .ent rest (nodes f) (slice P nodes ξ f)
    else if f < g + g * g then
      let t := f - g; let p := t / g; let p' := t % g
      .lit (if p < p' ∧ cp p (nodes p') ≠ cp p' (nodes p) then 0 else 1)
    else if f < g + g * g + g * g then
      let t := f - g - g * g; let o := t / g; let p := t % g
      .lit (if o ≠ v ∧ cp p (if row then nd o p else nd p o) ≠ unpack (packL g) (Θ o) (1 + p)
        then 0 else 1)
    else
      let (A₁, A₂, B₁, B₂) := quad g (f - g - g * g - g * g)
      if h : A₁ < A₂ ∧ B₁ < B₂ ∧ A₂ < g ∧ B₂ < g then
        let r : Rect g := ⟨((⟨A₁, by omega⟩, ⟨A₂, h.2.2.1⟩), (⟨B₁, by omega⟩, ⟨B₂, h.2.2.2⟩)),
          h.1, h.2.1⟩
        let k := (ι r).1; let c := (ι r).2
        let H : ℤ := diagWt a r
        if row then
          if v = A₁ then
            let m := unpack (packL g) (Θ A₂) (rStream g ⟨B₁, by omega⟩ ⟨B₂, h.2.2.2⟩)
            if (labelWt m : ℤ) ≤ H + k / 2 then
              let x := cp B₁ (nd A₂ B₂); let y := cp B₂ (nd A₂ B₁)
              .tr true x y m 0 (srcList true x y m).length (tgtMs true x y m) (k - c)
            else .zero
          else if v = A₂ then
            let m := unpack (packL g) (Θ A₁) (rStream g ⟨B₁, by omega⟩ ⟨B₂, h.2.2.2⟩)
            if (labelWt m : ℤ) ≤ H + k / 2 then
              let x := swapLabel (cp B₁ (nd A₁ B₂)); let y := swapLabel (cp B₂ (nd A₁ B₁))
              .tr false x y m 0 (srcList false x y m).length (tgtMs false x y m) c
            else .zero
          else .lit 1
        else
          if v = B₁ then
            let m := unpack (packL g) (Θ B₂) (rStream g ⟨A₁, by omega⟩ ⟨A₂, h.2.2.1⟩)
            if (labelWt m : ℤ) ≤ H - k / 2 then
              let x := cp A₁ (nd A₂ B₂); let y := swapLabel (cp A₂ (nd A₁ B₂))
              .tr true x y m 0 (srcList true x y m).length (tgtMs true x y m) (-k - c)
            else .zero
          else if v = B₂ then
            let m := unpack (packL g) (Θ B₁) (rStream g ⟨A₁, by omega⟩ ⟨A₂, h.2.2.1⟩)
            if (labelWt m : ℤ) ≤ H - k / 2 then
              let x := cp A₁ (nd A₂ B₁); let y := swapLabel (cp A₂ (nd A₁ B₁))
              .tr false x y m 0 (srcList false x y m).length (tgtMs false x y m) c
            else .zero
          else .lit 1
      else .lit 1

/-- The number of factors of an entry of the first clique at node `v`: the encoding test, then the
vertices (vertex groups) or the edges (test groups). -/
def nFac0 (v : ℕ) : ℕ := 1 + (if v < S.K then S.V else S.G.M)

/-- The value of a single factor of an entry of the first clique. -/
noncomputable def factor0 (v args f : ℕ) : ℤ :=
  let Θ : Fin (2 * S.K) → Label := fun u =>
    if h : v < S.C₀.q then decodeArgs S.C₀ ⟨v, h⟩ args ⟨u.val, by simp [Setup.C₀, firstClique]⟩
    else (0, 0)
  if f = 0 then
    if v < S.K then (if ∀ τ < S.K, IsEnc (width S.G S.K v τ)
        (labelOfNode S.K Θ (S.K + τ)) then 1 else 0)
    else (if ∀ j < S.K, IsEnc (width S.G S.K j (v - S.K)) (labelOfNode S.K Θ j) then 1 else 0)
  else if v < S.K then
    if h : f - 1 < S.V then
      let x : Fin S.V := ⟨f - 1, h⟩
      if vgroup S.G S.K x = v then
        S.G.eval x ((S.G.ports x).map fun e =>
          heBit S.G S.K (labelOfNode S.K Θ (S.K + tgroup S.G S.K e)) v (tgroup S.G S.K e)
            (e, decide (S.G.w e = x)))
      else 1
    else 1
  else
    if h : f - 1 < S.G.M then
      let e : Fin S.G.M := ⟨f - 1, h⟩
      if tgroup S.G S.K e = v - S.K then
        (if heBit S.G S.K (labelOfNode S.K Θ (vgroup S.G S.K (S.G.u e))) (vgroup S.G S.K (S.G.u e))
              (v - S.K) (e, false) =
            heBit S.G S.K (labelOfNode S.K Θ (vgroup S.G S.K (S.G.w e))) (vgroup S.G S.K (S.G.w e))
              (v - S.K) (e, true) then 1 else 0)
      else 1
    else 1

/-- The state of a factor range `[lo, hi)`: the product of nothing, a single factor, or a range. -/
noncomputable def rangeSt (mk : ℕ → St) (mkR : ℕ → ℕ → St) (lo hi : ℕ) : St :=
  if hi ≤ lo then .lit 1 else if hi = lo + 1 then mk lo else mkR lo hi

/-- The width of the copies of node `v` of the clique at `i :: rest`. -/
noncomputable def xiWidth (rest : List ℕ) (i v : ℕ) : ℕ :=
  match S.parentGrid rest i with
  | none => 0
  | some ⟨g, _, _, _, row⟩ => copiesWidth (S.clique rest) (holders g v row) g

/-- The labels `Θ` of node `v` of a clique are all valid packed labels. -/
def ArgsValid (C : Clique) (v args : ℕ) (L : ℕ) : Prop :=
  ∀ (w u : Fin C.q), w.val = v → u ≠ w → validLabel L (decodeArgs C w args u)

open Classical in
/-- **The generator of the formula.** -/
noncomputable def gen : AGen St where
  kind := fun
    | .zero | .lit _ => .leaf
    | .cl chs =>
      let C := S.clique chs
      if C.q = 2 then .sum else if 4 ≤ C.q ∧ C.q = Nat.sqrt C.q * Nat.sqrt C.q then .sum else .leaf
    | .last _ _ => .prod
    | .ent [] _ _ => .prod
    | .ent (i :: rest) v args =>
      match S.parentGrid rest i with
      | none => .leaf
      | some ⟨g, _, _, _, _⟩ =>
        if ArgsValid (S.clique (i :: rest)) v args (packL g) then .sum else .leaf
    | .rng _ _ _ _ _ _ | .rng0 _ _ _ _ => .prod
    | .tr _ _ _ _ lo hi _ _ => if lo < hi then .sum else .leaf
    | .trm .. | .trr .. => .prod
  width := fun
    | .cl chs =>
      let C := S.clique chs
      if h : C.q = 2 then codeWidth (C.a ⟨0, by omega⟩ ⟨1, by omega⟩)
      else choiceWidth (Nat.sqrt C.q) S.fw
    | .ent (i :: rest) v _ => S.xiWidth rest i v
    | .tr up x y m lo hi T _ => pivWidth (tWt (srcSub up x y m lo hi) T)
    | _ => 0
  leafVal := fun
    | .lit v => v
    | .tr _ _ _ _ _ _ T c => if T = 0 ∧ c = 0 then 1 else 0
    | _ => 0
  child := fun
    | .cl chs, i =>
      let C := S.clique chs
      if h : C.q = 2 then
        match decodeLabel (C.a ⟨0, by omega⟩ ⟨1, by omega⟩) i with
        | some l => if labelWt l = C.a ⟨0, by omega⟩ ⟨1, by omega⟩ then .last chs i else .zero
        | none => .zero
      else if h : C.q = Nat.sqrt C.q * Nat.sqrt C.q then
        if ValidChoiceCode (C.recast _ h).a S.fw i then .cl (i :: chs) else .zero
      else .zero
    | .last chs i, b => .ent chs b i
    | .ent [] v args, b =>
      let n := S.nFac0 v; let mid := n / 2
      if b = 0 then rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) 0 mid
      else rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) mid n
    | .rng0 v args lo hi, b =>
      let mid := (lo + hi) / 2
      if b = 0 then rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) lo mid
      else rangeSt (fun f => .lit (S.factor0 v args f)) (.rng0 v args) mid hi
    | .ent (i :: rest) v args, ξ =>
      match S.parentGrid rest i with
      | none => .zero
      | some ⟨g, _, _, _, row⟩ =>
        if CopiesValid (S.clique rest) (holders g v row) g ξ then .rng (i :: rest) v
            args ξ 0 (nFac g)
        else .zero
    | .rng (i :: rest) v args ξ lo hi, b =>
      let mid := (lo + hi) / 2
      if b = 0 then rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) lo mid
      else rangeSt (S.factorSt rest i v args ξ) (.rng (i :: rest) v args ξ) mid hi
    | .tr up x y m lo hi T c, i =>
      let l := srcSub up x y m lo hi
      let W := tWt l T
      if PivotValid up x y m lo hi T i then
        let (ν, t, T₁, c₁, c₀) := decodePivot up W i
        .trm up x y m lo (lo + ν) hi t T₁ (T - T₁ - {t}) c₁ c₀ (c - c₁ - c₀)
      else .zero
    | .trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂, b =>
      if b = 0 then .tr up x y m lo pos T₁ c₁ else .trr up x y m pos hi t T₂ c₀ c₂
    | .trr up x y m pos hi t T₂ c₀ c₂, b =>
      if b = 0 then
        let s := (srcList up x y m).getD pos t
        .lit ((hRule up s.1 s.2 t.1 t.2).coeff c₀)
      else .tr up x y m (pos + 1) hi T₂ c₂
    | _, _ => .zero

/-! ### The meaning of a state -/

/-- The entry of the table of node `v` of the clique at `chs`, at the labels coded by `args`. -/
noncomputable def entryMean (chs : List ℕ) (v args : ℕ) : ℤ :=
  let C := S.clique chs
  if h : v < C.q then C.T ⟨v, h⟩ (decodeArgs C ⟨v, h⟩ args) else 0

/-- The coefficient `[z^c]` of the transport sum of a source interval. -/
noncomputable def trMean (up : Bool) (x y m : Label) (lo hi : ℕ)
    (T : Multiset (HPlace × ℕ)) (c : ℤ) :
    ℤ :=
  (transportL (srcSub up x y m lo hi) T (hRule up)).coeff c

/-- The coefficient of the rule of the source at position `pos` and the target `t`. -/
noncomputable def ruleCoeff (up : Bool) (x y m : Label) (pos : ℕ) (t : HPlace × ℕ) (c₀ : ℤ) : ℤ :=
  let s := (srcList up x y m).getD pos t
  (hRule up s.1 s.2 t.1 t.2).coeff c₀

/-- The meaning of a state that is not a product range. -/
noncomputable def meanBase : St → ℤ
  | .zero => 0
  | .lit v => v
  | .cl chs =>
    let C := S.clique chs
    if C.q = 2 ∨ (4 ≤ C.q ∧ C.q = Nat.sqrt C.q * Nat.sqrt C.q) then C.value else 0
  | .last chs i => S.entryMean chs 0 i * S.entryMean chs 1 i
  | .ent chs v args => S.entryMean chs v args
  | .tr up x y m lo hi T c => trMean up x y m lo hi T c
  | .trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂ =>
    trMean up x y m lo pos T₁ c₁ * (ruleCoeff up x y m pos t c₀ * trMean up x y m
        (pos + 1) hi T₂ c₂)
  | .trr up x y m pos hi t T₂ c₀
      c₂ => ruleCoeff up x y m pos t c₀ * trMean up x y m (pos + 1) hi T₂ c₂
  | .rng .. | .rng0 .. => 0

/-- **The meaning of a state.** -/
noncomputable def mean : St → ℤ
  | .rng (i :: rest) v args ξ lo hi => ∏ f ∈ Ico lo hi, S.meanBase (S.factorSt rest i v args ξ f)
  | .rng0 v args lo hi => ∏ f ∈ Ico lo hi, S.factor0 v args f
  | st => S.meanBase st

/-- The setup is good: the first clique has `q₀ = 2^(2^e)` nodes (so that halving the name length
ends at two nodes), and the fields of choice codes hold every grade and split (`6 Φ₀ < 2^(fw-1)`;
every budget in the chain is at most `Φ₀`). -/
def Good : Prop :=
  1 ≤ S.K ∧ (∃ e, 2 * S.K = 2 ^ 2 ^ e) ∧ 12 * (S.C₀.potential + 1) < 2 ^ (S.fw - 1)

end Setup

end Cslib.Complexity.NtimeDspace.Cube
