/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
public import CslibFrontier.Computability.Complexity.Problems.UGraph
import CslibFrontier.Computability.Complexity.Problems.UGraph.USTCONWriter

/-!
# Undirected connectivity of a whole graph is in logarithmic space

**Goldreich's Theorem 5.6** [Goldreich2007DraftR2] (Section 5.2.4, `r2` PDF p. 54, printed
p. 170): deciding undirected connectivity (`UCONN`) is in `L`. Goldreich's `UCONN` asks whether a
given graph is connected (`r2` PDF p. 53, printed p. 169), and a graph "is called connected if
there exists a path between each pair of vertices in it" [Goldreich2007DraftR6] (Appendix G.1,
`r6` PDF p. 138, printed p. 646). Here graphs are undirected graph instances
(`Cslib.Complexity.UGraphInstance`, a symmetric loopless adjacency matrix on `Fin n`, encoded by
`Cslib.Complexity.encUGraph`), and `Cslib.Complexity.UCONN` is the set of instances whose graph is
`SimpleGraph.Preconnected`: every two vertices are joined by a walk. As in Goldreich's
definition, the graph without vertices is connected. (Mathlib's `SimpleGraph.Connected`
additionally requires a vertex.)

The proof reduces `UCONN` to undirected `s`–`t` connectivity, which is in `L` by Reingold's
theorem (`Cslib.Complexity.USTCON_mem_L`). A graph `G` on `n` vertices is connected exactly when
every vertex `v` is reachable from the vertex `0`. The instance
`Cslib.Complexity.UCONN.chainInstance G` puts these `n` queries in series: it takes `n` disjoint
copies of `G`, joins the vertex `v` of the copy `v` to the vertex `0` of the copy `v + 1`, a
source to the vertex `0` of the copy `0` and the vertex `n - 1` of the copy `n - 1` to a target.
Every joining edge is a bridge, so the source reaches the target exactly when the vertex `0`
reaches `v` in the copy `v` for every `v` (`Cslib.Complexity.UCONN.chainInstance_mem_iff`); for
`n = 0`, the source and the target are joined directly. The instance is written in logarithmic
space by `Cslib.Complexity.UGraphInstance.ustconWriter`: an entry within a copy reads one entry of
the input matrix and every other entry is arithmetic in `n` and its row and column
(`Cslib.Complexity.UCONN.computableInLogSpace_chainInstance`). This is a logarithmic-space
many-one reduction (`Cslib.Complexity.UCONN.logSpaceReducible_USTCON`), so `UCONN` is in `L`
(`Cslib.Complexity.UCONN_mem_L`). Space is that of `L`: the work-tape cells visited; as for every
problem in `L`, the decider is only required to be correct on encodings of instances.

Goldreich proves Theorem 5.6 directly, by transforming the graph into a collection of expanders
while preserving its connected components. The library's proof of Reingold's theorem decides
`s`–`t` connectivity; the series composition above is the step from `s`–`t` connectivity to the
whole graph.

The vertices of the instance are numbered so that a counter program can decode them: the source
is `0`, the target `1`, and the vertex `x` of the copy `v` is
`Cslib.Complexity.UCONN.copyVertex n v x = 2 + v n + x`.

## Main definitions

* `Cslib.Complexity.UCONN`: the connected undirected graphs.
* `Cslib.Complexity.UCONN.chainInstance`: the copies of the graph in series, as an instance of
  undirected `s`–`t` connectivity.

## Main results

* `Cslib.Complexity.UCONN.chainInstance_mem_iff`: the source reaches the target exactly when the
  graph is connected.
* `Cslib.Complexity.UCONN.logSpaceReducible_USTCON`: `UCONN` reduces to `USTCON` in logarithmic
  space.
* `Cslib.Complexity.UCONN_mem_L`: **Goldreich's Theorem 5.6**, `UCONN` is in `L`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  `r2`][Goldreich2007DraftR2]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  `r6`][Goldreich2007DraftR6]
* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
-/

@[expose] public section

namespace Cslib.Complexity

/-- **Undirected connectivity** (`UCONN`) [Goldreich2007DraftR2]: the undirected graphs in which
every two vertices are joined by a path, including the graph without vertices. -/
def UCONN : Set UGraphInstance :=
  {G | G.graph.Preconnected}

theorem mem_UCONN {G : UGraphInstance} : G ∈ UCONN ↔ G.graph.Preconnected := Iff.rfl

namespace UCONN

/-! ### The numbering of the copies -/

variable (n : ℕ)

/-- The number of vertices: the `n` vertices of each of the `n` copies, a source and a target. -/
def numVertices : ℕ := n * n + 2

/-- The vertex `x` of the copy `v`. -/
def copyVertex (v x : ℕ) : ℕ := 2 + v * n + x

/-- The copy of a vertex numbered at least `2`. -/
def copy (r : ℕ) : ℕ := (r - 2) / n

/-- The vertex of the graph that a vertex numbered at least `2` stands for. -/
def vert (r : ℕ) : ℕ := (r - 2) % n

/-- The edges between steps of the chain, from `r` to `c`: the source `0` is joined to the vertex
`0` of the copy `0`, or to the target `1` when there are no copies; the vertex `v` of the copy `v`
is joined to the target when `v` is the last copy, and otherwise to the vertex `0` of the copy
`v + 1`. -/
def Link (r c : ℕ) : Prop :=
  (r = 0 ∧ c = 1 ∧ n = 0) ∨ (r = 0 ∧ c = 2 ∧ 0 < n) ∨
    (2 ≤ r ∧ vert n r = copy n r ∧
      ((c = 1 ∧ copy n r + 1 = n) ∨ (2 ≤ c ∧ vert n c = 0 ∧ copy n c = copy n r + 1)))

instance (r c : ℕ) : Decidable (Link n r c) := by
  unfold Link
  infer_instance

variable {n}

theorem two_le_copyVertex (v x : ℕ) : 2 ≤ copyVertex n v x :=
  (Nat.le_add_right 2 _).trans (Nat.le_add_right _ _)

theorem copy_copyVertex {v x : ℕ} (hx : x < n) : copy n (copyVertex n v x) = v := by
  simp only [copy, copyVertex]
  rw [show 2 + v * n + x - 2 = x + n * v by rw [Nat.mul_comm]; omega,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem vert_copyVertex (v : ℕ) {x : ℕ} (hx : x < n) : vert n (copyVertex n v x) = x := by
  simp only [vert, copyVertex]
  rw [show 2 + v * n + x - 2 = x + n * v by rw [Nat.mul_comm]; omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem copyVertex_lt {v x : ℕ} (hv : v < n) (hx : x < n) : copyVertex n v x < numVertices n := by
  have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  simp only [copyVertex, numVertices]
  omega

/-- **Every vertex numbered at least `2` is a vertex of a copy.** -/
theorem eq_copyVertex {r : ℕ} (h₂ : 2 ≤ r) (hr : r < numVertices n) :
    copy n r < n ∧ vert n r < n ∧ r = copyVertex n (copy n r) (vert n r) := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [numVertices, h0] at hr; omega
  have hq : r - 2 < n * n := by simp only [numVertices] at hr; omega
  have := Nat.div_add_mod (r - 2) n
  refine ⟨Nat.div_lt_of_lt_mul hq, Nat.mod_lt _ hn, ?_⟩
  simp only [copyVertex, copy, vert, Nat.mul_comm _ n]
  omega

/-! ### The instance -/

variable (G : UGraphInstance)

/-- The edges of the copies in series, on natural numbers: within a copy, `x` and `y` are joined
when they are in `G`; between steps, the edges `Link`. -/
def entry (r c : ℕ) : Bool :=
  if 2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c then G.adjN (vert G.n r) (vert G.n c)
  else decide (Link G.n r c) || decide (Link G.n c r)

theorem entry_comm (r c : ℕ) : entry G r c = entry G c r := by
  unfold entry
  by_cases h : 2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c
  · rw [ite_eq_left h, ite_eq_left ⟨h.2.1, h.1, h.2.2.symm⟩, G.adjN_comm]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩, Bool.or_comm]

theorem entry_self (r : ℕ) : entry G r r = false := by
  unfold entry
  by_cases h : 2 ≤ r
  · rw [ite_eq_left ⟨h, h, rfl⟩, UGraphInstance.adjN]
    split_ifs with h'
    · exact G.loopless _
    · rfl
  · rw [ite_eq_right fun h' => h h'.1]
    simp only [Link, Bool.or_self, decide_eq_false_iff_not]
    omega

/-- **The copies of the graph in series**, with the source `0` and the target `1`, as an instance
of undirected `s`–`t` connectivity. -/
def chainInstance : USTCONInstance where
  n := numVertices G.n
  adj a b := entry G a b
  symm a b := entry_comm G a b
  loopless a := entry_self G a
  s := ⟨0, by simp [numVertices]⟩
  t := ⟨1, by simp [numVertices]⟩

/-- The vertex `x` of the copy `v`, as a vertex of the instance. -/
def cv {v : ℕ} (hv : v < G.n) (x : Fin G.n) : Fin (chainInstance G).n :=
  ⟨copyVertex G.n v x, copyVertex_lt hv x.isLt⟩

/-- An edge `{x, y}` of the graph joins `x` and `y` in every copy. -/
theorem adj_cv {v : ℕ} (hv : v < G.n) {x y : Fin G.n} (h : G.graph.Adj x y) :
    (chainInstance G).graph.Adj (cv G hv x) (cv G hv y) := by
  change entry G (copyVertex G.n v x) (copyVertex G.n v y) = true
  rw [entry, ite_eq_left ⟨two_le_copyVertex _ _, two_le_copyVertex _ _,
    by rw [copy_copyVertex x.isLt, copy_copyVertex y.isLt]⟩, vert_copyVertex _ x.isLt,
    vert_copyVertex _ y.isLt, UGraphInstance.adjN, dite_eq_left ⟨x.isLt, y.isLt⟩]
  exact h

/-- Every copy of the graph embeds in the instance. -/
def copyHom {v : ℕ} (hv : v < G.n) : G.graph →g (chainInstance G).graph :=
  ⟨cv G hv, adj_cv G hv⟩

/-- A map sending each edge to an edge or to a single vertex preserves reachability. -/
private theorem reachable_map {V W : Type*} {H : SimpleGraph V} {K : SimpleGraph W} (f : V → W)
    (hf : ∀ a b, H.Adj a b → f a = f b ∨ K.Adj (f a) (f b)) {a b : V} (h : H.Reachable a b) :
    K.Reachable (f a) (f b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  exact h.lift' f fun a b hab => (hf a b hab).elim
    (fun e => by change Relation.ReflTransGen K.Adj (f a) (f b); exact e ▸ .refl) .single

/-- The retraction onto the copy `w`: the source and the copies before `w` go to the vertex `0`,
the target and the copies after `w` to the vertex `w`. -/
private def retract (w : Fin G.n) (r : ℕ) : Fin G.n :=
  if r < 2 then (if r = 0 then ⟨0, Nat.zero_lt_of_lt w.isLt⟩ else w)
  else if copy G.n r = w then ⟨vert G.n r, Nat.mod_lt _ (Nat.zero_lt_of_lt w.isLt)⟩
  else if copy G.n r < w then ⟨0, Nat.zero_lt_of_lt w.isLt⟩ else w

private theorem val_retract (w : Fin G.n) (r : ℕ) :
    (retract G w r : ℕ) = if r < 2 then (if r = 0 then 0 else (w : ℕ))
      else if copy G.n r = w then vert G.n r else if copy G.n r < w then 0 else (w : ℕ) := by
  unfold retract
  split_ifs <;> rfl

/-- **The retraction sends each edge to an edge or to a single vertex.** -/
private theorem retract_adj (w : Fin G.n) (a b : Fin (chainInstance G).n)
    (hab : (chainInstance G).graph.Adj a b) :
    retract G w a = retract G w b ∨ G.graph.Adj (retract G w a) (retract G w b) := by
  change entry G a b = true at hab
  unfold entry at hab
  split_ifs at hab with hin
  · -- an edge within a copy
    obtain ⟨ha2, hb2, hcopy⟩ := hin
    obtain ⟨-, hva, -⟩ := eq_copyVertex ha2 a.isLt
    obtain ⟨-, hvb, -⟩ := eq_copyVertex hb2 b.isLt
    by_cases hw : copy G.n a = w
    · refine Or.inr ?_
      rw [show retract G w a = ⟨vert G.n a, hva⟩ from
          Fin.ext (by rw [val_retract, ite_eq_right (by omega), ite_eq_left hw]),
        show retract G w b = ⟨vert G.n b, hvb⟩ from
          Fin.ext (by rw [val_retract, ite_eq_right (by omega), ite_eq_left (hcopy ▸ hw)])]
      simpa [UGraphInstance.adjN, hva, hvb] using hab
    · refine Or.inl (Fin.ext ?_)
      rw [val_retract, val_retract]
      split_ifs <;> omega
  · -- an edge between steps
    refine Or.inl ?_
    have key (r c : Fin (chainInstance G).n) (hl : Link G.n r c) :
        retract G w r = retract G w c := by
      have := w.isLt
      apply Fin.ext
      rw [val_retract, val_retract]
      rcases hl with ⟨-, -, h0⟩ | ⟨hr0, hc2, hn⟩ | ⟨hr2, hvr, ⟨hc1, hlast⟩ | ⟨hc2, hvc, hcc⟩⟩
      · omega
      · have : copy G.n 2 = 0 ∧ vert G.n 2 = 0 := by simp [copy, vert]
        rw [hc2]
        split_ifs <;> omega
      · split_ifs <;> omega
      · split_ifs <;> omega
    rw [Bool.or_eq_true] at hab
    exact hab.elim (fun h => key a b (of_decide_eq_true h))
      (fun h => (key b a (of_decide_eq_true h)).symm)

/-- **The source reaches the target exactly when the graph is connected.** -/
theorem chainInstance_mem_iff : chainInstance G ∈ USTCON ↔ G ∈ UCONN := by
  rw [mem_UCONN]
  refine ⟨fun hst a b => ?_, fun hG => ?_⟩
  · -- the retraction onto the copy `w` maps the path to a walk from `0` to `w`
    have h0 (w : Fin G.n) : G.graph.Reachable ⟨0, Nat.zero_lt_of_lt w.isLt⟩ w := by
      have h := reachable_map (fun r : Fin (chainInstance G).n => retract G w r)
        (retract_adj G w) hst
      rwa [show retract G w (chainInstance G).s = ⟨0, Nat.zero_lt_of_lt w.isLt⟩ from
          Fin.ext (by simp [val_retract, chainInstance]),
        show retract G w (chainInstance G).t = w from
          Fin.ext (by simp [val_retract, chainInstance])] at h
    exact (h0 a).symm.trans (h0 b)
  · rcases Nat.eq_zero_or_pos G.n with hn | hn
    · -- no copies: the source and the target are joined
      exact SimpleGraph.Adj.reachable (show entry G 0 1 = true by simp [entry, Link, hn])
    -- the source reaches the vertex `v` of the copy `v`, along the copies before
    have hstep (v) (hv : v < G.n) :
        (chainInstance G).graph.Reachable (chainInstance G).s (cv G hv ⟨v, hv⟩) := by
      induction v with
      | zero =>
        exact SimpleGraph.Adj.reachable
          (show entry G 0 (copyVertex G.n 0 0) = true by simp [entry, Link, copyVertex, hn])
      | succ v ih =>
        have hlink : (chainInstance G).graph.Adj (cv G (v := v) (by omega) ⟨v, by omega⟩)
            (cv G hv ⟨0, hn⟩) := by
          change entry G (copyVertex G.n v v) (copyVertex G.n (v + 1) 0) = true
          have h1 : copy G.n (copyVertex G.n v v) = v := copy_copyVertex (by omega)
          have h2 : copy G.n (copyVertex G.n (v + 1) 0) = v + 1 := copy_copyVertex hn
          rw [entry, ite_eq_right (by omega), Bool.or_eq_true, decide_eq_true_eq]
          exact .inl (.inr (.inr ⟨two_le_copyVertex _ _, by rw [vert_copyVertex _ (by omega), h1],
            .inr ⟨two_le_copyVertex _ _, vert_copyVertex _ hn, by rw [h1, h2]⟩⟩))
        exact (ih (by omega)).trans (hlink.reachable.trans
          ((hG ⟨0, hn⟩ ⟨v + 1, hv⟩).map (copyHom G hv)))
    refine (hstep _ (Nat.sub_one_lt_of_lt hn)).trans (SimpleGraph.Adj.reachable ?_)
    change entry G (copyVertex G.n (G.n - 1) (G.n - 1)) 1 = true
    have h1 : copy G.n (copyVertex G.n (G.n - 1) (G.n - 1)) = G.n - 1 :=
      copy_copyVertex (by omega)
    rw [entry, ite_eq_right (by omega), Bool.or_eq_true, decide_eq_true_eq]
    exact .inl (.inr (.inr ⟨two_le_copyVertex _ _, by rw [vert_copyVertex _ (by omega), h1],
      .inl ⟨rfl, by omega⟩⟩))

/-! ### The writer -/

section Writer

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Expr
  _root_.Turing.MultiTapeTM

/-- The number of vertices, from `n` in register `0`. -/
private def numVerticesExpr : Expr := add (mul (reg 0) (reg 0)) (const 2)

/-- The copy of the vertex in a register. -/
private def copyExpr (i : ℕ) : Expr := div (sub (reg i) (const 2)) (reg 0)

/-- The vertex of the graph that the vertex in a register stands for. -/
private def vertExpr (i : ℕ) : Expr := mod (sub (reg i) (const 2)) (reg 0)

/-- The row `1` and the column `2` lie in one copy. -/
private def withinExpr : Expr :=
  andB (ltB (const 1) (reg 1)) (andB (ltB (const 1) (reg 2)) (eqB (copyExpr 1) (copyExpr 2)))

/-- The position of the input entry that an entry within a copy reads. -/
private def positionExpr : Expr :=
  add (add (reg 0) (const 1)) (add (mul (vertExpr 1) (reg 0)) (vertExpr 2))

/-- `Link` from the vertex in register `i` to the vertex in register `j`. -/
private def linkExpr (i j : ℕ) : Expr :=
  orB (andB (eqB (reg i) (const 0)) (andB (eqB (reg j) (const 1)) (eqB (reg 0) (const 0))))
    (orB (andB (eqB (reg i) (const 0)) (andB (eqB (reg j) (const 2)) (ltB (const 0) (reg 0))))
      (andB (ltB (const 1) (reg i)) (andB (eqB (vertExpr i) (copyExpr i))
        (orB (andB (eqB (reg j) (const 1)) (eqB (add (copyExpr i) (const 1)) (reg 0)))
          (andB (ltB (const 1) (reg j)) (andB (eqB (vertExpr j) (const 0))
            (eqB (copyExpr j) (add (copyExpr i) (const 1)))))))))

/-- The entries between steps. -/
private def endpointExpr : Expr := orB (linkExpr 1 2) (linkExpr 2 1)

private theorem eval_linkExpr (regs : List ℕ) (i j : ℕ) :
    (linkExpr i j).eval regs =
      (decide (Link (regs.getD 0 0) (regs.getD i 0) (regs.getD j 0))).toNat := by
  rw [linkExpr, eval_orB (eval_andB eval_eqB (eval_andB eval_eqB eval_eqB))
    (eval_orB (eval_andB eval_eqB (eval_andB eval_eqB eval_ltB))
      (eval_andB eval_ltB (eval_andB eval_eqB (eval_orB (eval_andB eval_eqB eval_eqB)
        (eval_andB eval_ltB (eval_andB eval_eqB eval_eqB))))))]
  simp only [copyExpr, vertExpr, eval_add, eval_sub, eval_div, eval_mod, eval_reg, eval_const]
  congr 1

variable (G : UGraphInstance)

private theorem eval_withinExpr (r c : ℕ) :
    withinExpr.eval [G.n, r, c] = (decide (2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c)).toNat := by
  rw [withinExpr, eval_andB eval_ltB (eval_andB eval_ltB eval_eqB)]
  simp only [copyExpr, copy, eval_div, eval_sub, eval_reg, eval_const, List.getD_cons_zero,
    List.getD_cons_succ]
  rfl

private theorem eval_endpointExpr (r c : ℕ) :
    endpointExpr.eval [G.n, r, c] = (decide (Link G.n r c) || decide (Link G.n c r)).toNat := by
  rw [endpointExpr, eval_orB (eval_linkExpr _ _ _) (eval_linkExpr _ _ _)]
  rfl

/-- The entry `(r, c)` of the copies in series, as computed from the expressions: the input bit
at `positionExpr` within a copy, `endpointExpr` otherwise. -/
private theorem entry_eq_exprs (G : UGraphInstance) (r c : Fin (chainInstance G).n) :
    (chainInstance G).adj r c =
      if 0 < withinExpr.eval [G.n, r, c] then G.encode[positionExpr.eval [G.n, r, c]]?.getD false
      else decide (0 < endpointExpr.eval [G.n, r, c]) := by
  change entry G r c = _
  rw [eval_withinExpr, entry]
  by_cases hw : 2 ≤ (r : ℕ) ∧ 2 ≤ (c : ℕ) ∧ copy G.n r = copy G.n c
  · obtain ⟨-, hvr, -⟩ := eq_copyVertex hw.1 r.isLt
    obtain ⟨-, hvc, -⟩ := eq_copyVertex hw.2.1 c.isLt
    have hpos : positionExpr.eval [G.n, r, c] = G.n + 1 + (vert G.n r * G.n + vert G.n c) := by
      simp [positionExpr, vertExpr, vert]
    rw [ite_eq_left hw, UGraphInstance.adjN, dite_eq_left ⟨hvr, hvc⟩, hpos,
      G.getElem?_encode_matrix hvr hvc]
    simp [hw]
  · rw [ite_eq_right hw, eval_endpointExpr]
    simp only [hw, decide_false, Bool.toNat_false, lt_irrefl, ↓reduceIte]
    cases decide (Link G.n r c) || decide (Link G.n c r) <;> simp

/-- **The copies in series are computed in logarithmic space** from the encoded graph, by
`UGraphInstance.ustconWriter`. -/
theorem computableInLogSpace_chainInstance :
    ComputableInLogSpace chainInstance encUGraph encUSTCON :=
  UGraphInstance.computableInLogSpace_of_entryExprs (numV := numVerticesExpr) 1
    (fun G r c => by simp [numVerticesExpr, chainInstance, numVertices])
    (fun G => by
      simp only [chainInstance, numVertices, G.length_encode, pow_one]
      omega)
    (fun _ => rfl) (fun _ => rfl) entry_eq_exprs

end Writer

/-- **Undirected connectivity reduces to undirected `s`–`t` connectivity in logarithmic space**,
by the copies of the graph in series. -/
theorem logSpaceReducible_USTCON : LogSpaceReducible encUGraph encUSTCON UCONN USTCON :=
  ⟨chainInstance, computableInLogSpace_chainInstance, fun G => (chainInstance_mem_iff G).symm⟩

end UCONN

/-- **Goldreich's Theorem 5.6** [Goldreich2007DraftR2]: deciding undirected connectivity is in
`L`. A graph is connected when every two of its vertices are joined by a path, so the graph
without vertices is connected. The proof reduces to undirected `s`–`t` connectivity, which is in
`L` by Reingold's theorem (`USTCON_mem_L`). -/
theorem UCONN_mem_L : UCONN ∈ L encUGraph :=
  UCONN.logSpaceReducible_USTCON.mem_L USTCON_mem_L

end Cslib.Complexity
