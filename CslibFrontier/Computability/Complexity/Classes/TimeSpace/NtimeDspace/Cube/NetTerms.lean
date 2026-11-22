/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.CodeTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.FirstNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameV

/-!
# Reading a network, and the counts of the first clique, as terms (Lemma 4.3 (c))

The machine of Lemma 6.4 reads the network `G : EdgeNet ℤ (Fin V)` only through a few accessors,
and computes the groups, positions and widths of the first clique (`FirstClique.lean`) by nested
scans over the vertices and edges, with counters of `O(log s)` bits. This module gives

* the **network-access interface** `NetT` (seven terms: the numbers of edges and vertices, the two
  ends of an edge, the length of a port list, a port, and the vertex function at the bits of a
  number), with the value contract `NetAcc` (on arguments in range, the accessors denote `uN`,
  `wN`, `degN`, `portN`, `evalN` of `FirstNum.lean`, in every extension of the environment) and
  the tier contract `NetTiers` (at budget `L ≥ 16`, the counts have tier `1`, the degrees are at
  most `L`, and each accessor maps arguments of tier `1` in range to tier `1`);
* terms for the counts of Lemma 4.3 (c), each with a value lemma (`val_*`, in the sense of
  `Num.Val` of `CodeTerm.lean`: stable, with the value of `FirstNum.lean`) and a tier lemma
  (`tm_*`).

The interface has two instances: the closed programs of a `LogspaceNetFamily`
(`NetInst.lean`), run on the size `s` (their bound `(s+2)^C` is at most `2^(128 L)` and
their values are below `2^L` once `L` is a large multiple of `log₂ (s+2)`), and the block-network
terms of `NetInstBlock.lean`. Arguments are given by their values (`Val`), so value-dependent
facts (an edge number below `M`, an argument below `2^deg`) can be used by an instance.

## Main definitions

* `NetT`, `NetAcc`, `NetTiers`; `Above env E` (`E` extends `env`).
* `degCT` (`degC`), `preT` (`preC`), `blockDT` (`blockD`), `vgroupT` (`vgroupC`), `clsEqT`
  (`ClsEq`), `edgePosT` (`edgePosC`), `tgroupT` (`tgroupC`), `heCntT` (`heCnt`), `widthT`
  (`widthC`), `hePosT` (`hePosC`).

## Main results

The tiers at budget `L` (`NetTiers`, `K` of tier `1`): `degCT` `2`, `preT` `3`, `blockDT` `3`,
`vgroupT` `3`, `clsEqT` `1`, `edgePosT` `2`, `tgroupT` `1`, `heCntT` `2`, `widthT` `3`, `hePosT`
`4`. With `FirstNum.lean` (`degC_eq`, …, `widthC_eq`, `heBit_eq_hePosC`) the values are the counts
of `FirstClique.lean`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset NtimeDspace.ProgTerm NtimeDspace.ProgTerm.Term NtimeDspace.Cross

variable {w : List Bool} {L : ℕ} {env : List ℕ}

/-! ### Extensions and small helpers -/

/-- `E` extends `env` by any values. -/
def Above (env E : List ℕ) : Prop := ∃ pre, E = pre ++ env

theorem Above.refl (env : List ℕ) : Above env env := ⟨[], rfl⟩

theorem Above.trans {e1 e2 e3 : List ℕ} (h12 : Above e1 e2) (h23 : Above e2 e3) : Above e1 e3 := by
  obtain ⟨p, rfl⟩ := h12
  obtain ⟨q, rfl⟩ := h23
  exact ⟨q ++ p, by simp⟩

theorem above_at2 (pre : List ℕ) (x k : ℕ) : Above env (x :: k :: (pre ++ env)) :=
  ⟨x :: k :: pre, rfl⟩

theorem ext_above {E : List ℕ} (h : Ext L E env) : Above env E := by
  obtain ⟨p, _, rfl⟩ := h; exact ⟨p, rfl⟩

theorem Val.up {t : Term} {n : ℕ} (h : Val w env t n) {E : List ℕ} (hE : Above env E) :
    Val w E t n := by
  obtain ⟨p, rfl⟩ := hE; exact h.ext p

theorem ite_ind {P : Prop} [Decidable P] {α : Type} (a b : α) :
    (if 0 < (if P then 1 else 0) then a else b) = if P then a else b := by
  by_cases h : P <;> simp [h]

theorem ite_or (P Q : Prop) [Decidable P] [Decidable Q] :
    (if 0 < (if P then 1 else 0) + (if Q then 1 else 0) then 1 else 0) = if P ∨
        Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem ite_cls (P Q R S : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable S] :
    (if 0 < (if P then 1 else 0) * (if Q then 1 else 0) + (if R then 1 else 0) *
        (if S then 1 else 0)
      then 1 else 0) = if (P ∧ Q) ∨ (R ∧ S) then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> by_cases hS : S <;> simp
      [hP, hQ, hR, hS]

theorem ite_bool (B : Bool) (P : Prop) [Decidable P] :
    (if 0 < B.toNat then (if P then 1 else 0) else 0) = if B = true ∧ P then 1 else 0 := by
  cases B <;> simp

/-- A constant `k ≤ 3` at any tier `1 ≤ d`. -/
theorem tcst {k d : ℕ} (hk : k ≤ 3) (hd : 1 ≤ d) (hL : 16 ≤ L) : Tm w L d (const k) env :=
  (t_small hk (by omega)).mono hd

/-- A sum whose body is bounded on the counter values below the count. -/
theorem tm_sumTb {n : Term} {body : Term → Term} {N dn db : ℕ} (hn : Val w env n N)
    (tn : Tm w L dn n env)
    (hb : ∀ E, Ext L E env → ∀ y k, Val w E y k → k < N → Tm w L dn y E → Tm w L db (body y) E)
    (hL : 1 ≤ L) (hd : dn + db ≤ 32) : Tm w L (dn + db) (sumT n body) env :=
  t_sumTv' tn (V := N) (fun pre _ => ((hn.ext pre).2).le)
    (fun E he y hy hys hyv => hb E he y _ ⟨hys, rfl⟩ (by simpa using hyv [] Small.nil) hy) hL hd

/-! ### The network-access interface -/

/-- Terms reading a network: the numbers of edges and vertices, the ends of an edge, the length of
the port list of a vertex, a port, and a vertex function at the bits of a number. -/
structure NetT where
  /-- The number of edges. -/
  MT : Term
  /-- The number of vertices. -/
  VT : Term
  /-- The first end of an edge. -/
  uT : Term → Term
  /-- The second end of an edge. -/
  wT : Term → Term
  /-- The length of the port list of a vertex. -/
  degT : Term → Term
  /-- Port `j` of vertex `v` (`portT v j`). -/
  portT : Term → Term → Term
  /-- The vertex function of `v` at the bits of `A` on its ports (`evalT v A`). -/
  evalT : Term → Term → Term

variable {V : ℕ} (G : EdgeNet ℤ (Fin V))

/-- **The value contract of the accessors**: in every extension of `env`, on arguments in range,
they denote the numbers `uN`, `wN`, `degN`, `portN`, `evalN` of `G`. -/
structure NetAcc (w : List Bool) (env : List ℕ) (N : NetT) : Prop where
  vM : Val w env N.MT G.M
  vV : Val w env N.VT V
  vu : ∀ E, Above env E → ∀ a i, Val w E a i → i < G.M → Val w E (N.uT a) (uN G i)
  vw : ∀ E, Above env E → ∀ a i, Val w E a i → i < G.M → Val w E (N.wT a) (wN G i)
  vdeg : ∀ E, Above env E → ∀ a x, Val w E a x → x < V → Val w E (N.degT a) (degN G x)
  vport : ∀ E, Above env E → ∀ a b x j, Val w E a x → Val w E b j → x < V → j < degN G x →
    Val w E (N.portT a b) (portN G x j)
  veval : ∀ E, Above env E → ∀ a b x A, Val w E a x → Val w E b A → x < V → A < 2 ^ degN G x →
    Val w E (N.evalT a b) (evalN G x A)

/-- **The tier contract of the accessors** at budget `L`: the counts have tier `1`, every port
list has at most `L` entries, and the accessors map arguments of tier `1` in range to tier `1`
(so every vertex function value is below `2^L`). -/
structure NetTiers (w : List Bool) (L : ℕ) (env : List ℕ) (N : NetT) : Prop where
  hL : 16 ≤ L
  hΔ : ∀ x, (G.ports x).length ≤ L
  tM : Tm w L 1 N.MT env
  tV : Tm w L 1 N.VT env
  tu : ∀ E, Ext L E env → ∀ a i, Val w E a i → Tm w L 1 a E → i < G.M → Tm w L 1 (N.uT a) E
  tw : ∀ E, Ext L E env → ∀ a i, Val w E a i → Tm w L 1 a E → i < G.M → Tm w L 1 (N.wT a) E
  tdeg : ∀ E, Ext L E env → ∀ a x, Val w E a x → Tm w L 1 a E → x < V → Tm w L 1 (N.degT a) E
  tport : ∀ E, Ext L E env → ∀ a b x j, Val w E a x → Tm w L 1 a E → Val w E b j → Tm w L 1 b E →
    x < V → j < degN G x → Tm w L 1 (N.portT a b) E
  teval : ∀ E, Ext L E env → ∀ a b x A, Val w E a x → Tm w L 1 a E → Val w E b A → Tm w L 1 b E →
    x < V → A < 2 ^ degN G x → Tm w L 1 (N.evalT a b) E

variable {G} {N : NetT}

theorem NetAcc.up (h : NetAcc G w env N) {E : List ℕ} (hE : Above env E) : NetAcc G w E N where
  vM := h.vM.up hE
  vV := h.vV.up hE
  vu := fun E' h' => h.vu E' (hE.trans h')
  vw := fun E' h' => h.vw E' (hE.trans h')
  vdeg := fun E' h' => h.vdeg E' (hE.trans h')
  vport := fun E' h' => h.vport E' (hE.trans h')
  veval := fun E' h' => h.veval E' (hE.trans h')

theorem NetTiers.up (h : NetTiers G w L env N) {E : List ℕ} (hE : Ext L E env) :
    NetTiers G w L E N where
  hL := h.hL
  hΔ := h.hΔ
  tM := h.tM.ext hE
  tV := h.tV.ext hE
  tu := fun E' h' => h.tu E' (h'.trans hE)
  tw := fun E' h' => h.tw E' (h'.trans hE)
  tdeg := fun E' h' => h.tdeg E' (h'.trans hE)
  tport := fun E' h' => h.tport E' (h'.trans hE)
  teval := fun E' h' => h.teval E' (h'.trans hE)

/-! ### Degrees and the ports before a vertex -/

/-- The number of edges at `v` (`degC`). -/
def degCT (N : NetT) (v : Term) : Term :=
  sumT N.MT fun e => lt (const 0) (add (eqT (N.uT e) v) (eqT (N.wT e) v))

/-- The ports of the vertices before `v` (`preC`). -/
def preT (N : NetT) (v : Term) : Term :=
  sumT N.VT fun u => ite (lt u v) (degCT N u) (const 0)

/-- `D₀ = max 1 ⌈2M/K⌉` (`blockD`). -/
def blockDT (N : NetT) (KT : Term) : Term :=
  cmaxT (const 1) (div (sub (add (mul (const 2) N.MT) KT) (const 1)) KT)

/-- The vertex group of `v` (`vgroupC`). -/
def vgroupT (N : NetT) (KT v : Term) : Term :=
  cminT (sub KT (const 1)) (div (preT N v) (blockDT N KT))

variable {vT KT : Term} {v K : ℕ}

theorem val_degCT (hA : NetAcc G w env N) (hv : Val w env vT v) :
    Val w env (degCT N vT) (degC G v) := by
  refine val_sumT (g := fun e => if uN G e = v ∨ wN G e = v then 1 else 0) hA.vM
    fun pre x k hk => ?_
  have hE := above_at2 (env := env) pre x k
  have hi := val_idx (w := w) (pre ++ env) x k
  exact (val_lt (val_const 0) (val_add (val_eqT (hA.vu _ hE _ _ hi hk) (hv.at2 pre x k))
    (val_eqT (hA.vw _ hE _ _ hi hk) (hv.at2 pre x k)))).congr (ite_or _ _)

theorem tm_degCT {dv : ℕ} (hA : NetAcc G w env N) (hT : NetTiers G w L env N)
    (tv : Tm w L dv vT env) : Tm w L 2 (degCT N vT) env := by
  have hL := hT.hL
  refine tm_sumTb (dn := 1) (db := 1) hA.vM hT.tM (fun E he y k hy hk ty => ?_) (by omega)
    (by norm_num)
  exact t_lt (tcst (k := 0) (by norm_num) le_rfl hL)
    (tm_add (d := 2) (t_eqT' (hT.tu E he y k hy ty hk) (tv.ext he) (by omega))
      (t_eqT' (hT.tw E he y k hy ty hk) (tv.ext he) (by omega)) le_rfl le_rfl (by norm_num)
      (by omega)) (by omega)

theorem val_preT (hA : NetAcc G w env N) (hv : Val w env vT v) :
    Val w env (preT N vT) (preC G v) := by
  refine val_sumT (g := fun u => if u < v then degC G u else 0) hA.vV fun pre x k hk => ?_
  have hE := above_at2 (env := env) pre x k
  have hi := val_idx (w := w) (pre ++ env) x k
  exact (val_ite (val_lt hi (hv.at2 pre x k)) (val_degCT (hA.up hE) hi) (val_const 0)).congr
    (ite_ind _ _)

theorem tm_preT {dv : ℕ} (hA : NetAcc G w env N) (hT : NetTiers G w L env N)
    (tv : Tm w L dv vT env) : Tm w L 3 (preT N vT) env := by
  have hL := hT.hL
  refine tm_sumTb (dn := 1) (db := 2) hA.vV hT.tV (fun E he y k hy hk ty => ?_) (by omega)
    (by norm_num)
  exact tm_ite (t_lt ty (tv.ext he) (by omega)) (tm_degCT (hA.up (ext_above he)) (hT.up he) ty)
    (tcst (by norm_num) (by norm_num) hL)

theorem val_blockDT (hA : NetAcc G w env N) (hK : Val w env KT K) :
    Val w env (blockDT N KT) (blockD G K) :=
  val_cmaxT (val_const 1) (val_div (val_sub (val_add (val_mul (val_const 2) hA.vM) hK)
    (val_const 1)) hK)

theorem tm_blockDT (hT : NetTiers G w L env N) (tK : Tm w L 1 KT env) :
    Tm w L 3 (blockDT N KT) env := by
  have hL := hT.hL
  exact tm_cmaxT (tcst (by norm_num) (by norm_num) hL)
    (t_div (t_sub (tm_add (d := 3) (t_mul (t_small (k := 2) (by norm_num) (by omega)) hT.tM
      (by norm_num)) tK (by norm_num) (by norm_num) (by norm_num) (by omega))
      (tcst (k := 1) (by norm_num) le_rfl hL)) tK) (by omega)

theorem val_vgroupT (hA : NetAcc G w env N) (hK : Val w env KT K) (hv : Val w env vT v) :
    Val w env (vgroupT N KT vT) (vgroupC G K v) :=
  val_cminT (val_sub hK (val_const 1)) (val_div (val_preT hA hv) (val_blockDT hA hK))

theorem tm_vgroupT {dv : ℕ} (hA : NetAcc G w env N) (hT : NetTiers G w L env N)
    (tK : Tm w L 1 KT env) (tv : Tm w L dv vT env) : Tm w L 3 (vgroupT N KT vT) env := by
  have hL := hT.hL
  exact tm_cminT ((t_sub tK (tcst (k := 1) (by norm_num) le_rfl hL)).mono (by norm_num))
    (t_div (tm_preT hA hT tv) (tm_blockDT hT tK)) (by omega)

/-! ### Edges: positions and test groups -/

/-- `1` if the pairs `{a, b}` and `{c, d}` are equal (`ClsEq`). -/
def clsEqT (a b c d : Term) : Term :=
  lt (const 0) (add (mul (eqT a c) (eqT b d)) (mul (eqT a d) (eqT b c)))

theorem val_clsEqT {a b c d : Term} {A B C D : ℕ} (ha : Val w env a A) (hb : Val w env b B)
    (hc : Val w env c C) (hd : Val w env d D) :
    Val w env (clsEqT a b c d) (if ClsEq A B C D then 1 else 0) :=
  (val_lt (val_const 0) (val_add (val_mul (val_eqT ha hc) (val_eqT hb hd))
    (val_mul (val_eqT ha hd) (val_eqT hb hc)))).congr (ite_cls _ _ _ _)

theorem tm_clsEqT {a b c d : Term} {da db dc dd : ℕ} (ta : Tm w L da a env) (tb : Tm w L db b env)
    (tc : Tm w L dc c env) (td : Tm w L dd d env) (hL : 16 ≤ L) : Tm w L 1 (clsEqT a b c d) env :=
  t_lt (tcst (k := 0) (by norm_num) le_rfl hL)
    (tm_add (d := 3) (t_mul (t_eqT' ta tc (by omega)) (t_eqT' tb td (by omega)) (by norm_num))
      (t_mul (t_eqT' ta td (by omega)) (t_eqT' tb tc (by omega)) (by norm_num)) (by norm_num)
      (by norm_num) (by norm_num) (by omega)) (by omega)

/-- The position of edge `e` among the edges between the groups of its ends (`edgePosC`). -/
def edgePosT (N : NetT) (KT e : Term) : Term :=
  sumT e fun e' => clsEqT (vgroupT N KT (N.uT e')) (vgroupT N KT (N.wT e'))
    (vgroupT N KT (N.uT e)) (vgroupT N KT (N.wT e))

/-- The test group of edge `e` (`tgroupC`). -/
def tgroupT (N : NetT) (KT e : Term) : Term := mod (edgePosT N KT e) KT

variable {eT : Term} {e : ℕ}

theorem val_edgePosT (hA : NetAcc G w env N) (hK : Val w env KT K) (he : Val w env eT e)
    (heM : e < G.M) : Val w env (edgePosT N KT eT) (edgePosC G K e) := by
  refine val_sumT (g := fun e' => if ClsEq (vgroupC G K (uN G e')) (vgroupC G K (wN G e'))
    (vgroupC G K (uN G e)) (vgroupC G K (wN G e)) then 1 else 0) he fun pre x k hk => ?_
  have hE := above_at2 (env := env) pre x k
  have hi := val_idx (w := w) (pre ++ env) x k
  have hA' := hA.up hE
  have hK' := hK.at2 pre x k
  have he' := he.at2 pre x k
  exact val_clsEqT (val_vgroupT hA' hK' (hA.vu _ hE _ _ hi (by omega)))
    (val_vgroupT hA' hK' (hA.vw _ hE _ _ hi (by omega)))
    (val_vgroupT hA' hK' (hA.vu _ hE _ _ he' heM)) (val_vgroupT hA' hK' (hA.vw _ hE _ _ he' heM))

theorem tm_edgePosT (hA : NetAcc G w env N) (hT : NetTiers G w L env N) (tK : Tm w L 1 KT env)
    (he : Val w env eT e) (te : Tm w L 1 eT env) (heM : e < G.M) :
    Tm w L 2 (edgePosT N KT eT) env := by
  have hL := hT.hL
  refine tm_sumTb (dn := 1) (db := 1) he te (fun E hE y k hy hk ty => ?_) (by omega) (by norm_num)
  have hA' := hA.up (ext_above hE)
  have hT' := hT.up hE
  have tK' := tK.ext hE
  have he' := he.up (ext_above hE)
  have te' := te.ext hE
  exact tm_clsEqT (tm_vgroupT hA' hT' tK' (hT.tu E hE y k hy ty (by omega)))
    (tm_vgroupT hA' hT' tK' (hT.tw E hE y k hy ty (by omega)))
    (tm_vgroupT hA' hT' tK' (hT.tu E hE eT e he' te' heM))
    (tm_vgroupT hA' hT' tK' (hT.tw E hE eT e he' te' heM)) hL

theorem val_tgroupT (hA : NetAcc G w env N) (hK : Val w env KT K) (he : Val w env eT e)
    (heM : e < G.M) : Val w env (tgroupT N KT eT) (tgroupC G K e) :=
  val_mod (val_edgePosT hA hK he heM) hK

theorem tm_tgroupT (hA : NetAcc G w env N) (hT : NetTiers G w L env N) (hK : Val w env KT K)
    (tK : Tm w L 1 KT env) (hK1 : 1 ≤ K) (he : Val w env eT e) (te : Tm w L 1 eT env)
    (heM : e < G.M) : Tm w L 1 (tgroupT N KT eT) env :=
  t_mod (tm_edgePosT hA hT tK he te heM) tK fun pre _ => by rw [(hK.ext pre).2]; exact hK1

/-! ### Half-edges and widths -/

/-- The number of half-edges of edge `e` on the pair (vertex group `i`, test group `τ`)
(`heCnt`). -/
def heCntT (N : NetT) (KT i τ e : Term) : Term :=
  ite (eqT (tgroupT N KT e) τ)
    (add (eqT (vgroupT N KT (N.uT e)) i) (eqT (vgroupT N KT (N.wT e)) i)) (const 0)

/-- The width of the pair (vertex group `i`, test group `τ`) (`widthC`). -/
def widthT (N : NetT) (KT i τ : Term) : Term := sumT N.MT fun e => heCntT N KT i τ e

/-- The position of the half-edge `(e, b)` in its list (`hePosC`); `b` is `0` or `1`. -/
def hePosT (N : NetT) (KT i τ e b : Term) : Term :=
  add (sumT e fun e' => heCntT N KT i τ e') (ite b (eqT (vgroupT N KT (N.uT e)) i) (const 0))

variable {iT τT : Term} {i τ : ℕ}

theorem val_heCntT (hA : NetAcc G w env N) (hK : Val w env KT K) (hi : Val w env iT i)
    (hτ : Val w env τT τ) (he : Val w env eT e) (heM : e < G.M) :
    Val w env (heCntT N KT iT τT eT) (heCnt G K i τ e) :=
  (val_ite (val_eqT (val_tgroupT hA hK he heM) hτ)
    (val_add (val_eqT (val_vgroupT hA hK (hA.vu _ (Above.refl _) _ _ he heM)) hi)
      (val_eqT (val_vgroupT hA hK (hA.vw _ (Above.refl _) _ _ he heM)) hi)) (val_const 0)).congr
    (ite_ind _ _)

theorem tm_heCntT {di dτ : ℕ} (hA : NetAcc G w env N) (hT : NetTiers G w L env N)
    (hK : Val w env KT K) (tK : Tm w L 1 KT env) (hK1 : 1 ≤ K) (ti : Tm w L di iT env)
    (tτ : Tm w L dτ τT env) (he : Val w env eT e) (te : Tm w L 1 eT env) (heM : e < G.M) :
    Tm w L 2 (heCntT N KT iT τT eT) env := by
  have hL := hT.hL
  exact tm_ite (t_eqT' (tm_tgroupT hA hT hK tK hK1 he te heM) tτ (by omega))
    (tm_add (t_eqT' (tm_vgroupT hA hT tK (hT.tu _ (Ext.refl _) _ _ he te heM)) ti (by omega))
      (t_eqT' (tm_vgroupT hA hT tK (hT.tw _ (Ext.refl _) _ _ he te heM)) ti (by omega))
      le_rfl le_rfl (by norm_num) (by omega)) (tcst (by norm_num) (by norm_num) hL)

theorem val_widthT (hA : NetAcc G w env N) (hK : Val w env KT K) (hi : Val w env iT i)
    (hτ : Val w env τT τ) : Val w env (widthT N KT iT τT) (widthC G K i τ) :=
  val_sumT (g := heCnt G K i τ) hA.vM fun pre x k hk =>
    val_heCntT (hA.up (above_at2 pre x k)) (hK.at2 pre x k) (hi.at2 pre x k) (hτ.at2 pre x k)
      (val_idx _ x k) hk

theorem tm_widthT {di dτ : ℕ} (hA : NetAcc G w env N) (hT : NetTiers G w L env N)
    (hK : Val w env KT K) (tK : Tm w L 1 KT env) (hK1 : 1 ≤ K) (ti : Tm w L di iT env)
    (tτ : Tm w L dτ τT env) : Tm w L 3 (widthT N KT iT τT) env := by
  have hL := hT.hL
  exact tm_sumTb (dn := 1) (db := 2) hA.vM hT.tM (fun E hE y k hy hk ty =>
    tm_heCntT (hA.up (ext_above hE)) (hT.up hE) (hK.up (ext_above hE)) (tK.ext hE) hK1 (ti.ext hE)
        (tτ.ext hE)
      hy ty hk) (by omega) (by norm_num)

variable {bT : Term} {b : Bool}

theorem val_hePosT (hA : NetAcc G w env N) (hK : Val w env KT K) (hi : Val w env iT i)
    (hτ : Val w env τT τ) (he : Val w env eT e) (heM : e < G.M) (hb : Val w env bT b.toNat) :
    Val w env (hePosT N KT iT τT eT bT) (hePosC G K i τ e b) := by
  have hs : Val w env (sumT eT fun e' => heCntT N KT iT τT e') (∑ k ∈ range e, heCnt G K i τ k) :=
    val_sumT (g := heCnt G K i τ) he fun pre x k hk =>
      val_heCntT (hA.up (above_at2 pre x k)) (hK.at2 pre x k) (hi.at2 pre x k) (hτ.at2 pre x k)
        (val_idx _ x k) (by omega)
  exact val_add hs ((val_ite hb (val_eqT (val_vgroupT hA hK (hA.vu _ (Above.refl _) _ _ he heM)) hi)
    (val_const 0)).congr (ite_bool _ _))

theorem tm_hePosT {di dτ db : ℕ} (hA : NetAcc G w env N) (hT : NetTiers G w L env N)
    (hK : Val w env KT K) (tK : Tm w L 1 KT env) (hK1 : 1 ≤ K) (ti : Tm w L di iT env)
    (tτ : Tm w L dτ τT env) (he : Val w env eT e) (te : Tm w L 1 eT env) (heM : e < G.M)
    (tb : Tm w L db bT env) : Tm w L 4 (hePosT N KT iT τT eT bT) env := by
  have hL := hT.hL
  have hs : Tm w L 3 (sumT eT fun e' => heCntT N KT iT τT e') env :=
    tm_sumTb (dn := 1) (db := 2) he te (fun E hE y k hy hk ty =>
      tm_heCntT (hA.up (ext_above hE)) (hT.up hE) (hK.up (ext_above hE)) (tK.ext hE) hK1 (ti.ext hE)
        (tτ.ext hE) hy ty (by omega)) (by omega) (by norm_num)
  exact tm_add hs (tm_ite tb (t_eqT' (tm_vgroupT hA hT tK (hT.tu _ (Ext.refl _) _ _ he te heM)) ti
    (by omega)) (tcst (by norm_num) le_rfl hL)) (by norm_num) (by norm_num) (by norm_num) (by omega)

end Cslib.Complexity.NtimeDspace.Cube.Num
