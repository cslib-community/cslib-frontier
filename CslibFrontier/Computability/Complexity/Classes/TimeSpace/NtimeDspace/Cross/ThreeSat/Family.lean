/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.NetFamily
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.BoundsAccess

/-!
# The 3-SAT networks have logspace access (Definition 2.1)

`threeSatFamily` is the family of the networks `(rawW w s).net` of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Net.lean`, as a
`LogspaceNetFamily`: a word `w` describes a network at size `s` when `|w| ≤ (s + 2)^2`, and that
network is read from `w` by `rawW` (for `w = frame x ++ encSlots φ` it is the degree-3 network of
`φ`, `rawW_enc`/`value_net_enc`). The family has at most `6s` edges, `7s` vertices, degree at most
`3` and `0/1` vertex functions, and its accessors are the closed programs obtained from the terms of
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Access.lean`,
with every value arising in their evaluation at most `(s + 2)^10`.

## Main definitions

* `threeSatFamily : LogspaceNetFamily`.

## Main results

* `threeSatFamily_value`: for an encoded 3-CNF formula `φ` in which every variable occurs, with
  `|w| ≤ (s + 2)^2` and at most `s` clauses, the network of the family has value `numModels φ`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset

/-! ### The closed accessor programs -/

/-- The number of edges, on `[s]`. -/
def edgesP : Prog := closeAt 1 (edgesT (lvl 0) 1)
/-- The number of vertices, on `[s]`. -/
def vertsP : Prog := closeAt 1 (vertsT (lvl 0) 1)
/-- The row end of an edge, on `[i, s]`. -/
def endUP : Prog := closeAt 2 (endUT (lvl 0) (lvl 1) 2)
/-- The column end of an edge, on `[i, s]`. -/
def endWP : Prog := closeAt 2 (endWT (lvl 0) (lvl 1) 2)
/-- The degree of a vertex, on `[v, s]`. -/
def degP : Prog := closeAt 2 (degT' (lvl 0) (lvl 1) 2)
/-- The `j`-th port of a vertex, on `[v, j, s]`. -/
def portP : Prog := closeAt 3 (portT' (lvl 0) (lvl 2) (lvl 1) 3)
/-- The vertex function of `v` at the bits of `A`, on `[v, A, s]`. -/
def funP : Prog := closeAt 3 (funT (lvl 0) (lvl 2) (lvl 1) 3)

section Specs

variable {w : List Bool} {s : ℕ}

theorem sz_pow (s : ℕ) : Sz s ((s + 2) ^ 10) := by
  constructor
  have h : 64 ≤ (s + 2) ^ 6 :=
    (Nat.pow_le_pow_left (show 2 ≤ s + 2 by omega) 6).trans' (by norm_num)
  calc 64 * (s + 2) ^ 4 ≤ (s + 2) ^ 6 * (s + 2) ^ 4 := Nat.mul_le_mul_right _ h
    _ = (s + 2) ^ 10 := by rw [← pow_add]

/-- Running a closed term: its value is the program's value, and its bound gives `Bounded`. -/
theorem run_closeAt {t : Term} {n : ℕ} {env : List ℕ} (hn : env.length = n) {v M : ℕ}
    (hv : Val w t env v) (hb : Bd w M t env) :
    (closeAt n (t n)).eval w env = v ∧ (closeAt n (t n)).Bounded w M env := by
  subst hn
  refine ⟨?_, ?_⟩
  · rw [eval_closeAt _ _ env rfl]; exact hv.eq
  · rw [bounded_closeAt _ _ env rfl]; exact hb.bnd

theorem val_s1 : Val w (lvl 0) [s] s := val_lvl (by simp)
theorem val_s2 (x : ℕ) : Val w (lvl 0) [x, s] s := val_lvl (by simp)
theorem val_x2 (x : ℕ) : Val w (lvl 1) [x, s] x := val_lvl (by simp)
theorem val_s3 (x y : ℕ) : Val w (lvl 0) [x, y, s] s := val_lvl (by simp)
theorem val_y3 (x y : ℕ) : Val w (lvl 1) [x, y, s] y := val_lvl (by simp)
theorem val_x3 (x y : ℕ) : Val w (lvl 2) [x, y, s] x := val_lvl (by simp)

theorem ofFn_net_eq (v : Fin (7 * (rawW w s).m)) (A : ℕ) :
    (List.ofFn fun j : Fin (((rawW w s).net ℤ).ports v).length => A.testBit j) =
      Raw.bitsAt A ((rawW w s).portsN v).length := by
  have hl : (((rawW w s).net ℤ).ports v).length = ((rawW w s).portsN v).length := by
    rw [← Raw.map_val_ports ℤ v, List.length_map]
  rw [List.ofFn_congr hl]
  rfl

end Specs

/-! ### The family -/

/-- **The 3-SAT networks as a family with logspace access** (Definition 2.1). -/
def threeSatFamily : LogspaceNetFamily where
  Mem w s := w.length ≤ bnd s
  V w s := 7 * (rawW w s).m
  net w s := (rawW w s).net ℤ
  C := 10
  length_le w s h := h.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
  edges_le w s _ := by
    have := rawW_m_le w s
    change 6 * (rawW w s).m ≤ 10 * (s + 1)
    omega
  verts_le w s _ := by
    have h1 := rawW_m_le w s
    have h2 : s + 2 ≤ (s + 2) ^ 10 := Nat.le_self_pow (by norm_num) _
    have h3 : 8 * (s + 2) ≤ (s + 2) ^ 10 := by
      have : 8 ≤ (s + 2) ^ 9 := (Nat.pow_le_pow_left (show 2 ≤ s + 2 by omega)
          9).trans' (by norm_num)
      calc 8 * (s + 2) ≤ (s + 2) ^ 9 * (s + 2) := Nat.mul_le_mul_right _ this
        _ = (s + 2) ^ 10 := by ring
    omega
  deg_le w s _ v := (Raw.net_degree_le ℤ v).trans (by omega)
  eval_mem w s _ v x _ := by
    change (0 : ℤ) ≤ (if _ then 1 else 0) ∧ (if _ then 1 else 0 : ℤ) ≤ ((s + 2) ^ 10 : ℕ)
    have : (1 : ℤ) ≤ ((s + 2) ^ 10 : ℕ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
    split_ifs <;> constructor <;> omega
  ports_nodup w s _ v := Raw.nodup_net_ports ℤ v
  edgesP := edgesP
  vertsP := vertsP
  endUP := endUP
  endWP := endWP
  degP := degP
  portP := portP
  funP := funP
  edgesP_closed := closed_closeAt _ _
  vertsP_closed := closed_closeAt _ _
  endUP_closed := closed_closeAt _ _
  endWP_closed := closed_closeAt _ _
  degP_closed := closed_closeAt _ _
  portP_closed := closed_closeAt _ _
  funP_closed := closed_closeAt _ _
  edgesP_spec w s _ :=
    run_closeAt rfl (val_edgesT val_s1) (bd_edgesT val_s1 (bd_lvl _ _) (sz_pow s))
  vertsP_spec w s _ :=
    run_closeAt rfl (val_vertsT val_s1) (bd_vertsT val_s1 (bd_lvl _ _) (sz_pow s))
  endUP_spec w s _ i hi :=
    run_closeAt rfl (val_endUT (val_s2 i) (val_x2 i))
      (bd_endUT (val_s2 i) (bd_lvl _ _) (sz_pow s) (val_x2 i) (bd_lvl _ _) hi)
  endWP_spec w s _ i hi :=
    run_closeAt rfl (val_endWT (val_s2 i) (val_x2 i))
      (bd_endWT (val_s2 i) (bd_lvl _ _) (sz_pow s) (val_x2 i) (bd_lvl _ _) hi)
  degP_spec w s _ v hv := by
    have := run_closeAt rfl (val_degT' (val_s2 v) (val_x2 v))
      (bd_degT' (val_s2 v) (bd_lvl _ _) (sz_pow s) (val_x2 v) (bd_lvl _ _) hv)
    rw [← Raw.map_val_ports ℤ ⟨v, hv⟩, List.length_map] at this
    exact this
  portP_spec w s _ v hv j hj := by
    have hj' : j < ((rawW w s).portsN v).length := by
      rw [← Raw.map_val_ports ℤ ⟨v, hv⟩, List.length_map]; exact hj
    have hj3 : j ≤ 3 := (Raw.portsN_length_le v).trans' hj'.le
    have := run_closeAt rfl (val_portT' (val_s3 v j) (val_x3 v j) (val_y3 v j))
      (bd_portT' (val_s3 v j) (bd_lvl _ _) (sz_pow s) (val_x3 v j) (bd_lvl _ _) hv (val_y3 v j)
        (bd_lvl _ _) hj3)
    refine ⟨this.1.trans ?_, this.2⟩
    rw [← Raw.getElem_portsN hj']
    have h := congrArg (fun l => l[j]?) (Raw.map_val_ports ℤ (d := rawW w s) ⟨v, hv⟩)
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj',
      Option.map_some, Option.some.injEq] at h
    rw [← h]; rfl
  funP_spec w s _ v hv A _ := by
    have := run_closeAt rfl (val_funT (val_s3 v A) (val_x3 v A) (val_y3 v A))
      (bd_funT (val_s3 v A) (bd_lvl _ _) (sz_pow s) (val_x3 v A) (bd_lvl _ _) hv (val_y3 v A)
        (bd_lvl _ _))
    have e : funP.eval w [v, A, s] = (rawW w s).funN v A := this.1
    refine ⟨?_, this.2⟩
    rw [e, Raw.net_eval, ofFn_net_eq, Raw.funN]
    cases (rawW w s).evalN v (Raw.bitsAt A ((rawW w s).portsN v).length) <;> rfl

/-- **The value of the network of an encoded formula** in the family. -/
theorem threeSatFamily_value (x : List Bool) {n : ℕ} (φ : Cslib.Logic.PL.CNF (Fin n)) (s : ℕ)
    (h3 : ∀ C ∈ φ, C.length ≤ 3) (hocc : EveryVarOccurs φ)
    (hw : (Turing.MultiTapeTM.frame x ++ encSlots φ).length ≤ bnd s) (hm : φ.length ≤ s) :
    (threeSatFamily.net (Turing.MultiTapeTM.frame x ++ encSlots φ) s).value = (numModels φ : ℤ) :=
  value_net_enc ℤ x φ s h3 hocc hw hm

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
