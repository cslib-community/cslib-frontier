/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgPieces
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.NatList

/-!
# List operations as program terms

Program terms for the head, the tail and the cons of codes of `NatList.enc`,
together with the pure functions they compute (`hdF`, `tlF`, `consF`).
Arguments are variables (`lvl a`); larger arguments are bound with `letT`
first, which keeps both the meaning and the value bounds of a term local.

Every value arising in `consT x l` is at most the result (when `l ≥ 1`), and
every value arising in `hdT e` or `tlT e` is at most `e`, when `e` is the code of
a nonempty list (`bnd_consT`, `bnd_hdT`, `bnd_tlT`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NtimeDspace.ProgTerm Term NatList

/-! ### Pure functions -/

/-- One step of counting the trailing ones of `e`. -/
def tOnesStep (e acc i : ℕ) : ℕ :=
  if acc < i then acc else if i < acc then acc else if e.testBit i then i + 1 else acc

/-- The number of trailing ones of `e`, capped at `e`. -/
def tOnesF (e : ℕ) : ℕ := (List.range e).foldl (tOnesStep e) 0

/-- One step of computing the bit length of `x`. -/
def sizeStep (x acc i : ℕ) : ℕ := if x.testBit i then i + 1 else acc

/-- The bit length of `x`. -/
def sizeF (x : ℕ) : ℕ := (List.range x).foldl (sizeStep x) 0

/-- The head of a code. -/
def hdF (e : ℕ) : ℕ := e / 2 ^ (tOnesF e + 1) % 2 ^ tOnesF e

/-- The tail of a code. -/
def tlF (e : ℕ) : ℕ := e / 2 ^ (tOnesF e + tOnesF e + 1)

/-- The cons of codes. -/
def consF (x l : ℕ) : ℕ :=
  (2 ^ sizeF x - 1) + 2 ^ (sizeF x + 1) * x + 2 ^ (sizeF x + sizeF x + 1) * l

theorem size_mod_two_pow_succ (x m : ℕ) :
    (x % 2 ^ (m + 1)).size = if x.testBit m then m + 1 else (x % 2 ^ m).size := by
  have hsplit : x % 2 ^ (m + 1) = x % 2 ^ m + 2 ^ m * (x.testBit m).toNat := by
    rw [Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ m) with h | h <;> simp [h, Nat.mul_comm]
  have hlt : x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
  split_ifs with hb
  · rw [hsplit, hb, Bool.toNat_true, Nat.mul_one]
    apply le_antisymm
    · exact Nat.size_le.mpr (by rw [Nat.pow_succ]; omega)
    · exact Nat.lt_size.mpr (by omega)
  · rw [hsplit, show x.testBit m = false by simpa using hb]; simp

theorem foldl_sizeStep (x : ℕ) : ∀ m, (List.range m).foldl (sizeStep x) 0 = (x % 2 ^ m).size
  | 0 => by simp [Nat.mod_one]
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_sizeStep x m, size_mod_two_pow_succ]
    simp [sizeStep]

theorem sizeF_eq (x : ℕ) : sizeF x = x.size := by
  rw [sizeF, foldl_sizeStep, Nat.mod_eq_of_lt Nat.lt_two_pow_self]

theorem foldl_tOnesStep {e n : ℕ} (hset : ∀ i < n, e.testBit i = true) (hclr : e.testBit n = false)
    :
    ∀ m, (List.range m).foldl (tOnesStep e) 0 = min m n
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_tOnesStep hset hclr m]
    simp only [List.foldl_cons, List.foldl_nil, tOnesStep]
    rcases Nat.lt_trichotomy m n with h | h | h
    · rw [min_eq_left h.le, if_neg (lt_irrefl m), if_neg (lt_irrefl m), if_pos (hset m h)]
      omega
    · subst h
      rw [min_self, if_neg (lt_irrefl m), if_neg (lt_irrefl m), hclr]
      simp
    · rw [min_eq_right h.le, if_pos h]
      omega

theorem tOnesF_enc_cons (x : ℕ) (l : List ℕ) : tOnesF (enc (x :: l)) = x.size := by
  rw [tOnesF, foldl_tOnesStep (fun i hi => testBit_enc_cons_lt x l hi) (testBit_enc_cons_size x l),
    min_eq_right (size_lt_enc_cons x l).le]

@[simp] theorem hdF_enc_cons (x : ℕ) (l : List ℕ) : hdF (enc (x :: l)) = x := by
  rw [hdF, tOnesF_enc_cons, enc_cons_head]

@[simp] theorem tlF_enc_cons (x : ℕ) (l : List ℕ) : tlF (enc (x :: l)) = enc l := by
  rw [tlF, tOnesF_enc_cons, show x.size + x.size + 1 = 2 * x.size + 1 by ring, enc_cons_tail]

@[simp] theorem consF_enc (x : ℕ) (l : List ℕ) : consF x (enc l) = enc (x :: l) := by
  rw [consF, sizeF_eq, enc_cons, show x.size + x.size + 1 = 2 * x.size + 1 by ring]

theorem two_pow_tOnesF_le (x : ℕ) (l : List ℕ) :
    2 ^ (tOnesF (enc (x :: l)) + tOnesF (enc (x :: l)) + 1) ≤ enc (x :: l) := by
  rw [tOnesF_enc_cons, show x.size + x.size + 1 = 2 * x.size + 1 by ring]
  exact two_pow_le_enc_cons x l

/-! ### Terms -/

/-- The number of trailing ones. -/
def tOnesT (e : Term) : Term :=
  foldT e (const 0) fun acc i =>
    ite (lt acc i) acc (ite (lt i acc) acc (ite (bit e i) (add i (const 1)) acc))

/-- The bit length. -/
def sizeT (x : Term) : Term :=
  foldT x (const 0) fun acc i => ite (bit x i) (add i (const 1)) acc

/-- The head of a code. -/
def hdT (e : Term) : Term :=
  letT (tOnesT e) fun n => mod (div e (pow2 (add n (const 1)))) (pow2 n)

/-- The tail of a code. -/
def tlT (e : Term) : Term :=
  letT (tOnesT e) fun n => div e (pow2 (add (add n n) (const 1)))

/-- The cons of codes. -/
def consT (x l : Term) : Term :=
  letT (sizeT x) fun n =>
    add (add (sub (pow2 n) (const 1)) (mul (pow2 (add n (const 1))) x))
      (mul (pow2 (add (add n n) (const 1))) l)

variable {w : List Bool} {B : ℕ}

theorem lvl_cons {a : ℕ} {env : List ℕ} (ha : a < env.length) (x : ℕ) :
    (lvl a).denote w (x :: env) = (lvl a).denote w env :=
  (stableAt_lvl ha).cons x

theorem lvl_cons₂ {a : ℕ} {env : List ℕ} (ha : a < env.length) (x y : ℕ) :
    (lvl a).denote w (x :: y :: env) = (lvl a).denote w env :=
  (stableAt_lvl ha).cons₂ x y

theorem bnd_ite_of {c t e : Term} {env : List ℕ} (hc : c.Bnd w B env) (ht : t.Bnd w B env)
    (he : e.Bnd w B env) : (ite c t e).Bnd w B env := by
  rw [bnd_ite]; exact ⟨hc, by split_ifs <;> assumption⟩

theorem denote_tOnesT {a : ℕ} {env : List ℕ} (ha : a < env.length) :
    (tOnesT (lvl a)).denote w env = tOnesF ((lvl a).denote w env) := by
  rw [tOnesT, denote_foldT, denote_const,
    foldAcc_eq _ env (tOnesStep ((lvl a).denote w env)) (fun acc k => ?_), tOnesF]
  simp only [denote_ite, denote_lt, denote_bit, denote_add, denote_const, denote_lvl_acc,
    denote_lvl_index, lvl_cons₂ ha, tOnesStep]
  by_cases h1 : acc < k
  · simp [h1]
  · by_cases h2 : k < acc
    · simp [h1, h2]
    · cases hb : ((lvl a).denote w env).testBit k <;> simp [h1, h2]

theorem denote_sizeT {a : ℕ} {env : List ℕ} (ha : a < env.length) :
    (sizeT (lvl a)).denote w env = ((lvl a).denote w env).size := by
  rw [sizeT, denote_foldT, denote_const,
    foldAcc_eq _ env (sizeStep ((lvl a).denote w env)) (fun acc k => ?_), ← sizeF, sizeF_eq]
  simp only [denote_ite, denote_bit, denote_add, denote_const, denote_lvl_acc,
    denote_lvl_index, lvl_cons₂ ha, sizeStep]
  cases ((lvl a).denote w env).testBit k <;> simp

theorem denote_hdT {a : ℕ} {env : List ℕ} (ha : a < env.length) :
    (hdT (lvl a)).denote w env = hdF ((lvl a).denote w env) := by
  simp only [hdT, denote_letT, denote_mod, denote_div, denote_pow2, denote_add, denote_const,
    denote_lvl_let, lvl_cons ha, denote_tOnesT ha, hdF]

theorem denote_tlT {a : ℕ} {env : List ℕ} (ha : a < env.length) :
    (tlT (lvl a)).denote w env = tlF ((lvl a).denote w env) := by
  simp only [tlT, denote_letT, denote_div, denote_pow2, denote_add, denote_const,
    denote_lvl_let, lvl_cons ha, denote_tOnesT ha, tlF]

theorem denote_consT {a b : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length) :
    (consT (lvl a) (lvl b)).denote w env = consF ((lvl a).denote w env) ((lvl b).denote w env) := by
  simp only [consT, denote_letT, denote_mul, denote_sub, denote_pow2, denote_add, denote_const,
    denote_lvl_let, lvl_cons ha, lvl_cons hb, denote_sizeT ha, consF, sizeF_eq]

/-! ### Value bounds -/

theorem bnd_tOnesT {a : ℕ} {env : List ℕ} (ha : a < env.length)
    (hB : (lvl a).denote w env ≤ B) : (tOnesT (lvl a)).Bnd w B env := by
  rw [tOnesT, bnd_foldT]
  refine ⟨trivial, Nat.zero_le _, hB, fun k hk => ?_⟩
  refine bnd_ite_of (by simp) trivial (bnd_ite_of (by simp) trivial
    (bnd_ite_of (by simp) ?_ trivial))
  rw [bnd_add]
  simp only [denote_lvl_index, denote_const, bnd_lvl, bnd_const, true_and]
  omega

theorem bnd_sizeT {a : ℕ} {env : List ℕ} (ha : a < env.length)
    (hB : (lvl a).denote w env ≤ B) : (sizeT (lvl a)).Bnd w B env := by
  rw [sizeT, bnd_foldT]
  refine ⟨trivial, Nat.zero_le _, hB, fun k hk => bnd_ite_of (by simp) ?_ trivial⟩
  rw [bnd_add]
  simp only [denote_lvl_index, denote_const, bnd_lvl, bnd_const, true_and]
  omega

theorem bnd_pow2_lvl_add {n : ℕ} {env : List ℕ} (x : ℕ) (hn : env.length = n)
    (h : 2 ^ (x + 1) ≤ B) :
    (pow2 (add (lvl n) (const 1))).Bnd w B (x :: env) := by
  have hx : x + 1 ≤ B := (Nat.lt_two_pow_self).le.trans h
  refine bnd_pow2 w B _ _ ?_ ?_
  · rw [bnd_add]; subst hn; simp only [bnd_lvl, bnd_const, denote_lvl_let, denote_const, true_and]
    exact ⟨by omega, hx⟩
  · subst hn; simpa using h

theorem bnd_hdT {a : ℕ} {env : List ℕ} (ha : a < env.length)
    (hB : (lvl a).denote w env ≤ B)
    (hP : 2 ^ (tOnesF ((lvl a).denote w env) + tOnesF ((lvl a).denote w env) + 1) ≤ B) :
    (hdT (lvl a)).Bnd w B env := by
  rw [hdT, bnd_letT]
  refine ⟨bnd_tOnesT ha hB, ?_⟩
  rw [denote_tOnesT ha]
  set t := tOnesF ((lvl a).denote w env)
  have h1 : 2 ^ (t + 1) ≤ B := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hP
  have h0 : 2 ^ t ≤ B := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hP
  simp only [bnd_mod, bnd_div, bnd_lvl, true_and]
  exact ⟨bnd_pow2_lvl_add t rfl h1, bnd_pow2 w B _ _ trivial (by simpa using h0)⟩

theorem bnd_tlT {a : ℕ} {env : List ℕ} (ha : a < env.length)
    (hB : (lvl a).denote w env ≤ B)
    (hP : 2 ^ (tOnesF ((lvl a).denote w env) + tOnesF ((lvl a).denote w env) + 1) ≤ B) :
    (tlT (lvl a)).Bnd w B env := by
  rw [tlT, bnd_letT]
  refine ⟨bnd_tOnesT ha hB, ?_⟩
  rw [denote_tOnesT ha]
  set t := tOnesF ((lvl a).denote w env)
  simp only [bnd_div, bnd_lvl, true_and]
  have hx : t + t + 1 ≤ B := (Nat.lt_two_pow_self).le.trans hP
  refine bnd_pow2 w B _ _ ?_ (by simpa using hP)
  simp only [bnd_add, bnd_lvl, bnd_const, denote_add, denote_lvl_let, denote_const, true_and]
  and_intros <;> omega

theorem consF_ge (x l : ℕ) (hl : 1 ≤ l) :
    x ≤ consF x l ∧ 2 ^ (sizeF x + sizeF x + 1) ≤ consF x l ∧
      2 ^ (sizeF x + 1) * x ≤ consF x l ∧ 2 ^ (sizeF x + sizeF x + 1) * l ≤ consF x l ∧
      (2 ^ sizeF x - 1) + 2 ^ (sizeF x + 1) * x ≤ consF x l := by
  unfold consF
  have h1 : x ≤ 2 ^ (sizeF x + 1) * x := Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : 2 ^ (sizeF x + sizeF x + 1) ≤ 2 ^ (sizeF x + sizeF x + 1) * l :=
    Nat.le_mul_of_pos_right _ hl
  omega

theorem bnd_consT {a b : ℕ} {env : List ℕ} (ha : a < env.length) (hb : b < env.length)
    (hl : 1 ≤ (lvl b).denote w env)
    (hB : consF ((lvl a).denote w env) ((lvl b).denote w env) ≤ B) :
    (consT (lvl a) (lvl b)).Bnd w B env := by
  set x := (lvl a).denote w env
  set l := (lvl b).denote w env
  obtain ⟨hx, hp, hm1, hm2, hs⟩ := consF_ge x l hl
  have hsz : sizeF x = x.size := sizeF_eq x
  rw [consT, bnd_letT]
  refine ⟨bnd_sizeT ha (hx.trans hB), ?_⟩
  rw [denote_sizeT ha, ← hsz]
  set n := sizeF x
  have hP2 : 2 ^ (n + n + 1) ≤ B := hp.trans hB
  have hP1 : 2 ^ (n + 1) ≤ B := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hP2
  have hP0 : 2 ^ n ≤ B := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hP2
  have hnB : n + n + 1 ≤ B := (Nat.lt_two_pow_self).le.trans hP2
  simp only [bnd_add, bnd_mul, bnd_sub, bnd_const, bnd_lvl, denote_add, denote_mul,
    denote_sub, denote_pow2, denote_lvl_let, denote_const, lvl_cons ha, lvl_cons hb, true_and]
  have hp2 : (pow2 (add (add (lvl env.length) (lvl env.length)) (const 1))).Bnd w B
      (n :: env) := by
    refine bnd_pow2 w B _ _ ?_ (by simpa using hP2)
    simp only [bnd_add, bnd_lvl, bnd_const, denote_add, denote_lvl_let, denote_const, true_and]
    and_intros <;> omega
  have hp0 : (pow2 (lvl env.length)).Bnd w B (n :: env) :=
    bnd_pow2 w B _ _ trivial (by simpa using hP0)
  have hp1 := bnd_pow2_lvl_add (w := w) (env := env) n rfl hP1
  exact ⟨⟨⟨hp0, Nat.one_le_two_pow.trans hP0⟩, ⟨hp1, hm1.trans hB⟩, hs.trans hB⟩,
    ⟨hp2, hm2.trans hB⟩, hB⟩

end Cslib.Complexity.NtimeDspace.SumProduct
