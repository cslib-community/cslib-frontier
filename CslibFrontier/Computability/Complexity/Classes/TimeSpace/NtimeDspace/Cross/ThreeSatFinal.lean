/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactClocked
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.SqrtLogGrowth
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Family
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ThreeSat.Instance
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgLength

/-!
# Corollary 7.2: #3-SAT in space `O(m/√log m)`

Corollary 7.2 (paper `cor:3sat`): *given a 3-CNF formula with `m ≥ 2` clauses in which every
variable occurs, the number of its satisfying assignments can be computed in space
`O(m/√log m)` and time `2^{O(m/√log m)}`.* As in the paper (before Theorem 2.3), a machine computes
an integer when, given the binary index of a bit position, it outputs that bit.

The formula is turned into its degree-3 network, as in the paper's proof
(`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/ThreeSat/Net.lean`;
each occurrence of a variable gets its own copy, chained to the others by equalities), and these
networks have logspace access at size `s = 8m + K'` (`threeSatFamily`). The rest goes through
residues, while the paper computes the bits directly: a residue form of Theorem 2.3 computes
`Z(G) = #SAT(φ)` modulo every prime `p` with `H(s) < p ≤ s`, the primes of the window have product
above `2^{s/2+1}` (`prime_window`, the elementary prime product bound), and the Chinese remainder
step (`Exact.exists_bitsProg`) turns the residues into bits. Bit positions `j > 3m` are answered `0`
directly (the count is at most `2^n ≤ 2^{3m}`).

This file takes this residue form of Theorem 2.3 as the explicit hypothesis `Theorem41`, for
**every** family with logspace access (Definition 2.1, `LogspaceNetFamily`), with
`H(s) = (2(⌊log₂ s⌋ + 1))^c`, at most `(2 log s + 2)^c`. Everything else is proved here;
the module `Cross.ThreeSat.Unconditional` discharges the hypothesis with `Net.networkCounting`
and states Corollary 7.2 unconditionally (`cor_9_4_unconditional`).

## Main definitions

* `Theorem41`: a residue form of Theorem 2.3 for every network family with logspace access.
* `BitLanguage`: the instances `(φ, j)` (`Instance`, encoded by `instEnc`) such that bit `j` of
  `numModels φ` is `1`.

## Main results

* `cor_9_4_bits`: under `Theorem41`, one machine decides `BitLanguage` in simultaneous space
  `C (m/√log m + log₂ |input|)` and time `2^{C (m/√log m + log₂ |input|)}` (`SqrtLog m` is
  `⌊m / ⌊√⌊log₂ m⌋⌋⌋ + 1`).
* `cor_9_4`: the same for the bit positions `j ≤ 3m` (all positions of a count `≤ 2^{3m}`), in space
  `C · m/√log m` and time `2^{C · m/√log m}`: the paper's statement.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.ThreeSat

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.Cross.Exact Finset
  _root_.Turing.MultiTapeTM Cslib.Complexity.CountingSimulation NtimeDspace.SumProduct

/-! ### The statements -/

/-- **A residue form of Theorem 2.3** (paper `thm:counting`, which is stated for bits) for every
family of networks with logspace access: a closed program `R` on `[s, |w|, p]` and constants `c, C,
s₀` such that, for every description `w`
of a network `G` of the family at size `s ≥ s₀` and every prime `p` with `(2 (log₂ s + 1))^c < p ≤
s`, `R` computes `Z(G) mod p` with every value arising in its evaluation at most `2^(C·SqrtLog s)`
(space `O(s/√log s)` and time `2^{O(s/√log s)}`). -/
def Theorem41 : Prop :=
  ∀ F : LogspaceNetFamily, ∃ (R : Prog) (c C s₀ : ℕ), Prog'.closed 3 R = true ∧
    ∀ (w : List Bool) (s p : ℕ), F.Mem w s → s₀ ≤ s → p.Prime →
      (2 * (Nat.log 2 s + 1)) ^ c < p → p ≤ s →
      (R.eval w [s, w.length, p] : ℤ) = (F.net w s).value % p ∧
        R.Bounded w (2 ^ (C * SqrtLog s)) [s, w.length, p]

/-- The instances `(φ, j)` such that bit `j` of the number of satisfying assignments of `φ` is
`1`. -/
def BitLanguage : Set Instance := {a | (numModels a.φ).testBit a.j = true}

/-! ### Parameter programs -/

variable {w : List Bool} {M : ℕ} {env : List ℕ}

/-- `b ^ c`. -/
def powC (b : Term) (c : ℕ) : Term := foldT (const c) (const 1) fun acc _ => mul acc b

theorem foldl_pow (x c : ℕ) : (List.range c).foldl (fun acc _ => acc * x) 1 = x ^ c := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ]

theorem val_powC {b : Term} {x : ℕ} (c : ℕ) (hb : Val w b env x) : Val w (powC b c)
    env (x ^ c) := by
  have := val_foldT (f := fun acc _ => mul acc b) (val_const c env) (val_const 1 env)
    (fun acc _ => acc * x) fun pre u u' p q hu _ => val_mul hu (hb.ext pre)
  rwa [foldl_pow] at this

theorem bd_powC {b : Term} {x : ℕ} (c : ℕ) (hb : Val w b env x) (hbb : Bd w M b env) (hx : 1 ≤ x)
    (h : x ^ c ≤ M) (hc : c ≤ M) : Bd w M (powC b c) env := by
  refine bd_foldT (f := fun acc _ => mul acc b) (val_const c env) (val_const 1 env)
    (fun acc _ => acc * x) (fun pre u u' p q hu _ => val_mul hu (hb.ext pre))
    (bd_const hc _) (bd_const ((Nat.one_le_pow _ _ hx).trans h) _) hc
    fun pre u u' p q hq hp hu _ hbu _ => ?_
  rw [foldl_pow] at hp
  subst hp
  refine bd_mul hbu (hbb.ext pre) hu (hb.ext pre) ?_
  rw [← pow_succ]
  exact (Nat.pow_le_pow_right hx hq).trans h

/-- `H(s) = (2 (log₂ s + 1))^(c+1)`, on `[s]`. -/
def Hprog (c : ℕ) : Prog := closeAt 1 (powC (mul (const 2) (bitLenT (lvl 0))) (c + 1) 1)
/-- `X(s) = s`, on `[s]`. -/
def Xprog : Prog := closeAt 1 (lvl 0 1)
/-- `E(s) = ⌊s/2⌋`, on `[s]`. -/
def Eprog : Prog := closeAt 1 (div (lvl 0) (const 2) 1)

/-- The window bound `(2 (log₂ s + 1))^(c+1)`. -/
abbrev hW (c s : ℕ) : ℕ := (2 * (Nat.log 2 s + 1)) ^ (c + 1)

theorem Hprog_spec (c : ℕ) {s : ℕ} (hs : 1 ≤ s) (hM : s + 1 ≤ M) (hH : hW c s ≤ M)
    (hc : c + 1 ≤ M) :
    (Hprog c).eval w [s] = hW c s ∧ (Hprog c).Bounded w M [s] := by
  have hb := val_mul (val_const 2 [s]) (val_bitLenT (val_s1 (w := w) (s := s)) hs)
  refine run_closeAt rfl (val_powC (c + 1) hb) (bd_powC (c + 1) hb ?_ (by omega) hH hc)
  have hl : Nat.log 2 s + 1 ≤ s := by
    have := Nat.log_lt_self 2 (show s ≠ 0 by omega); omega
  have h2 : 2 * (Nat.log 2 s + 1) ≤ hW c s := by
    have := Nat.le_self_pow (show c + 1 ≠ 0 by omega) (2 * (Nat.log 2 s + 1)); simpa using this
  exact bd_mul (bd_const (by omega) _) (bd_bitLenT val_s1 (bd_lvl _ _) hM) (val_const 2 _)
    (val_bitLenT val_s1 hs) (by omega)

theorem Xprog_spec {s : ℕ} (_hM : s ≤ M) : Xprog.eval w [s] = s ∧ Xprog.Bounded w M [s] :=
  run_closeAt rfl val_s1 (bd_lvl _ _)

theorem Eprog_spec {s : ℕ} (hM : 2 ≤ M) : Eprog.eval w [s] = s / 2 ∧ Eprog.Bounded w M [s] :=
  run_closeAt rfl (val_div val_s1 (val_const 2 _)) (bd_div (bd_lvl _ _) (bd_const hM _))

/-! ### The decider -/

section Decider

variable (Pb : Prog) (K' : ℕ)

/-- The number of clauses, read with the cap `|w|`. -/
def mmT : Term := mT (lvl 0)
/-- The number of digits of the bit position. -/
def ljT : Term := div (sub (offT (lvl 0)) (const 1)) (const 2)
/-- `⌊log₂ (3m + 1)⌋ + 1`. -/
def lbT : Term := bitLenT (add (mul (const 3) mmT) (const 1))
/-- The bit position. -/
def jT : Term := TermBlocks.ofBitsT ljT fun k => input (add (mul (const 2) k) (const 1))
/-- The size `s = 8m + K'`. -/
def szT : Term := add (mul (const 8) mmT) (const K')

/-- **The decider**, on `[|w|]`: `0` if the bit position has more digits than `3m + 1`, and
otherwise bit `j` of the count, by the program `Pb` of the Chinese remainder step at size `s = 8m +
K'`. -/
def deciderT : Term := ite (lt lbT ljT) (const 0) (call3 Pb (szT K') (lvl 0) jT)

/-- The decider as a program closed in `[|w|]`. -/
def decider : Prog := closeAt 1 (deciderT Pb K' 1)

end Decider

/-! ### The decider on an instance -/

section Instance

variable (a : Instance)

/-- The space budget `SqrtLog m + log₂ |input| + 1`. -/
def bud (a : Instance) : ℕ := SqrtLog a.φ.length + (instEnc a).length.log2 + 1

theorem instEnc_apply : instEnc a = frame (encNat a.j) ++ encSlots a.φ := rfl

theorem len_le_bnd : (instEnc a).length ≤ bnd (instEnc a).length := by
  unfold bnd; nlinarith

theorem m_le_len : a.φ.length ≤ (instEnc a).length := by
  rw [instEnc_apply, List.length_append]
  have := length_le_length_enc a.φ; omega

theorem mW_inst : mW (instEnc a) (instEnc a).length = a.φ.length :=
  mW_eq (len_le_bnd a) (m_le_len a)

theorem offW_inst : offW (instEnc a) (instEnc a).length = 2 * (encNat a.j).length + 1 :=
  offW_eq (len_le_bnd a)

theorem n_le (a : Instance) : a.n ≤ 3 * a.φ.length := n_le_three_mul a.φ a.three a.occurs

theorem count_lt (a : Instance) : numModels a.φ < 2 ^ (3 * a.φ.length + 1) :=
  (numModels_le a.φ).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by have := n_le a; omega))

/-- The input is short when the bit position has few digits. -/
theorem len_small {a : Instance} (h : (encNat a.j).length ≤ Nat.log 2 (3 * a.φ.length + 1) + 1) :
    (instEnc a).length ≤ 18 * a.φ.length ^ 2 + 18 * a.φ.length + 8 := by
  rw [instEnc_apply, List.length_append, length_frame, length_enc]
  have hn := n_le a
  have hl : Nat.log 2 (3 * a.φ.length + 1) ≤ 3 * a.φ.length + 1 := Nat.log_le_self _ _
  have hw : width a.n ≤ 6 * a.φ.length + 1 := by
    have := Nat.log2_le_self (2 * a.n); unfold width; omega
  have : a.φ.length * (3 * width a.n) ≤ a.φ.length * (3 * (6 * a.φ.length + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

end Instance


/-! ### Corollary 7.2 -/

theorem aux_sq (m K : ℕ) (hm : 1 ≤ m) : 18 * m ^ 2 + 18 * m + 8 ≤ (8 * m + K + 2) ^ 2 := by
  have h1 : 64 * m ^ 2 ≤ (8 * m + K + 2) ^ 2 := by
    have := Nat.pow_le_pow_left (show 8 * m ≤ 8 * m + K + 2 by omega) 2
    rw [mul_pow] at this; norm_num at this; exact this
  have h2 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  omega

theorem aux_C₂ {C K' C₂ b : ℕ} (h : C₂ = (C + 8) * (2 * (8 + K' + 1)) + K' + 64) (hb : 1 ≤ b) :
    4 * b + 10 ≤ C₂ * b ∧ 8 + K' + 1 ≤ C₂ ∧ 1 ≤ C₂ ∧ (C + 8) * (2 * (8 + K' + 1)) ≤ C₂ := by
  subst h
  generalize (C + 8) * (2 * (8 + K' + 1)) = Q
  refine ⟨?_, by omega, by omega, by omega⟩
  have : 64 * b ≤ (Q + K' + 64) * b := Nat.mul_le_mul_right _ (by omega)
  omega

theorem pow_four_le {n L : ℕ} (hn : n < 2 ^ L) : 64 * (n + 2) ^ 4 ≤ 2 ^ (4 * L + 10) := by
  have h2 : 2 ≤ 2 ^ (L + 1) := by
    have := Nat.one_le_two_pow (n := L); rw [pow_succ]; omega
  have hn2 : n + 2 ≤ 2 ^ (L + 1) := by rw [pow_succ]; omega
  calc 64 * (n + 2) ^ 4 ≤ 2 ^ 6 * (2 ^ (L + 1)) ^ 4 :=
        Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hn2 4)
    _ = 2 ^ (4 * L + 10) := by rw [← pow_mul, ← pow_add]; ring_nf

/-- **Corollary 7.2, for every bit position**, conditionally on the residue form of Theorem 2.3
for every family (`Theorem41`): one machine, fixed before the instance, decides from the encoding
of `(φ, j)` whether bit `j` of the number of satisfying assignments of `φ` is `1`, in simultaneous
space `C · (SqrtLog m + log₂ |input| + 1)` and time `2^{C · (SqrtLog m + log₂ |input| + 1)}`, where
`m` is
the number of clauses of `φ`. -/
theorem cor_9_4_bits (h41 : Theorem41) :
    ∃ C, DecidableInTimeAndSpace BitLanguage instEnc (fun a => 2 ^ (C * bud a))
      (fun a => C * bud a) := by
  obtain ⟨R, c, C, s₀, hRc, hR⟩ := h41 threeSatFamily
  obtain ⟨Pb, hPbc, hPb⟩ := exists_bitsProg R (Hprog c) Xprog Eprog sqrtLogProg hRc
    (closed_closeAt _ _) (closed_closeAt _ _) (closed_closeAt _ _) closed_sqrtLogProg
  obtain ⟨τ₁, hτ₁⟩ := sizes_eventually 1
  obtain ⟨s₁, hs₁⟩ := prime_window (c + 1)
  obtain ⟨K', hK'⟩ : ∃ K', K' = s₀ + τ₁ + s₁ + c + 64 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = (C + 8) * (2 * (8 + K' + 1)) + K' + 64 := ⟨_, rfl⟩
  have key : ∀ a : Instance, (decider Pb K').Bounded (instEnc a) (2 ^ (C₂ * bud a))
      [(instEnc a).length] ∧
      (1 ≤ (decider Pb K').eval (instEnc a) [(instEnc a).length] ↔ a ∈ BitLanguage) := by
    intro a
    -- notation and sizes
    obtain ⟨w, hw⟩ : ∃ w, w = instEnc a := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, n = w.length := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, m = a.φ.length := ⟨_, rfl⟩
    obtain ⟨lj, hlj⟩ : ∃ lj, lj = (encNat a.j).length := ⟨_, rfl⟩
    obtain ⟨Lb, hLb⟩ : ∃ Lb, Lb = Nat.log 2 (3 * m + 1) + 1 := ⟨_, rfl⟩
    obtain ⟨Mf, hMf⟩ : ∃ Mf, Mf = 2 ^ (C₂ * bud a) := ⟨_, rfl⟩
    rw [← hw, ← hn, ← hMf]
    have hm2 : 2 ≤ m := hm ▸ a.two_le
    have hmn : m ≤ n := by rw [hm, hn, hw]; exact m_le_len a
    have hbud : n.log2 + 1 ≤ bud a := by rw [hn, hw]; unfold bud; omega
    have hbud1 : 1 ≤ bud a := by omega
    have hsq1 : SqrtLog m ≤ bud a := by rw [hm]; unfold bud; omega
    have hnL : n < 2 ^ bud a := Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) hbud)
    obtain ⟨hC₂b, hCK, hC1, hCQ⟩ := aux_C₂ hC₂ hbud1
    have hN1 : 64 * (n + 2) ^ 4 ≤ Mf := (pow_four_le hnL).trans (by
      rw [hMf]; exact Nat.pow_le_pow_right (by norm_num) hC₂b)
    have hSz : Sz n Mf := ⟨hN1⟩
    have hnM : 64 * (n + 2) ≤ Mf := by
      have : (n + 2) ≤ (n + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
      omega
    -- values
    have hvs : Val w (lvl 0) [n] n := val_s1
    have hraw : (rawW w n).m = m := by rw [hm, hn, hw]; exact mW_inst a
    have hvm : Val w mmT [n] m := by have := val_mT (sT := lvl 0) (s := n) hvs; rwa [hraw] at this
    have hoff : offW w n = 2 * lj + 1 := by rw [hlj, hn, hw]; exact offW_inst a
    have hvlj : Val w ljT [n] lj := by
      have := val_div (val_sub (val_offT (sT := lvl 0) hvs) (val_const 1 [n])) (val_const 2 [n])
      rw [hoff] at this
      refine fun extra => (this extra).trans ?_
      omega
    have hv3 : Val w (add (mul (const 3) mmT) (const 1)) [n] (3 * m + 1) :=
      val_add (val_mul (val_const 3 _) hvm) (val_const 1 _)
    have hvlb : Val w lbT [n] Lb := by rw [hLb]; exact val_bitLenT hv3 (by omega)
    have hbm : Bd w Mf mmT [n] := bd_mT hvs (bd_lvl _ _) hSz
    have hboff : Bd w Mf (offT (lvl 0)) [n] := bd_offT hvs (bd_lvl _ _) hSz
    have hblj : Bd w Mf ljT [n] := bd_div (bd_sub hboff (bd_const (by omega) _))
        (bd_const (by omega) _)
    have hblb : Bd w Mf lbT [n] := bd_bitLenT hv3 (bd_add (bd_mul (bd_const (by omega) _) hbm
      (val_const 3 _) hvm (by omega)) (bd_const (by omega) _) (val_mul (val_const 3 _) hvm)
      (val_const 1 _) (by omega)) (by omega)
    -- the bit position
    have hfv : FVal w (fun k => input (add (mul (const 2) k) (const 1))) [n]
        (fun k => ib w (2 * k + 1)) := fun pre u q hu =>
      val_input (val_add (val_mul (val_const 2 _) hu) (val_const 1 _))
    have hvj : Val w jT [n] a.j := by
      have := val_ofBitsT hvlj hfv
      have e : TermBlocks.bitsNum lj (fun k => ib w (2 * k + 1)) = a.j := by
        rw [hlj, hw, instEnc_apply, bitsNum_frame_encNat]
      rw [e] at this; exact this
    -- the size
    obtain ⟨s, hs⟩ : ∃ s, s = 8 * m + K' := ⟨_, rfl⟩
    have hvsz : Val w (szT K') [n] s := by
      rw [hs]; exact val_add (val_mul (val_const 8 _) hvm) (val_const K' _)
    have hN3 : s ≤ Mf := by
      have h := mul_add_le_two_pow 8 K' (hmn.trans_lt hnL) hbud1
      rw [hs, hMf]
      exact h.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hCK))
    have hbsz : Bd w Mf (szT K') [n] :=
      bd_add (bd_mul (bd_const (by omega) _) hbm (val_const 8 _) hvm (by omega))
        (bd_const (by omega) _) (val_mul (val_const 8 _) hvm) (val_const K' _) (by omega)
    have hvd := val_ite (val_lt hvlb hvlj) (val_const 0 [n]) (val_call3 hPbc hvsz hvs hvj)
    by_cases hbig : Lb < lj
    · -- many digits: the bit is `0`
      have hv0 : Val w (deciderT Pb K') [n] 0 := by
        refine fun extra => (hvd extra).trans ?_
        simp [hbig]
      have hb0 : Bd w Mf (deciderT Pb K') [n] :=
        bd_ite (bd_lt hblb hblj) (val_lt hvlb hvlj) (fun _ => bd_const (Nat.zero_le _) _)
          (fun h => absurd (by simpa using hbig) h)
      obtain ⟨he, hb⟩ := run_closeAt rfl hv0 hb0
      have he' : (decider Pb K').eval w [n] = 0 := he
      have hb' : (decider Pb K').Bounded w Mf [n] := hb
      refine ⟨hb', ?_⟩
      rw [he']
      simp only [BitLanguage, Set.mem_ofPred_eq, Nat.one_le_iff_ne_zero, ne_eq, not_true_eq_false,
        false_iff, Bool.not_eq_true]
      apply Nat.testBit_eq_false_of_lt
      have hsz : (encNat a.j).length = Nat.size a.j := by rw [encNat_apply, Nat.size_eq_bits_len]
      have hge : 2 ^ (lj - 1) ≤ a.j := by
        by_contra h
        have := Nat.size_le.mpr (not_le.mp h)
        omega
      have h3 : 3 * m + 1 < 2 ^ Lb := by rw [hLb]; exact Nat.lt_pow_succ_log_self (by norm_num) _
      have hpow : 2 ^ Lb ≤ 2 ^ (lj - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (count_lt a).trans_le (Nat.pow_le_pow_right (by norm_num) (by rw [← hm]; omega))
    · -- few digits: the Chinese remainder step at size `s`
      have hsmall : lj ≤ Lb := by omega
      have hlen : w.length ≤ bnd s := by
        have := len_small (a := a) (by rw [← hlj, ← hm, ← hLb]; exact hsmall)
        rw [← hw, ← hm] at this
        rw [bnd, hs]; exact this.trans (aux_sq m K' (by omega))
      -- the parameters at `s`
      have hs1 : s₁ ≤ s := by omega
      have hsτ : τ₁ ≤ s := by omega
      obtain ⟨hS2, hSX, hSE, hSM⟩ := hτ₁ s hsτ s (by simp)
      have hprod := hs₁ s hs1
      obtain ⟨S, hS⟩ : ∃ S, S = SqrtLog s := ⟨_, rfl⟩
      rw [← hS] at hS2 hSX hSE hSM
      obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = 2 ^ ((C + 8) * S) := ⟨_, rfl⟩
      have h8M : 2 ^ (8 * S) ≤ Ms := by
        rw [hMs]; exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
      have hsS : s < 2 ^ S := by rw [hS]; exact lt_two_pow_sqrtLog s
      have hS8 : 2 ^ S ≤ 2 ^ (8 * S) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hHs : hW c s < s := by
        by_contra hge
        have : (Ioc (hW c s) s).filter Nat.Prime = ∅ := by
          ext p; simp only [mem_filter, mem_Ioc, Finset.notMem_empty, iff_false, not_and]
          intro h1 h2; omega
        rw [this, prod_empty] at hprod
        have := Nat.one_le_two_pow (n := s / 2 + 1)
        omega
      have hH2 : 2 ≤ hW c s := by
        have : 2 ≤ 2 * (Nat.log 2 s + 1) := by omega
        exact this.trans
            (by simpa using Nat.le_self_pow (show c + 1 ≠ 0 by omega) (2 * (Nat.log 2 s + 1)))
      obtain ⟨hHe, hHb⟩ := Hprog_spec (w := w) (M := Ms) c (s := s) (by omega) (by omega) (by omega)
        (by omega)
      obtain ⟨hXe, hXb⟩ := Xprog_spec (w := w) (M := Ms) (s := s) (by omega)
      obtain ⟨hEe, hEb⟩ := Eprog_spec (w := w) (M := Ms) (s := s) (by omega)
      have hWe : sqrtLogProg.eval w [s] = S := by rw [hS]; exact eval_sqrtLogProg (by omega)
      have hWb : sqrtLogProg.Bounded w Ms [s] := by
        refine bounded_sqrtLogProg (by omega) ?_
        have : s + 2 ≤ 2 ^ (S + 1) := by rw [pow_succ]; omega
        calc (s + 2) * (s + 2) ≤ 2 ^ (S + 1) * 2 ^ (S + 1) := Nat.mul_le_mul this this
          _ = 2 ^ (2 * S + 2) := by rw [← pow_add]; ring_nf
          _ ≤ Ms := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h8M
      -- the residues, by the residue form of Theorem 2.3 for the 3-SAT family
      have hres : ∀ p, p.Prime → hW c s < p → p ≤ s →
          R.eval w [s, n, p] = numModels a.φ % p ∧ R.Bounded w Ms [s, n, p] := by
        intro p hp hHp hps
        have hcp : (2 * (Nat.log 2 s + 1)) ^ c < p :=
          lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega)) hHp
        have hmem : threeSatFamily.Mem w s := hlen
        obtain ⟨h1, h2⟩ := hR w s p hmem (by omega) hp hcp hps
        have hlen' : (frame (encNat a.j) ++ encSlots a.φ).length ≤ bnd s := by
          rw [← instEnc_apply, ← hw]; exact hlen
        have hval := threeSatFamily_value (encNat a.j) a.φ s a.three a.occurs hlen' (by omega)
        rw [← instEnc_apply, ← hw] at hval
        rw [hval, ← hn] at h1
        refine ⟨by exact_mod_cast h1, ?_⟩
        rw [← hn] at h2
        have hle : 2 ^ (C * SqrtLog s) ≤ Ms := by
          rw [hMs, ← hS]
          exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
        exact bounded_mono hle _ _ h2
      have hZ : numModels a.φ ≤ 2 ^ (s / 2) :=
        (numModels_le a.φ).trans (Nat.pow_le_pow_right (by norm_num) (by have := n_le a; omega))
      have hgrp : numGroups s (s / 2) S ≤ numGroups s (paddedTime s) S := by
        unfold numGroups
        have := le_paddedTime s
        exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) _
      have hsize : 4 * ((s + 1) * 2 ^ S * (S ^ numGroups s (s / 2) S + 1)) ≤ Ms := by
        refine le_trans ?_ (hSM.trans h8M)
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right
          (Nat.pow_le_pow_right (by omega) hgrp) _))
      have hspec := hPb w s n (numModels a.φ) Ms
      simp only [hHe, hXe, hEe, hWe] at hspec
      obtain ⟨hPbe, hPbb⟩ := hspec hH2 hprod hZ hres hHb hXb hEb hWb hS2 hSX
        (by have := le_paddedTime s; omega) hsize a.j
      -- the decider
      have hv1 : Val w (deciderT Pb K') [n] (numModels a.φ / 2 ^ a.j % 2) := by
        refine fun extra => (hvd extra).trans ?_
        simp [hbig, hPbe]
      have hMsf : Ms ≤ Mf := by
        rw [hMs, hMf]
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have hsl := sqrtLog_le_of_le_mul_add 8 K' (m := m) (by norm_num)
            (show s ≤ 8 * m + K' by omega)
        rw [← hS] at hsl
        calc (C + 8) * S ≤ (C + 8) * (2 * (8 + K' + 1) * SqrtLog m) := Nat.mul_le_mul_left _ hsl
          _ ≤ (C + 8) * (2 * (8 + K' + 1)) * bud
              a := by rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hsq1
          _ ≤ C₂ * bud a := Nat.mul_le_mul_right _ hCQ
      have h2lj : 2 ^ lj ≤ 6 * m + 2 := by
        calc 2 ^ lj ≤ 2 ^ Lb := Nat.pow_le_pow_right (by norm_num) hsmall
          _ ≤ 2 * (3 * m + 1) := by
            rw [hLb, pow_succ, mul_comm]
            exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
          _ = 6 * m + 2 := by ring
      have hljle : lj ≤ 2 ^ lj := Nat.lt_two_pow_self.le
      have hbj : Bd w Mf jT [n] := bd_ofBitsT hvlj hblj hfv (fun pre u q hq hu hbu =>
        bd_input (bd_add (bd_mul (bd_const (by omega) _) hbu (val_const 2 _) hu (by omega))
          (bd_const (by omega) _) (val_mul (val_const 2 _) hu) (val_const 1 _) (by omega)))
        (by omega) (by omega)
      have hb1 : Bd w Mf (deciderT Pb K') [n] :=
        bd_ite (bd_lt hblb hblj) (val_lt hvlb hvlj) (fun h => absurd (by simpa using h) hbig)
          (fun _ => bd_call3 hPbc hvsz hvs hvj hbsz (bd_lvl _ _) hbj
            (bounded_mono hMsf _ _ hPbb))
      obtain ⟨he, hb⟩ := run_closeAt rfl hv1 hb1
      have he' : (decider Pb K').eval w [n] = numModels a.φ / 2 ^ a.j % 2 := he
      have hb' : (decider Pb K').Bounded w Mf [n] := hb
      refine ⟨hb', ?_⟩
      rw [he', ← Nat.toNat_testBit]
      simp only [BitLanguage, Set.mem_ofPred_eq]
      cases (numModels a.φ).testBit a.j <;> simp
  exact decidable_of_prog_len BitLanguage (decider Pb K') bud (fun a => C₂ * bud a) C₂
    (fun a => by unfold bud; omega) (fun a => by
      have : 1 ≤ bud a := by unfold bud; omega
      have : 1 ≤ C₂ := by omega
      nlinarith) (fun a => le_rfl)
    (fun a => by
      have h1 : (instEnc a).length < 2 ^ ((instEnc a).length.log2 + 1) := Nat.lt_log2_self
      refine h1.le.trans (Nat.pow_le_pow_right (by norm_num) ?_)
      have : (instEnc a).length.log2 + 1 ≤ bud a := by unfold bud; omega
      have : 1 ≤ C₂ := by omega
      nlinarith)
    (fun a => (key a).1) (fun a => (key a).2)


/-! ### The paper's form: all bit positions of the count -/

/-- Instances whose bit position is at most `3m`. The count is at most `2^n ≤ 2^{3m}`, so these
positions carry all of its bits. -/
def SmallInstance : Type := {a : Instance // a.j ≤ 3 * a.φ.length}

/-- The encoding of the instances with `j ≤ 3m`. -/
def smallEnc : SmallInstance ↪ List Bool := (Function.Embedding.subtype _).trans instEnc

/-- `BitLanguage` on the instances with `j ≤ 3m`. -/
def SmallBitLanguage : Set SmallInstance := {a | a.1 ∈ BitLanguage}

/-- For a bit position `j ≤ 3m` the budget is `O(SqrtLog m)`. -/
theorem bud_le (a : Instance) (h : a.j ≤ 3 * a.φ.length) : bud a ≤ 11 * SqrtLog a.φ.length := by
  have hm2 := a.two_le
  have hsz : (encNat a.j).length ≤ Nat.log 2 (3 * a.φ.length + 1) + 1 := by
    rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
    exact (show a.j < 3 * a.φ.length + 1 by omega).trans (Nat.lt_pow_succ_log_self (by norm_num) _)
  have hlen := len_small hsz
  have hlog := log2_add_one_le_sqrtLog a.φ.length
  have hmL : a.φ.length < 2 ^ (a.φ.length.log2 + 1) := Nat.lt_log2_self
  have hl64 : (instEnc a).length < 2 ^ (2 * a.φ.length.log2 + 8) := by
    have hsq : a.φ.length ^ 2 < (2 ^ (a.φ.length.log2 + 1)) ^ 2 := Nat.pow_lt_pow_left
        hmL (by norm_num)
    have e : 2 ^ (2 * a.φ.length.log2 + 8) = 64 * (2 ^ (a.φ.length.log2 + 1)) ^ 2 := by
      rw [← pow_mul, show (64 : ℕ) = 2 ^ 6 by rfl, ← pow_add]; ring_nf
    rw [e]
    have : 18 * a.φ.length ^ 2 + 18 * a.φ.length + 8 < 64 * (2 ^ (a.φ.length.log2 + 1)) ^ 2 := by
      have h1 : a.φ.length ≤ a.φ.length ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    omega
  have hl : (instEnc a).length.log2 < 2 * a.φ.length.log2 + 8 :=
    (Nat.log2_lt (by have := m_le_len a; omega)).mpr hl64
  unfold bud
  have : 1 ≤ SqrtLog a.φ.length := Nat.le_add_left _ _
  omega

/-- **Corollary 7.2** (paper `cor:3sat`), conditionally on the residue form of Theorem 2.3 for
every family (`Theorem41`). There are a constant `C` and one machine, fixed before the instance,
that given the encoding of a 3-CNF formula `φ` with `m ≥ 2` clauses in which every variable occurs
and of a bit position `j ≤ 3m` (the count is at most `2^{3m}`, so these are all its bits) decides
whether bit
`j` of the number of satisfying assignments of `φ` is `1`, in space `C · SqrtLog m` and time
`2^{C · SqrtLog m}`, where `SqrtLog m = ⌊m / ⌊√⌊log₂ m⌋⌋⌋ + 1 = O(m/√log m)`. -/
theorem cor_9_4 (h41 : Theorem41) :
    ∃ C, DecidableInTimeAndSpace SmallBitLanguage smallEnc
      (fun a => 2 ^ (C * SqrtLog a.1.φ.length)) (fun a => C * SqrtLog a.1.φ.length) := by
  obtain ⟨C, k, State, hfin, tm, htm⟩ := cor_9_4_bits h41
  refine ⟨11 * C, k, State, hfin, tm, fun a => ?_⟩
  have hb := bud_le a.1 a.2
  have h := htm a.1
  have hind : indicator SmallBitLanguage a = indicator BitLanguage a.1 := rfl
  rw [hind]
  refine ⟨h.1, h.2.1.mono (Nat.pow_le_pow_right (by norm_num) ?_), h.2.2.mono ?_⟩
  · calc C * bud a.1 ≤ C * (11 * SqrtLog a.1.φ.length) := Nat.mul_le_mul_left _ hb
      _ = 11 * C * SqrtLog a.1.φ.length := by ring
  · calc C * bud a.1 ≤ C * (11 * SqrtLog a.1.φ.length) := Nat.mul_le_mul_left _ hb
      _ = 11 * C * SqrtLog a.1.φ.length := by ring

end Cslib.Complexity.NtimeDspace.Cross.ThreeSat
