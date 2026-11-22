/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalPacked
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.WeightTerm

/-!
# The one-interval simulation as a term: one step

A numeric configuration is packed in one number `cpack R n` with the radix `R`
and `width k = 3 + 4k` digits: the state, the input position, the track, and
for every work tape its head cell, left and right numbers, and head index.

`stepT` computes the packed configuration after one coin step from the packed
configuration before it: `stepT_denote` shows it is `cpack R (nStep …)` when
the digits fit the radix. The machine is consulted through `tabT`, a finite
table written out as a chain of comparisons.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM

variable {w : List Bool}

/-! ### Finite tables -/

/-- The table of `f` below `N`, as a chain of comparisons (`0` from `N` on). -/
def tabT (f : ℕ → ℕ) : ℕ → Term → Term
  | 0, _ => const 0
  | N + 1, x => ite (eqT x (const N)) (const (f N)) (tabT f N x)

theorem denote_tabT (f : ℕ → ℕ) (N : ℕ) (x : Term) (env : List ℕ) :
    (tabT f N x).denote w env = if x.denote w env < N then f (x.denote w env) else 0 := by
  induction N with
  | zero => simp [tabT]
  | succ N ih =>
    simp only [tabT, denote_ite, denote_eqT, denote_const, ih]
    by_cases h : x.denote w env = N
    · simp [h]
    · simp only [h, ite_false, Nat.lt_irrefl, ite_false]
      by_cases h' : x.denote w env < N
      · simp [h', show x.denote w env < N + 1 by omega]
      · simp [h', show ¬ x.denote w env < N + 1 by omega]

theorem StableAt.tabT {f : ℕ → ℕ} {N : ℕ} {x : Term} {env : List ℕ} (hx : StableAt w x env) :
    StableAt w (tabT f N x) env := fun extra => by rw [denote_tabT, denote_tabT, hx extra]

/-! ### Packing configurations -/

variable {k s : ℕ} {State : Type} (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)

/-- The digits of a packed configuration. -/
def comp (n : NCfg k) (i : ℕ) : ℕ :=
  if i = 0 then n.st else if i = 1 then n.ip else if i = 2 then n.tr else
  if h : (i - 3) / 4 < k then
    if (i - 3) % 4 = 0 then (n.tapes ⟨_, h⟩).1
    else if (i - 3) % 4 = 1 then (n.tapes ⟨_, h⟩).2.1
    else if (i - 3) % 4 = 2 then (n.tapes ⟨_, h⟩).2.2
    else n.rho ⟨_, h⟩
  else 0

/-- The number of digits. -/
def width (k : ℕ) : ℕ := 3 + 4 * k

/-- A configuration packed in radix `R`. -/
def cpack (R : ℕ) (n : NCfg k) : ℕ := packDigits R (comp n) (width k)

/-- Every digit fits the radix. -/
def Fits (R : ℕ) (n : NCfg k) : Prop := ∀ i < width k, comp n i < R

theorem comp_tape (n : NCfg k) (h : Fin k) (f : ℕ) (hf : f < 4) :
    comp n (3 + 4 * h + f) =
      if f = 0 then (n.tapes h).1 else if f = 1 then (n.tapes h).2.1
      else if f = 2 then (n.tapes h).2.2 else n.rho h := by
  have hd : (3 + 4 * (h : ℕ) + f - 3) / 4 = h := by omega
  have hm : (3 + 4 * (h : ℕ) + f - 3) % 4 = f := by omega
  unfold comp
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      dite_eq_left (by omega)]
  have hfin : (⟨(3 + 4 * (h : ℕ) + f - 3) / 4, by omega⟩ : Fin k) = h := Fin.ext hd
  simp only [hm, hfin]

theorem digit_cpack {R : ℕ} (hR : 0 < R) {n : NCfg k} (hf : Fits R n) {i : ℕ}
    (hi : i < width k) : cpack R n / R ^ i % R = comp n i := by
  unfold cpack
  rw [packDigits_div_pow_mod hR _ _ hf, ite_eq_left hi]

/-! ### Numeric functions of a packed configuration -/

/-- Digit `j` of `a` in radix `R`. -/
def digN (R a j : ℕ) : ℕ := a / R ^ j % R

/-- The input cell code at input position `ip`. -/
def inN (w : List Bool) (ip : ℕ) : ℕ :=
  if ip = 0 then 0 else (ProgLang.Prog.inputValue w (ip - 1) + 1) % 3

/-- The head cells as base-3 digits. -/
def headsN (k R a : ℕ) : ℕ := ∑ h ∈ Finset.range k, digN R a (3 + 4 * h) * 3 ^ h

/-- The key of a packed configuration and a coin. -/
def keyN (k s : ℕ) (w : List Bool) (R a bit : ℕ) : ℕ :=
  keyOf s (digN R a 0) (inN w (digN R a 1)) bit (headsN k R a)

/-- A table lookup: `f x` below `N`, and `0` from `N` on. -/
def tabF (f : ℕ → ℕ) (N x : ℕ) : ℕ := if x < N then f x else 0

theorem tabF_of_lt {f : ℕ → ℕ} {N x : ℕ} (h : x < N) : tabF f N x = f x := ite_eq_left h

/-- Digit `i` after one step, from the packed configuration `a`. -/
def compN (w : List Bool) (R N a bit i : ℕ) : ℕ :=
  let key := keyN k s w R a bit
  if i = 0 then tabF (fSt e machine) (keyCount k s) key
  else if i = 1 then ipC N (digN R a 1) (tabF (fIn e machine) (keyCount k s) key)
  else if i = 2 then
    tabF fEmit 9 (digN R a 2 % 3 + 3 * tabF (fOut e machine) (keyCount k s) key)
  else
    let h := (i - 3) / 4
    let x := key + keyCount k s * h
    let wc := tabF (fW e machine) (keyCount k s * k) x
    let mc := tabF (fM e machine) (keyCount k s * k) x
    let t : NTape := (digN R a (3 + 4 * h), digN R a (3 + 4 * h + 1), digN R a (3 + 4 * h + 2))
    if (i - 3) % 4 = 0 then (tapeC t wc mc).1
    else if (i - 3) % 4 = 1 then (tapeC t wc mc).2.1
    else if (i - 3) % 4 = 2 then (tapeC t wc mc).2.2
    else moveC (digN R a (3 + 4 * h + 3)) mc

theorem inN_eq (w : List Bool) (ip : ℕ) : inN w ip = cc (inputAt w ip) := by
  unfold inN inputAt
  by_cases h : ip = 0
  · simp [h]
  · simp only [h, ite_false, ProgLang.Prog.inputValue]
    rcases w[ip - 1]? with _ | _ | _ <;> rfl

variable {e machine}

/-- **The step on packed configurations.** -/
theorem compN_cpack {R : ℕ} (hR : 0 < R) {n : NCfg k} (hf : Fits R n) (hn : WF (s := s) n)
    (bit : Bool) {i : ℕ} (hi : i < width k) :
    compN e machine w R w.length (cpack R n) bit.toNat i = comp (nStepC e machine w n bit) i := by
  have dg : ∀ j, j < width k → digN R (cpack R n) j = comp n j := fun j hj =>
    digit_cpack hR hf hj
  have w3 : ∀ h : Fin k, 3 + 4 * (h : ℕ) + 3 < width k := fun h => by
    have := h.isLt; unfold width; omega
  have dhead : ∀ h : Fin k, digN R (cpack R n) (3 + 4 * h) = (n.tapes h).1 := fun h => by
    rw [dg _ (by have := w3 h; omega)]
    have := comp_tape n h 0 (by norm_num); simpa using this
  have dleft : ∀ h : Fin k, digN R (cpack R n) (3 + 4 * h + 1) = (n.tapes h).2.1 := fun h => by
    rw [dg _ (by have := w3 h; omega), comp_tape n h 1 (by norm_num)]; rfl
  have dright : ∀ h : Fin k, digN R (cpack R n) (3 + 4 * h + 2) = (n.tapes h).2.2 := fun h => by
    rw [dg _ (by have := w3 h; omega), comp_tape n h 2 (by norm_num)]; rfl
  have drho : ∀ h : Fin k, digN R (cpack R n) (3 + 4 * h + 3) = n.rho h := fun h => by
    rw [dg _ (w3 h), comp_tape n h 3 (by norm_num)]; rfl
  have d0 : digN R (cpack R n) 0 = n.st := by rw [dg 0 (by unfold width; omega)]; rfl
  have d1 : digN R (cpack R n) 1 = n.ip := by rw [dg 1 (by unfold width; omega)]; rfl
  have d2 : digN R (cpack R n) 2 = n.tr := by rw [dg 2 (by unfold width; omega)]; rfl
  have hheads : headsN k R (cpack R n) = headsOf n.tapes := by
    unfold headsN headsOf packDigits
    refine Finset.sum_congr rfl fun h hh => ?_
    have hk : h < k := Finset.mem_range.mp hh
    beta_reduce
    rw [dite_eq_left hk, show 3 + 4 * h = 3 + 4 * ((⟨h, hk⟩ : Fin k) : ℕ) from rfl, dhead]
  have hkey : keyN k s w R (cpack R n) bit.toNat = keyAt (s := s) w n bit := by
    unfold keyN keyAt
    rw [d0, d1, inN_eq, hheads]
  have hK := keyAt_lt (s := s) (input := w) hn bit
  have hOut : fOut e machine (keyAt (s := s) w n bit) < 3 := cc_lt _
  have hx : ∀ h : ℕ, h < k → keyAt (s := s) w n bit + keyCount k s * h < keyCount k s * k :=
    fun h hh => by nlinarith
  unfold compN nStepC
  have h9 : n.tr % 3 + 3 * fOut e machine (keyAt (s := s) w n bit) < 9 := by
    have := Nat.mod_lt n.tr (show 3 > 0 by norm_num); omega
  simp only [hkey, tabF_of_lt hK]
  by_cases h0 : i = 0
  · subst h0; simp [comp]
  by_cases h1 : i = 1
  · subst h1; simp [comp, d1]
  by_cases h2 : i = 2
  · subst h2; simp only [OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, d2,
      comp]; exact tabF_of_lt h9
  have hh : (i - 3) / 4 < k := by unfold width at hi; omega
  set h : Fin k := ⟨(i - 3) / 4, hh⟩
  have hi' : i = 3 + 4 * (h : ℕ) + (i - 3) % 4 := by simp only [h]; omega
  rw [hi', comp_tape _ h _ (Nat.mod_lt _ (by norm_num))]
  rw [← hi']
  simp only [h0, h1, h2, ite_false]
  have ht : ((digN R (cpack R n) (3 + 4 * ((i - 3) / 4)),
      digN R (cpack R n) (3 + 4 * ((i - 3) / 4) + 1),
      digN R (cpack R n) (3 + 4 * ((i - 3) / 4) + 2)) : NTape) = n.tapes h := by
    rw [show (i - 3) / 4 = (h : ℕ) from rfl, dhead, dleft, dright]
  rw [ht, show 3 + 4 * ((i - 3) / 4) + 3 = 3 + 4 * (h : ℕ) + 3 from rfl, drho,
    tabF_of_lt (hx _ hh), tabF_of_lt (hx _ hh)]

/-! ### The terms -/

variable (e machine)

/-- The head cells of a packed configuration as base-3 digits. -/
def headsT (k : ℕ) (R a : Term) : Term :=
  sumT (const k) fun h => mul (digitT R a (add (const 3) (mul (const 4) h))) (powT (const 3) h)

/-- The input cell code at the position in digit `1`. -/
def inT (R a : Term) : Term :=
  ite (eqT (digitT R a (const 1)) (const 0)) (const 0)
    (mod (add (input (sub (digitT R a (const 1)) (const 1))) (const 1)) (const 3))

def keyT (k s : ℕ) (R a bit : Term) : Term :=
  add (digitT R a (const 0)) (mul (const (s + 1))
    (add (inT R a) (mul (const 3) (add bit (mul (const 2) (headsT k R a))))))

def moveCT (r m : Term) : Term :=
  ite (eqT m (const 0)) (sub r (const 1)) (ite (eqT m (const 1)) r (add r (const 1)))

def minT (a b : Term) : Term := ite (lt b a) b a

/-- The tape digit `f` after a step with write code `wc` and move code `mc`. -/
def tapePartT (f hd L Rt rho wc mc : Term) : Term :=
  ite (eqT f (const 0))
    (ite (eqT mc (const 0)) (mod L (const 3))
      (ite (eqT mc (const 1)) (ite (eqT wc (const 0)) hd (sub wc (const 1))) (mod Rt (const 3))))
  (ite (eqT f (const 1))
    (ite (eqT mc (const 0)) (div L (const 3))
      (ite (eqT mc (const 1)) L
        (add (mul L (const 3)) (ite (eqT wc (const 0)) hd (sub wc (const 1))))))
  (ite (eqT f (const 2))
    (ite (eqT mc (const 0))
      (add (mul Rt (const 3)) (ite (eqT wc (const 0)) hd (sub wc (const 1))))
      (ite (eqT mc (const 1)) Rt (div Rt (const 3))))
    (moveCT rho mc)))

/-- Digit `i` after one step. -/
def compT (R N a bit i : Term) : Term :=
  ite (eqT i (const 0)) (tabT (fSt e machine) (keyCount k s) (keyT k s R a bit))
  (ite (eqT i (const 1))
    (minT (add N (const 1)) (moveCT (digitT R a (const 1))
      (tabT (fIn e machine) (keyCount k s) (keyT k s R a bit))))
  (ite (eqT i (const 2))
    (tabT fEmit 9 (add (mod (digitT R a (const 2)) (const 3))
      (mul (const 3) (tabT (fOut e machine) (keyCount k s) (keyT k s R a bit)))))
    (tapePartT (mod (sub i (const 3)) (const 4))
      (digitT R a (add (const 3) (mul (const 4) (div (sub i (const 3)) (const 4)))))
      (digitT R a (add (add (const 3) (mul (const 4) (div (sub i (const 3)) (const 4))))
        (const 1)))
      (digitT R a (add (add (const 3) (mul (const 4) (div (sub i (const 3)) (const 4))))
        (const 2)))
      (digitT R a (add (add (const 3) (mul (const 4) (div (sub i (const 3)) (const 4))))
        (const 3)))
      (tabT (fW e machine) (keyCount k s * k) (add (keyT k s R a bit)
        (mul (const (keyCount k s)) (div (sub i (const 3)) (const 4)))))
      (tabT (fM e machine) (keyCount k s * k) (add (keyT k s R a bit)
        (mul (const (keyCount k s)) (div (sub i (const 3)) (const 4))))))))

/-- **One packed step**: the sum of the new digits times the powers of `R`. -/
def stepT (R N a bit : Term) : Term :=
  sumT (const (width k)) fun i => mul (compT e machine R N a bit i) (powT R i)

variable {e machine}

theorem denote_headsT (R a : Term) (env : List ℕ) (hR : StableAt w R env)
    (ha : StableAt w a env) :
    (headsT k R a).denote w env = headsN k (R.denote w env) (a.denote w env) := by
  unfold headsT headsN
  rw [denote_sumT _ _ env (fun h => digN (R.denote w env) (a.denote w env) (3 + 4 * h) * 3 ^ h)]
  · rfl
  · intro acc h
    have hR' : StableAt w R (acc :: h :: env) := hR.extend [acc, h]
    rw [denote_mul, digitT_denote _ _ _ _ hR', powT_denote _ _ _ (stableAt_const _ _)]
    simp [hR.cons₂, ha.cons₂, digN]

theorem denote_keyT (R a bit : Term) (env : List ℕ) (hR : StableAt w R env)
    (ha : StableAt w a env) :
    (keyT k s R a bit).denote w env =
      keyN k s w (R.denote w env) (a.denote w env) (bit.denote w env) := by
  unfold keyT keyN keyOf inT inN
  simp only [denote_add, denote_mul, denote_const, denote_ite, denote_eqT, denote_mod,
    denote_input, denote_sub, digitT_denote _ _ _ _ hR, denote_headsT R a env hR ha, digN]
  simp only [pow_one]
  by_cases h : a.denote w env / R.denote w env % R.denote w env = 0 <;> simp [h]

theorem denote_tapePartT (f hd L Rt rho wc mc : Term) (env : List ℕ) :
    (tapePartT f hd L Rt rho wc mc).denote w env =
      let t : NTape := (hd.denote w env, L.denote w env, Rt.denote w env)
      if f.denote w env = 0 then (tapeC t (wc.denote w env) (mc.denote w env)).1
      else if f.denote w env = 1 then (tapeC t (wc.denote w env) (mc.denote w env)).2.1
      else if f.denote w env = 2 then (tapeC t (wc.denote w env) (mc.denote w env)).2.2
      else moveC (rho.denote w env) (mc.denote w env) := by
  unfold tapePartT moveCT
  simp only [denote_ite, denote_eqT, denote_const, denote_mod, denote_div, denote_add,
    denote_mul, denote_sub, tapeC, moveC]
  by_cases hf0 : f.denote w env = 0 <;> by_cases hf1 : f.denote w env = 1 <;>
    by_cases hf2 : f.denote w env = 2 <;>
    by_cases hm0 : mc.denote w env = 0 <;> by_cases hm1 : mc.denote w env = 1 <;>
    by_cases hw : wc.denote w env = 0 <;> simp_all

theorem denote_compT (R N a bit i : Term) (env : List ℕ) (hR : StableAt w R env)
    (ha : StableAt w a env) :
    (compT e machine R N a bit i).denote w env =
      compN e machine w (R.denote w env) (N.denote w env) (a.denote w env) (bit.denote w env)
        (i.denote w env) := by
  unfold compT compN tabF
  simp only [denote_ite, denote_eqT, denote_const, denote_tabT, denote_keyT R a bit env hR ha,
    digitT_denote _ _ _ _ hR, denote_tapePartT, denote_add, denote_mul, denote_mod, denote_div,
    denote_sub, minT, moveCT, denote_lt, digN, ipC, moveC]
  by_cases h0 : i.denote w env = 0
  · simp [h0]
  by_cases h1 : i.denote w env = 1
  · simp only [h1]; simp [min_def]; split_ifs <;> omega
  by_cases h2 : i.denote w env = 2
  · simp [h2]
  simp [h0, h1, h2]

end Cslib.Complexity.NtimeDspace.LocalSim

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM

variable {w : List Bool} {k s : ℕ} {State : Type} {e : State ≃ Fin s}
  {machine : MultiTapePTM k Bool State}

/-- **One packed step is the numeric step.** -/
theorem stepT_denote (R N a bit : Term) (env : List ℕ) (hR : StableAt w R env)
    (hN : StableAt w N env) (ha : StableAt w a env) (hbit : StableAt w bit env)
    {Rv : ℕ} (hRv : R.denote w env = Rv) (hRpos : 0 < Rv) (hNv : N.denote w env = w.length)
    {n : NCfg k} (hf : Fits Rv n) (hn : WF (s := s) n) (hav : a.denote w env = cpack Rv n)
    {b : Bool} (hbv : bit.denote w env = b.toNat) :
    (stepT e machine R N a bit).denote w env = cpack Rv (nStep e machine w n b) := by
  unfold stepT
  rw [denote_sumT _ _ env (fun i => compN e machine w Rv w.length (cpack Rv n) b.toNat i * Rv ^ i)]
  · rw [denote_const, nStep_eq_nStepC hn]
    conv_rhs => rw [cpack, packDigits]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [compN_cpack hRpos hf hn b (Finset.mem_range.mp hi)]
  · intro acc i
    have hR' : StableAt w R (acc :: i :: env) := hR.extend [acc, i]
    have ha' : StableAt w a (acc :: i :: env) := ha.extend [acc, i]
    rw [denote_mul, denote_compT _ _ _ _ _ _ hR' ha', powT_denote _ _ _ hR']
    simp only [hR.cons₂, hN.cons₂, ha.cons₂, hbit.cons₂, hRv, hNv, hav, hbv, denote_lvl_index]

end Cslib.Complexity.NtimeDspace.LocalSim
