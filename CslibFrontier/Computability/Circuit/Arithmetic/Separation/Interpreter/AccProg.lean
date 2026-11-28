/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ParseLoop
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Util
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.WordCode

/-!
# The program of an accelerator

`Interpreter.accF M m d out` evaluates the part of degree at most `d` of a polynomial `p` with a
small circuit, at the point coded by its argument. The constants are the trie `Interpreter.accK`.
Its value is the sum of the first `d + 1` coefficients of `p` along the line through that point
(`Interpreter.accF_kv`), where `p` is given by `Arithmetic.ComputedWithin`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Acc.Prog`.

## Main definitions

* `Interpreter.pairsF`, `Interpreter.treeF`, `Interpreter.accF`, `Interpreter.codeB`,
  `Interpreter.accK`.

## Main results

* `Interpreter.nds_accK`, `Interpreter.ht_accK`: the size of the trie of constants.
* `Interpreter.accF_kv`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- Pair the neighbours of a list. The argument is (this program, list). -/
@[expose] def pairB : Fm := .ite (.tl .id) (.cons (.cons (.hd (.tl .id)) (.hd (.tl (.tl .id))))
  (.run (.hd .id) (.cons (.hd .id) (.tl (.tl (.tl .id)))))) (.quote .nil)

private theorem pairB_gives (l : List Tree) :
    Gives θ pairB (.cons pairB.code (listT l)) (listT (pairL l)) (40 * (l.length + 1)) := by
  induction l using pairL.induct with
  | case1 => exact ((Gives.id _).tl.ite_false (Gives.quote .nil _)).mono (by norm_num)
  | case2 a =>
    have h0 : Gives θ (Fm.ofTree pairB.code) (.cons pairB.code (listT [])) (listT (pairL [])) 40 :=
        by
      rw [Fm.ofTree_code]
      exact ((Gives.id _).tl.ite_false (Gives.quote .nil _)).mono (by norm_num)
    have h := (Gives.id (θ := θ) (.cons pairB.code (listT [a]))).tl.ite_true (H := .quote .nil)
        (by simp [listT])
      (Gives.cons (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd)
        (Gives.run (Gives.id _).hd (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl.tl) h0))
    exact h.mono (by simp)
  | case3 a b l ih =>
    have h0 : Gives θ (Fm.ofTree pairB.code) (.cons pairB.code (listT l)) (listT (pairL l))
        (40 * (l.length + 1)) := by
      rw [Fm.ofTree_code]
      exact ih
    have h :=
        (Gives.id (θ := θ) (.cons pairB.code (listT (a :: b :: l)))).tl.ite_true (H := .quote .nil)
      (by simp [listT]) (Gives.cons (Gives.cons (Gives.id _).tl.hd (Gives.id _).tl.tl.hd)
        (Gives.run (Gives.id _).hd (Gives.cons (Gives.id _).hd (Gives.id _).tl.tl.tl) h0))
    refine h.mono ?_
    simp only [List.length_cons]
    omega

/-- Pair the neighbours several times. -/
@[expose] def pairsF : ℕ → Fm → Fm
  | 0, l => l
  | m + 1, l => pairsF m (app pairB.code (.cons (.quote pairB.code) l))

private theorem length_pairL_le (l : List Tree) : (pairL l).length ≤ l.length := by
  rw [length_pairL]
  omega

private theorem pairsF_gives (m : ℕ)
    {l : Fm} {x : Tree} {xs : List Tree} {c : ℕ} (hl : Gives θ l x (listT xs) c) :
    Gives θ (pairsF m l) x (listT (pairL^[m] xs)) (c + m * (40 * (xs.length + 1) + 10)) := by
  induction m generalizing l xs c with
  | zero => simpa [pairsF] using hl
  | succ m ih =>
    have h := Gives.app (p := pairB.code) (Gives.cons (Gives.quote pairB.code x) hl) (by
      rw [Fm.ofTree_code]
      exact pairB_gives xs)
    have h2 := ih h
    rw [Function.iterate_succ_apply]
    refine h2.mono ?_
    have h3 : m * (40 * ((pairL xs).length + 1) + 10) ≤ m * (40 * (xs.length + 1) + 10) := by
      apply Nat.mul_le_mul_left
      have := length_pairL_le xs
      omega
    have h4 : (m + 1) * (40 * (xs.length + 1) + 10) = m * (40 * (xs.length + 1) + 10) +
        (40 * (xs.length + 1) + 10) := by
      ring
    omega

/-- The letter of the empty tree. -/
@[expose] def lt0 : Tree := ofBits [true, false]

/-- The letter of a node. -/
@[expose] def lt1 : Tree := ofBits [true, true]

/-- The letter at the end. -/
@[expose] def lt2 : Tree := ofBits [false, true]

/-- The tree of pairs of the letters of the word of the argument. -/
@[expose] def treeF (m : ℕ) : Fm := .hd (pairsF m (app (wordB lt0 lt1).code
  (.cons (.quote (wordB lt0 lt1).code) (.cons .id (.quote (listT [lt2]))))))

/-- The program. -/
@[expose] def accF (M m d : ℕ) (out : List Bool) : Fm :=
    .ite .guess (.mul (.quote (ofBits [true, false])))
  (app (loopF M m).code (.cons (.quote (loopF M m).code) (.cons (.quote (num (d - 1)))
    (.cons (.quote (listT ([out].map ofBits))) (treeF m)))))

/-- The tree of pairs. -/
private def pairTree (m : ℕ) (z : Tree) : Tree :=
    (listT (pairL^[m] (wordT lt0 lt1 z ++ [lt2]))).hd

private theorem treeF_gives (m : ℕ) (z : Tree) :
    Gives θ (treeF m) z (pairTree m z) (60 * z.size + m * (40 * (z.size + 2) + 10) + 12) := by
  have h0 := Gives.app (p := (wordB lt0 lt1).code)
      (Gives.cons (Gives.quote (θ := θ) (wordB lt0 lt1).code z)
    (Gives.cons (Gives.id z) (Gives.quote (listT [lt2]) z))) (by
      rw [Fm.ofTree_code]
      exact wordB_gives lt0 lt1 z [lt2])
  have h := (pairsF_gives m h0).hd
  rw [List.length_append, length_wordT, List.length_singleton] at h
  have e : m * (40 * (z.size + 1 + 1) + 10) = m * (40 * (z.size + 2) + 10) := rfl
  refine h.mono ?_
  rw [e]
  omega

/-- The letter as a tree. -/
@[expose] def ltr : Option Bool → Tree
  | some false => lt0
  | some true => lt1
  | none => lt2

theorem wordT_eq (z : Tree) : wordT lt0 lt1 z ++ [lt2] = ((tbits z).map some ++ [none]).map ltr :=
  by rw [List.map_append, List.map_map, ← wordT_eq_map_tbits]; rfl

/-- The letter at a place of the tree of pairs. -/
private theorem look_pairTree {m : ℕ} {z : Tree} (hz : z.size < 2 ^ m)
    {p : List Bool} (hp : p.length = m) :
    look p (pairTree m z) =
        ((((tbits z).map some ++ [none])[KT.val p.reverse]?).map ltr).getD .nil := by
  rw [pairTree, look_pairs m _ (by rw [List.length_append, length_wordT]; exact hz) p hp, wordT_eq,
    List.getD_eq_getElem?_getD, List.getElem?_map]

/-- The letter with a given code. -/
private def decL (c : List Bool) : Option (Option Bool) :=
  if c = [true, false] then some (some false) else if c = [true, true] then some (some true)
  else if c = [false, true] then some none else none

private theorem decL_lc (o : Option (Option Bool)) : decL (lc ((o.map ltr).getD .nil)) = o := by
  rcases o with _ | _ | _ | _ <;> rfl

private theorem length_lc (o : Option (Option Bool)) : (lc ((o.map ltr).getD .nil)).length = 2 := by
  rcases o with _ | _ | _ | _ <;> rfl

private theorem ltr_cases (o : Option (Option Bool)) :
    (o.map ltr).getD .nil = .nil ∨ ∃ w : List Bool,
        w.length = 2 ∧ (o.map ltr).getD .nil = ofBits w := by
  rcases o with _ | _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr ⟨[false, true], rfl, rfl⟩
  · exact Or.inr ⟨[true, false], rfl, rfl⟩
  · exact Or.inr ⟨[true, true], rfl, rfl⟩

/-- The one-hot code of a word, with one letter `none` at the end, as `0`/`1` values: the tape's
`Tape.wordCode` read in `R`. -/
@[expose] def codeB (R : Type) [CommRing R] (N : ℕ) (w : List Bool) : Fin N × Option Bool → R :=
  fun q => if Tape.wordCode N w q then 1 else 0

/-- The weight of a letter at a place. -/
private def lamK {N : ℕ} (lam : Fin N × Option Bool → R) (i : ℕ) (o : Option (Option Bool)) : R :=
  match o with
  | none => 0
  | some γ => if h : i < N then lam (⟨i, h⟩, γ) else 0

private theorem lamK_ge {N : ℕ} (lam : Fin N × Option Bool → R) {i : ℕ} (h : ¬ i < N)
    (o : Option (Option Bool)) :
    lamK lam i o = 0 := by
  cases o with
  | none => rfl
  | some γ => exact dite_eq_right h

/-- The constants of an accelerator. -/
def accK (M m N : ℕ) (γ : R) (k : ℕ → ℕ → ℕ → R)
    (lam : ℕ → Fin N × Option Bool → R) : KT R :=
  .node (.node
      (KT.full (M + M + M) fun w => k (KT.val (w.take M)) (KT.val ((w.drop M).take M))
          (KT.val (w.drop (M + M))))
    (KT.full (M + m + 2) fun w => lamK (lam (KT.val (w.take M))) (KT.val ((w.drop M).take m))
        (decL (w.drop (M + m)))))
    (.leaf γ)

section names

variable {M m N : ℕ} {γ : R} {k : ℕ → ℕ → ℕ → R} {lam : ℕ → Fin N × Option Bool → R}

/-- The three parts of `a ++ b ++ c`, recovered from the lengths of `a` and `b`. -/
private theorem take_drop_three {α : Type*} {a b c : List α} {la lb : ℕ} (ha : a.length = la)
    (hb : b.length = lb) :
    (a ++ b ++ c).take la = a ∧ ((a ++ b ++ c).drop la).take lb = b ∧
      (a ++ b ++ c).drop (la + lb) = c :=
  ⟨by rw [List.append_assoc, List.take_left' ha],
    by rw [List.append_assoc, List.drop_left' ha, List.take_left' hb],
    List.drop_left' (by simp [ha, hb])⟩

private theorem accK_k {g l r : List Bool} (hg : g.length = M) (hl : l.length = M)
    (hr : r.length = M) :
    (accK M m N γ k lam).lk ([false, false] ++ g ++ l ++ r ++ [false]) = k (KT.val g) (KT.val l)
        (KT.val r) ∧
    (accK M m N γ k lam).InB 1 ([false, false] ++ g ++ l ++ r ++ [false]) := by
  have e : [false, false] ++ g ++ l ++ r ++ [false] =
      false :: false :: ((g ++ l ++ r) ++ [false]) := by simp
  have h : (g ++ l ++ r).length = M + M + M := by
    simp only [List.length_append, hg, hl, hr]
  rw [e]
  obtain ⟨e1, e2, e3⟩ := take_drop_three (c := r) hg hl
  refine ⟨(KT.lk_full (fun w => k (KT.val (w.take M)) (KT.val ((w.drop M).take M))
    (KT.val (w.drop (M + M)))) h).trans ?_, KT.inB_full _ h⟩
  simp only [e1, e2, e3]

private theorem accK_l {g p c : List Bool} (hg : g.length = M) (hp : p.length = m)
    (hc : c.length = 2) :
    (accK M m N γ k lam).lk ([false, true] ++ g ++ p ++ c ++ [false]) =
      lamK (lam (KT.val g)) (KT.val p) (decL c) ∧
    (accK M m N γ k lam).InB 1 ([false, true] ++ g ++ p ++ c ++ [false]) := by
  have e : [false, true] ++ g ++ p ++ c ++ [false] = false :: true :: ((g ++ p ++ c) ++ [false]) :=
      by simp
  have h : (g ++ p ++ c).length = M + m + 2 := by
    simp only [List.length_append, hg, hp, hc]
  rw [e]
  obtain ⟨e1, e2, e3⟩ := take_drop_three (c := c) hg hp
  refine ⟨(KT.lk_full (fun w => lamK (lam (KT.val (w.take M))) (KT.val ((w.drop M).take m))
    (decL (w.drop (M + m)))) h).trans ?_, KT.inB_full _ h⟩
  simp only [e1, e2, e3]

private theorem accK_c : (accK M m N γ k lam).lk [true, false] = γ ∧
    (accK M m N γ k lam).InB 1 [true, false] :=
  ⟨rfl, ⟨0, zero_lt_one, rfl⟩⟩

theorem nds_accK : (accK M m N γ k lam).nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 := by
  have h1 := KT.nds_full (M + M + M) fun w => k (KT.val (w.take M)) (KT.val ((w.drop M).take M))
      (KT.val (w.drop (M + M)))
  have h2 := KT.nds_full (M + m + 2) fun w =>
    lamK (lam (KT.val (w.take M))) (KT.val ((w.drop M).take m)) (decL (w.drop (M + m)))
  have e : M + M + M + 1 = 3 * M + 1 := by ring
  have e2 : M + m + 2 + 1 = M + m + 3 := by ring
  rw [e] at h1
  rw [e2] at h2
  rw [accK, KT.nds, KT.nds, KT.nds]
  omega

theorem ht_accK : (accK M m N γ k lam).ht ≤ 3 * M + m + 4 := by
  rw [accK, KT.ht, KT.ht, KT.ht, KT.ht_full, KT.ht_full]
  omega

end names

open Cslib.Circuits.Arithmetic.Separation.LowDegree MvPolynomial in
/-- **The program computes the part of degree at most `d` of a polynomial with a small circuit.** -/
theorem accF_kv {M m N d s : ℕ} {p : MvPolynomial (Fin N × Option Bool) R}
    (hp : ComputedWithin p s) (hs : s ≤ 2 ^ M)
    (hd : 0 < d) (hNm : N ≤ 2 ^ m) : ∃ (K : KT R) (out : List Bool), out.length = M ∧
      K.nds ≤ 2 ^ (3 * M + 1) + 2 ^ (M + m + 3) + 3 ∧ K.ht ≤ 3 * M + m + 4 ∧
      ∀ (A : Type) [CommRing A] [Algebra A R] (θ : List Bool → A) (z : Tree), z.size < N →
        KV θ K.lk {q | K.InB 1 q} (accF M m d out) z
          (∑ i ∈ Finset.range (d + 1), (line (codeB R N (tbits z)) p).coeff i)
          (d * (800 * (M + m) + 4000) + (z.size + 2) * (40 * m + 60) + 10 * m + 100) := by
  obtain ⟨k, lam, P, o, ho, rfl, hE⟩ := exists_series hp hs
  obtain ⟨out, hout, hval⟩ := exists_word ho
  set K := accK M m N (MvPolynomial.constantCoeff (P o)) k lam with hK
  refine ⟨K, out, hout, nds_accK, ht_accK, fun A _ _ θ z hz => ?_⟩
  have hzm : z.size < 2 ^ m := hz.trans_le hNm
  have hT : ∀ p : List Bool, p.length = m → look p (pairTree m z) = .nil ∨
      ∃ c : List Bool, c.length = 2 ∧ look p (pairTree m z) = ofBits c := by
    intro p hp
    rw [look_pairTree hzm hp]
    exact ltr_cases _
  have ha : ∀ g : List Bool, g.length = M →
      ((allBits m).map fun p =>
          K.lk ([false, true] ++ g ++ p.reverse ++ lc (look p (pairTree m z)) ++ [false])).sum =
        ∑ i, lam (KT.val g) i * codeB R N (tbits z) i := by
    intro g hg
    have h1 : ∀ p ∈ allBits m,
        K.lk ([false, true] ++ g ++ p.reverse ++ lc (look p (pairTree m z)) ++ [false]) =
        (fun w => lamK (lam (KT.val g)) (KT.val w) (((tbits z).map some ++ [none])[KT.val w]?))
            p.reverse := by
      intro p hp
      have hpm := length_of_mem_allBits hp
      rw [look_pairTree hzm hpm, hK, (accK_l hg (by simpa using hpm) (length_lc _)).1, decL_lc]
    rw [List.map_congr_left h1]
    refine (sum_allBits_reverse m fun w => lamK (lam (KT.val g)) (KT.val w)
      (((tbits z).map some ++ [none])[KT.val w]?)).trans ?_
    refine (sum_allBits m fun i =>
        lamK (lam (KT.val g)) i (((tbits z).map some ++ [none])[i]?)).trans ?_
    rw [← Finset.sum_subset (Finset.range_mono hNm), Finset.sum_range, Fintype.sum_prod_type]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rcases Option.eq_none_or_eq_some (((tbits z).map some ++ [none])[(i : ℕ)]?) with hc | ⟨γ, hc⟩
      · simp [codeB, Tape.wordCode, hc, lamK]
      · rw [Finset.sum_eq_single γ]
        · simp [codeB, Tape.wordCode, hc, lamK, i.isLt]
        · intro c _ hne
          simp only [codeB, Tape.wordCode, hc, Option.some.injEq, decide_eq_true_eq]
          rw [ite_eq_right hne.symm, mul_zero]
        · simp
    · intro i _ hi
      exact lamK_ge _ (by simpa using hi) _
  have hloop := loopF_kv (θ := θ) (M := M) (m := m) (T := pairTree m z) (κ := K.lk)
      (S := {q | K.InB 1 q})
    (E := fun g => ser (codeB R N (tbits z)) (P g))
        (a := fun g => ∑ i, lam g i * codeB R N (tbits z) i) (k := k)
    (hE (codeB R N (tbits z)))
    (fun g l r hg hl hr => accK_k hg hl hr) ha
    (fun g p c hg hp hc =>
        (accK_l (γ := MvPolynomial.constantCoeff (P o)) (k := k) (lam := lam) hg hp hc).2) hT
    (2 * (d - 1) + 1) (d - 1) [out] (by simp) (by simpa using hout)
  have h1 := KV.mul (κ := K.lk) (S := {q | K.InB 1 q})
      (Gives.quote (θ := θ) (ofBits [true, false]) z) (by
    rw [path_ofBits]
    exact (accK_c (M := M) (m := m) (γ := MvPolynomial.constantCoeff (P o)) (k := k)
        (lam := lam)).2)
  rw [path_ofBits, hK, accK_c.1, ← hK] at h1
  have h2 := KV.app_gives (κ := K.lk) (S := {q | K.InB 1 q}) (p := (loopF M m).code)
    (Gives.cons (Gives.quote (θ := θ) (loopF M m).code z) (Gives.cons (Gives.quote (num (d - 1)) z)
      (Gives.cons (Gives.quote (listT ([out].map ofBits)) z) (treeF_gives m z)))) (by
        rw [Fm.ofTree_code]
        exact hloop)
  refine ((KV.either h1 h2).mono ?_).congr ?_
  · have e : 2 * (d - 1) + 1 + 1 = 2 * d := by omega
    rw [e]
    have h4 : d * (800 * (M + m) + 4000) = 2 * d * (400 * (M + m) + 2000) := by ring
    have h5 : m * (40 * (z.size + 2) + 10) = 40 * ((z.size + 2) * m) + 10 * m := by ring
    have h6 : (z.size + 2) * (40 * m + 60) = 40 * ((z.size + 2) * m) + 60 * (z.size + 2) := by ring
    omega
  · rw [sum_coeff_line _ _ _ _ hd, List.map_singleton, hval]

end Cslib.Circuits.Arithmetic.Separation.Interpreter
