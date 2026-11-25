/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.TM2.PartrecToTM2
public import CslibFrontier.Computability.Machines.Turing.TM2.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable.Defs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Mathlib.Computability.Partrec
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
import CslibFrontier.Computability.Machines.Turing.TM2.PolyTime
import CslibFrontier.Computability.Machines.Turing.TM2.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeFinitePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeTermination
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.TuringMachine.Config

/-!
# Computable functions are computed by multi-tape Turing machines

Every function that is `Computable` in Mathlib's sense is computed by a total binary multi-tape
Turing machine with finitely many states (`Computable.isComputable`), with the binary encoding
`encNat` of the `Encodable` index of its input and output. This is the converse of
`Turing.MultiTapeTM.IsComputable.computable`.

The proof runs Mathlib's compiler of partial recursive codes to stack machines
(`Turing.PartrecToTM2`), on the finite set of labels its runs visit
(`Turing.PartrecToTM2.finProgram`). One step of a stack machine with finite labels, state and
alphabets is computed in polynomial time on encoded configurations
(`Turing.TM2.stepTotal_polyTime`).
A native loop repeats it until the configuration halts (`Turing.TM2.isComputable_of_eval`). The
loop needs no bound on the number of steps or the size of the stacks: it only uses that the run
halts.

## Main results

* `Turing.TM2.isComputable_of_eval`: a halting run of a stack machine with finite labels, state
  and alphabets, from a configuration computed in polynomial time, is computed by a total machine.
* `Computable.isComputable`: computable functions are computable by total multi-tape machines.
* `Turing.MultiTapeTM.isComputable_iff_computable`: with these encodings, computability by total
  multi-tape machines is Mathlib's computability.
-/

public section

namespace Turing.TM2

open MultiTapeTM ComputableInPolyTime StateTransition

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} {M : Λ → Stmt Γ Λ σ}

/-- A path to a configuration is a number of padded steps, all from unhalted configurations. -/
private theorem exists_iterate_of_reaches {a b : Cfg Γ Λ σ}
    (h : StateTransition.Reaches (step M) a b) :
    ∃ T, (stepTotal M)^[T] a = b ∧ ∀ n < T, ((stepTotal M)^[n] a).l.isSome := by
  induction h with
  | refl => exact ⟨0, rfl, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | @tail c d _ hcd ih =>
    obtain ⟨T, hT, hlt⟩ := ih
    have hc : c.l.isSome := by
      rcases c with ⟨_ | _, _, _⟩
      · exact absurd hcd (by simp [step])
      · rfl
    refine ⟨T + 1, ?_, fun n hn => ?_⟩
    · rw [Function.iterate_succ_apply', hT, stepTotal_of_step, Option.mem_def.1 hcd,
        Option.getD_some]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
      · exact hlt n hn
      · rwa [hT]

/-- One round of the native loop: advance an unhalted configuration, and stop after a halted
one. -/
private def round (M : Λ → Stmt Γ Λ σ) (o : Option (Cfg Γ Λ σ)) : Option (Cfg Γ Λ σ) :=
  o.elim none fun c => if c.l.isSome then some (stepTotal M c) else none

section Finite

variable [Fintype K] [Finite Λ] [Finite σ] [∀ k, Finite (Γ k)]

private theorem round_polyTime :
    ComputableInPolyTime (round M) (encOption encCfg) (encOption encCfg) := by
  refine optionElimWithInput (body := fun _ c => if c.l.isSome then some (stepTotal M c) else none)
    id' (const none) ?_
  have hc := snd (encOption (encCfg (Γ := Γ) (Λ := Λ) (σ := σ))) (encCfg (Γ := Γ) (Λ := Λ) (σ := σ))
  exact ite' (encC := encBool) ((of_finite Option.isSome).comp (cfg_label.comp hc))
    ((optionSome encCfg).comp ((stepTotal_polyTime M).comp hc)) (const none)

end Finite

private theorem iterate_round {a : Cfg Γ Λ σ} {T : ℕ}
    (hlt : ∀ n < T, ((stepTotal M)^[n] a).l.isSome) :
    ∀ n ≤ T, (round M)^[n] (some a) = some ((stepTotal M)^[n] a) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
    simp [round, hlt n (by omega)]

/-- **Halting stack-machine runs are natively computable.** Suppose a stack machine with finite
labels, state and alphabets halts from a configuration `start a` computed in polynomial time, and a
polynomial-time `read` of the halted configuration is the encoded value `f a`. Then `f` is computed
by a total binary multi-tape machine. No bound on the running time or the stacks is assumed. -/
theorem isComputable_of_eval [Fintype K] [Finite Λ] [Finite σ] [∀ k, Finite (Γ k)]
    {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {start : α → Cfg Γ Λ σ} {read : Cfg Γ Λ σ → List Bool}
    (hstart : ComputableInPolyTime start encIn encCfg)
    (hread : ComputableInPolyTime read encCfg encBits)
    (hf : ∀ a, ∃ b ∈ StateTransition.eval (step M) (start a), read b = encOut (f a)) :
    IsComputable f encIn encOut := by
  choose b hb hread_eq using hf
  have hrun (a : α) := exists_iterate_of_reaches (mem_eval.1 (hb a)).1
  choose T hT hlt using hrun
  have hiter (a : α) := iterate_round (M := M) (hlt a)
  have hhalt (a : α) : (b a).l = none := by
    have h := (mem_eval.1 (hb a)).2
    rcases hba : b a with ⟨_ | _, _, _⟩
    · rfl
    · rw [hba] at h
      simp [step] at h
  let fin : Option (Cfg Γ Λ σ) → List Bool := fun o => (o.map read).getD []
  have hfin : ComputableInPolyTime fin (encOption encCfg) encBits :=
    optionGetDWithInput (optionMapWithInput (f := fun _ c => read c) id'
      (hread.comp (snd _ _))) (const [])
  obtain ⟨c, d, hc⟩ := exists_computableInTimeAndSpace_iterateWhile
    (init := fun a => some (start a)) (step := round M) (fin := fin)
    ((optionSome encCfg).comp hstart) round_polyTime hfin (r := T)
    (l := fun a => (Finset.range (T a + 1)).sup fun n =>
      (encOption encCfg ((round M)^[n] (some (start a)))).length)
    (fun a n hn => Finset.le_sup (f := fun n =>
      (encOption encCfg ((round M)^[n] (some (start a)))).length)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hn)))
    (fun a n hn => by rw [hiter a (n + 1) hn]; simp)
    (fun a => by
      rw [Function.iterate_succ_apply', hiter a (T a) le_rfl, hT a]
      simp [round, hhalt a])
  have hval (a : α) : fin ((round M)^[T a] (some (start a))) = encOut (f a) := by
    simp [fin, hiter a (T a) le_rfl, hT a, hread_eq a]
  obtain ⟨k, State, hState, tm, htm⟩ := hc
  exact ComputableInTimeAndSpace.isComputable ⟨k, State, hState, tm, fun a => by
    have h := htm a
    dsimp only at h
    rw [hval a] at h
    exact h⟩

end Turing.TM2

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime Turing.PartrecToTM2

/-- The digits of an encoded number on the main stack, without the list separator. -/
private def readDigits (c : ToPartrec.Code) :
    TM2.Cfg (fun _ : K' => Γ') (Label c) (Option Γ') → List Bool :=
  fun cfg => ((cfg.stk K'.main).filter fun x => x != Γ'.cons).map fun x => x == Γ'.bit1

private theorem readDigits_halt (c : ToPartrec.Code) (n : ℕ)
    (cfg : TM2.Cfg (fun _ : K' => Γ') (Label c) (Option Γ'))
    (h : cfg.mapLabel Subtype.val = halt [n]) : readDigits c cfg = n.bits := by
  have hstk : cfg.stk K'.main = trList [n] := by
    simpa [halt, TM2.Cfg.mapLabel] using congrFun (congrArg TM2.Cfg.stk h) K'.main
  rw [readDigits, hstk, trList, trList, trNat_eq_map_bits]
  simp only [List.filter_append, List.map_append, List.filter_map,
    List.map_map]
  have hfilter : ∀ l : List Bool,
      List.filter ((fun x => x != Γ'.cons) ∘ fun b => if b then Γ'.bit1 else Γ'.bit0) l = l :=
    fun l => List.filter_eq_self.2 fun b _ => by cases b <;> rfl
  simp only [hfilter]
  have hmap : ∀ l : List Bool,
      List.map ((fun x => x == Γ'.bit1) ∘ fun b => if b then Γ'.bit1 else Γ'.bit0) l = l :=
    fun l => by rw [List.map_congr_left (g := id) fun b _ => by cases b <;> rfl, List.map_id]
  simp [hmap]

/-- **Computable functions are computed by multi-tape Turing machines.** A function that is
`Computable` in Mathlib's sense is computed by a total binary multi-tape Turing machine with
finitely many states, from the binary digits `encNat` of the `Encodable` index of the input to
those of the output. This is the converse of `Turing.MultiTapeTM.IsComputable.computable`. -/
theorem Computable.isComputable {α β : Type} [Primcodable α] [Primcodable β] {f : α → β}
    (hf : Computable f) :
    IsComputable f ((Encodable.encode' α).trans encNat) ((Encodable.encode' β).trans encNat) := by
  let g : ℕ → ℕ := fun n =>
    ((Encodable.decode (α := α) n).map fun a => Encodable.encode (f a)).getD 0
  have hg : Computable g :=
    Computable.option_getD (Computable.option_map Computable.decode
      ((Computable.encode.comp hf).comp Computable.snd).to₂) (Computable.const 0)
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.2 hg)
  have heval (a : α) : c.eval [Encodable.encode a] = pure [Encodable.encode (f a)] := by
    simpa [g, Encodable.encodek, List.Vector.head] using hc ⟨[Encodable.encode a], rfl⟩
  refine Turing.TM2.isComputable_of_eval (M := finProgram c)
    (start := fun a => finInit c [Encodable.encode a]) (read := readDigits c) ?_ ?_ fun a => ?_
  · have hbits : ComputableInPolyTime (fun a : α => (Encodable.encode a).bits)
        ((Encodable.encode' α).trans encNat) encBits := ComputableInPolyTime.of_eq fun _ => rfl
    have hdigit : ComputableInPolyTime (fun b : Bool => if b then Γ'.bit1 else Γ'.bit0)
        encBool (encFinite Γ') := ComputableInPolyTime.of_finite _
    have hdigits := (ComputableInPolyTime.map hdigit).comp
      (ComputableInPolyTime.bitsToList.comp hbits)
    have hmain := (ComputableInPolyTime.listAppend (encFinite Γ')).comp
      (hdigits.prod (ComputableInPolyTime.const [Γ'.cons]))
    refine TM2.cfg_mk (ComputableInPolyTime.const _) (ComputableInPolyTime.const none)
      (ComputableInPolyTime.dpi fun k => ?_)
    cases k
    · simpa [finInit, init, TM2.Cfg.mapLabel, trList, trNat_eq_map_bits, Function.comp_def]
        using hmain
    all_goals exact ComputableInPolyTime.const []
  · have hstack := (ComputableInPolyTime.dpi_apply _ K'.main).comp
      (TM2.cfg_stacks (Γ := fun _ : K' => Γ') (Λ := Label c) (σ := Option Γ'))
    have hkeep : ComputableInPolyTime (fun x : Γ' => x != Γ'.cons) (encFinite Γ') encBool :=
      ComputableInPolyTime.of_finite _
    have hbit : ComputableInPolyTime (fun x : Γ' => x == Γ'.bit1) (encFinite Γ') encBool :=
      ComputableInPolyTime.of_finite _
    exact ComputableInPolyTime.listToBits.comp ((ComputableInPolyTime.map hbit).comp
      ((ComputableInPolyTime.filter hkeep).comp hstack))
  · have h := eval_finProgram c [Encodable.encode a]
    rw [heval a] at h
    have hmem : halt [Encodable.encode (f a)] ∈
        TM2.Cfg.mapLabel Subtype.val <$> StateTransition.eval (TM2.step (finProgram c))
          (finInit c [Encodable.encode a]) := h ▸ Part.mem_map halt (Part.mem_some _)
    obtain ⟨b, hb, hbhalt⟩ := (Part.mem_map_iff _).1 hmem
    exact ⟨b, hb, readDigits_halt c _ b hbhalt⟩

/-- Reading a word as a number, least significant bit first, is primitive recursive. -/
private theorem primrec_ofBits : Primrec ofBits := by
  have hbit : Primrec₂ fun (_ : List Bool) (p : Bool × ℕ) => Nat.bit p.1 p.2 :=
    (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂.of_eq
      fun _ p => by cases p.1 <;> rfl
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hbit).of_eq fun _ => rfl

/-- **Computability by multi-tape machines is computability.** With the binary digits `encNat` of
the `Encodable` index of the input and output, a function is computed by a total binary
multi-tape Turing machine with finitely many states exactly when it is `Computable`. -/
theorem Turing.MultiTapeTM.isComputable_iff_computable {α β : Type} [Primcodable α]
    [Primcodable β] {f : α → β} :
    IsComputable f ((Encodable.encode' α).trans encNat) ((Encodable.encode' β).trans encNat) ↔
      Computable f := by
  refine ⟨fun h => ?_, Computable.isComputable⟩
  have hbits := h.computable_enc (primrec_bits.comp Primrec.encode).to_comp
  exact Computable.encode_iff.1 ((primrec_ofBits.to_comp.comp hbits).of_eq fun a => by
    simp [encNat_apply, Encodable.encode'])
