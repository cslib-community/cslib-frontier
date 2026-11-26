/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Clocked
public import CslibFrontier.Foundations.Computability.RecursiveInUniform

/-!
# Oracle codes as clocked oracle programs

Oracle codes `Nat.RecursiveIn.Code` and clocked oracle programs `Cslib.ClockedComp` querying a
single oracle `ℕ →. ℕ` (the interface `Cslib.natOracleSpec`) compute the same partial functions.

* **Code to program.** `Code.toClocked` compiles a code constructor by constructor: composition
  is `bind`, primitive recursion is Lean recursion, and unbounded search is `ClockedComp.rfind`.
  The compiled program computes the code relative to every partial oracle (`eval_toClocked`); it
  does not depend on the oracle.
* **Program to code.** A clocked program is a shallow embedding: its continuations are arbitrary
  Lean functions, so a program may compute a function that is not recursive in its oracle. The
  admissible programs are those whose *dialogue* is computable (`ClockedComp.dialogue`): the
  next move (query or result) for each input, fuel and list of answers received so far. Such a
  family is an oracle machine: its control is computable and only the answers come from the
  oracle. Such a family is computed by a single code relative to every partial oracle
  (`ClockedComp.exists_code_eval`). The code runs the definition of `ClockedComp.eval`: it
  searches for the least fuel that finishes, and runs each fuel by iterating the dialogue
  (`OracleComp.interpret_eq_rfind`).
* **Characterization.** Relative to a partial oracle `g`, a partial function is recursive in `g`
  iff some family of clocked programs with computable dialogue computes it against `g`
  (`recursiveIn_iff_exists_clockedComp`). The forward direction is `toClocked`, whose dialogue
  is computable (`Code.computable_dialogue_toClocked`). The proof goes through the *play* of a
  family (`ClockedComp.play`), the next move together with the answers left over, whose
  computability is closed under `pure`, queries, `bind`, `map`, `rfind` and iterated `bind`.

## Main definitions

* `Cslib.natOracleSpec`: the interface of a single oracle `ℕ →. ℕ`.
* `Cslib.OracleComp.nextMove`, `Cslib.OracleComp.replies`: the next move of a program after given
  answers, and the answers it has received after a number of steps.
* `Cslib.OracleComp.play`: the next move, with the answers a finished program has not used.
* `Cslib.ClockedComp.dialogue`, `Cslib.ClockedComp.play`: the dialogue and the play of a family of
  clocked programs.
* `Nat.RecursiveIn.Code.toClocked`: the clocked program of a code.

## Main results

* `Cslib.OracleComp.interpret_eq_rfind`: running a program is iterating its dialogue.
* `Nat.RecursiveIn.Code.eval_toClocked`: code to program, for every partial oracle.
* `Cslib.ClockedComp.exists_code_eval`, `Cslib.ClockedComp.recursiveIn_eval`: program to code,
  with one code for every partial oracle.
* `Cslib.ClockedComp.computable_play_bind`, `.computable_play_rfind`, `.computable_play_natRec`
  and their siblings: computable plays are closed under the program constructors.
* `Nat.RecursiveIn.Code.computable_dialogue_toClocked`: compiled programs have computable
  dialogues.
* `Nat.RecursiveIn.Code.recursiveIn_iff_exists_clockedComp`: recursiveness in a partial oracle is
  computability by clocked programs querying it.

## Implementation notes

A query to a point where the oracle is undefined diverges, as in `Nat.RecursiveIn`, so the
characterization holds for partial oracles. The dialogue of a bind needs to know how many answers
its first part consumed; the play records the answers left over, and the dialogue is read off it
(`ClockedComp.computable_dialogue_of_play`).

-/

@[expose] public section

namespace Cslib

/-- The interface of a single oracle `ℕ →. ℕ`: a query is a number and so is its answer. -/
abbrev natOracleSpec : OracleSpec ℕ := fun _ => ℕ

namespace OracleComp

variable {α : Type}

/-- The next move of a program over `natOracleSpec` once it has received the answers `rs` to its
first queries: its next query, or its result. Answers after the result are ignored. -/
def nextMove : OracleComp natOracleSpec α → List ℕ → ℕ ⊕ α
  | .pure a, _ => .inr a
  | .liftBind q _, [] => .inl q
  | .liftBind _ k, r :: rs => nextMove (k r) rs

/-- The play of a program over `natOracleSpec` on the answers `rs`: its next query once the
answers run out, or its result together with the answers it has not used. -/
def play : OracleComp natOracleSpec α → List ℕ → ℕ ⊕ (α × List ℕ)
  | .pure a, rs => .inr (a, rs)
  | .liftBind q _, [] => .inl q
  | .liftBind _ k, r :: rs => play (k r) rs

theorem nextMove_eq_play : ∀ (T : OracleComp natOracleSpec α) (rs : List ℕ),
    nextMove T rs = Sum.map id Prod.fst (play T rs)
  | .pure _, _ => rfl
  | .liftBind _ _, [] => rfl
  | .liftBind _ k, r :: rs => nextMove_eq_play (k r) rs

/-- Playing `T >>= f` plays `T`, then `f` of its result on the answers left over. -/
theorem play_bind {β : Type} : ∀ (T : OracleComp natOracleSpec α)
    (f : α → OracleComp natOracleSpec β) (rs : List ℕ),
    play (T >>= f) rs = Sum.elim Sum.inl (fun p => play (f p.1) p.2) (play T rs)
  | .pure _, _, _ => rfl
  | .liftBind _ _, _, [] => rfl
  | .liftBind _ k, f, r :: rs => play_bind (k r) f rs

/-- One step of running a program against `g`: ask its next query and append the answer, or
stay put once the program has a result. -/
def stepReplies (g : ℕ →. ℕ) (T : OracleComp natOracleSpec α) (rs : List ℕ) : Part (List ℕ) :=
  match nextMove T rs with
  | .inl q => (g q).map (rs ++ [·])
  | .inr _ => Part.some rs

/-- The answers `T` has received from `g` after `t` steps. -/
def replies (g : ℕ →. ℕ) (T : OracleComp natOracleSpec α) : ℕ → Part (List ℕ)
  | 0 => Part.some []
  | t + 1 => (replies g T t).bind (stepReplies g T)

theorem replies_pure (g : ℕ →. ℕ) (a : α) :
    ∀ t, replies g (.pure a : OracleComp natOracleSpec α) t = Part.some []
  | 0 => rfl
  | t + 1 => by rw [replies, replies_pure g a t, Part.bind_some]; rfl

theorem replies_liftBind (g : ℕ →. ℕ) (q : ℕ) (k : ℕ → OracleComp natOracleSpec α) :
    ∀ t, replies g (.liftBind q k) (t + 1) = (g q).bind fun r => (replies g (k r) t).map (r :: ·)
  | 0 => by
    simp only [replies, Part.bind_some, Part.map_some]
    simp [stepReplies, nextMove, Part.bind_some_eq_map]
  | t + 1 => by
    rw [replies, replies_liftBind g q k t, Part.bind_assoc]
    refine congrArg _ (funext fun r => ?_)
    rw [Part.bind_map, replies, Part.map_bind]
    refine congrArg _ (funext fun rs => ?_)
    cases h : nextMove (k r) rs <;>
      simp [stepReplies, nextMove, h, Part.map_map, Function.comp_def]

/-- A program returns `a` against `g` iff some finite reply trace leads to the result `a`. -/
theorem mem_interpret_iff (g : ℕ →. ℕ) :
    ∀ (T : OracleComp natOracleSpec α) (a : α),
      a ∈ OracleComp.interpret g T ↔ ∃ t rs, rs ∈ replies g T t ∧ nextMove T rs = .inr a
  | .pure b, a => by
    change a ∈ Part.some b ↔ _
    simp only [nextMove, Sum.inr.injEq, Part.mem_some_iff, eq_comm (a := a)]
    exact ⟨fun h => ⟨0, [], Part.mem_some _, h⟩, fun ⟨_, _, _, h⟩ => h⟩
  | .liftBind q k, a => by
    change a ∈ (g q).bind (fun r => OracleComp.interpret g (k r)) ↔ _
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨r, hr, h⟩ := Part.mem_bind_iff.1 h
      obtain ⟨t, rs, hrs, hn⟩ := (mem_interpret_iff g (k r) a).1 h
      exact ⟨t + 1, r :: rs,
        (replies_liftBind g q k t).symm ▸ Part.mem_bind_iff.2 ⟨r, hr, Part.mem_map _ hrs⟩, hn⟩
    · rintro ⟨_ | t, rs, hrs, hn⟩
      · cases Part.mem_some_iff.1 hrs ▸ hn
      · obtain ⟨r, hr, hrs⟩ := Part.mem_bind_iff.1 (replies_liftBind g q k t ▸ hrs)
        obtain ⟨rs', hrs', rfl⟩ := (Part.mem_map_iff _).1 hrs
        exact Part.mem_bind_iff.2 ⟨r, hr, (mem_interpret_iff g (k r) a).2 ⟨t, rs', hrs', hn⟩⟩

theorem replies_dom_of_le {g : ℕ →. ℕ} {T : OracleComp natOracleSpec α} {m : ℕ} :
    ∀ {t}, (replies g T t).Dom → m ≤ t → (replies g T m).Dom
  | 0, h, hm => by rwa [Nat.le_zero.1 hm]
  | t + 1, h, hm => by
    rcases Nat.eq_or_lt_of_le hm with rfl | hm
    · exact h
    · exact replies_dom_of_le (Part.Dom.of_bind h) (Nat.lt_succ_iff.1 hm)

/-- Running a program against `g` iterates `stepReplies` up to the first step whose next move is
a result, and returns that result. -/
theorem interpret_eq_rfind [Inhabited α] (g : ℕ →. ℕ) (T : OracleComp natOracleSpec α) :
    OracleComp.interpret g T =
      (Nat.rfind fun t => (replies g T t).map fun rs => (nextMove T rs).isRight).bind fun t =>
        (replies g T t).map fun rs => (nextMove T rs).elim (fun _ => default) id := by
  ext a
  rw [Part.mem_bind_iff]
  constructor
  · intro ha
    obtain ⟨t, rs, hrs, hn⟩ := (mem_interpret_iff g T a).1 ha
    have hex : ∃ t, ∃ rs ∈ replies g T t, (nextMove T rs).isRight := ⟨t, rs, hrs, by simp [hn]⟩
    classical
    obtain ⟨rs₀, hrs₀, hn₀⟩ := Nat.find_spec hex
    have hdom : ∀ m < Nat.find hex, (replies g T m).Dom := fun m hm =>
      replies_dom_of_le hrs₀.fst hm.le
    refine ⟨Nat.find hex, Nat.mem_rfind.2 ⟨(Part.mem_map_iff _).2 ⟨rs₀, hrs₀, hn₀⟩,
      fun {m} hm => ?_⟩, ?_⟩
    · refine (Part.mem_map_iff _).2 ⟨(replies g T m).get (hdom m hm), Part.get_mem _, ?_⟩
      simpa using fun h => Nat.find_min hex hm ⟨_, Part.get_mem _, h⟩
    · cases h : nextMove T rs₀ with
      | inl _ => simp [h] at hn₀
      | inr b =>
        obtain rfl := Part.mem_unique ha ((mem_interpret_iff g T b).2 ⟨_, rs₀, hrs₀, h⟩)
        exact (Part.mem_map_iff _).2 ⟨rs₀, hrs₀, by simp [h]⟩
  · rintro ⟨t, ht, ha⟩
    obtain ⟨rs, hrs, hfl⟩ := (Part.mem_map_iff _).1 (Nat.rfind_spec ht)
    obtain ⟨rs', hrs', rfl⟩ := (Part.mem_map_iff _).1 ha
    obtain rfl := Part.mem_unique hrs hrs'
    cases h : nextMove T rs with
    | inl _ => simp [h] at hfl
    | inr b => simpa [h] using (mem_interpret_iff g T b).2 ⟨t, rs, hrs, h⟩

end OracleComp

namespace ClockedComp

open Nat.RecursiveIn.Code (HasUniformCode)

/-- The dialogue of a family of clocked programs on natural numbers: the next move of the program
for input `n` run with fuel `k`, after it has received the answers `rs`. A family whose dialogue
is computable is an oracle machine: its control is computable, and only the answers to its
queries come from the oracle. -/
def dialogue (P : ℕ → ClockedComp natOracleSpec ℕ) : (ℕ × ℕ) × List ℕ → ℕ ⊕ Option ℕ
  | ((n, k), rs) => OracleComp.nextMove ((P n) k).run rs

section Compile

variable {P : ℕ → ClockedComp natOracleSpec ℕ}

private abbrev State := (ℕ × ℕ) × List ℕ

private def decodeState (s : ℕ) : State := (Encodable.decode s).getD default

private theorem computable_decodeState : Computable decodeState :=
  Computable.option_getD Primrec.decode.to_comp (Computable.const _)

private theorem decodeState_encode (x : State) : decodeState (Encodable.encode x) = x := by
  simp only [decodeState, Encodable.encodek, Option.getD_some]

/-- The run of input and fuel `nk`, without the reader layer. -/
private abbrev run (P : ℕ → ClockedComp natOracleSpec ℕ) (nk : ℕ) :
    OracleComp natOracleSpec (Option ℕ) :=
  ((P nk.unpair.1) nk.unpair.2).run

/-- The encoded state of the run `nk` after receiving `rs`. -/
private abbrev enc (nk : ℕ) (rs : List ℕ) : ℕ :=
  Encodable.encode (((nk.unpair.1, nk.unpair.2), rs) : State)

private theorem computable_move (hP : Computable (dialogue P)) :
    Computable fun s => dialogue P (decodeState s) :=
  hP.comp computable_decodeState

/-- `0` once the program has a result, `1` while it still queries. -/
private def busy (P : ℕ → ClockedComp natOracleSpec ℕ) (s : ℕ) : ℕ :=
  Sum.elim (fun _ => 1) (fun _ => 0) (dialogue P (decodeState s))

private def nextQuery (P : ℕ → ClockedComp natOracleSpec ℕ) (s : ℕ) : ℕ :=
  Sum.elim id (fun _ => 0) (dialogue P (decodeState s))

private def push (p : ℕ) : ℕ :=
  Encodable.encode ((decodeState p.unpair.1).1, (decodeState p.unpair.1).2 ++ [p.unpair.2])

private def output (P : ℕ → ClockedComp natOracleSpec ℕ) (s : ℕ) : ℕ :=
  Encodable.encode (Sum.elim (fun _ => (none : Option ℕ)) id (dialogue P (decodeState s)))

private theorem computable_busy (hP : Computable (dialogue P)) : Computable (busy P) :=
  Computable.sumCasesOn (computable_move hP) (Computable.const 1).to₂ (Computable.const 0).to₂

private theorem computable_nextQuery (hP : Computable (dialogue P)) : Computable (nextQuery P) :=
  Computable.sumCasesOn (computable_move hP) Computable.snd.to₂ (Computable.const 0).to₂

private theorem computable_push : Computable push := by
  have hd : Computable fun p : ℕ => decodeState p.unpair.1 :=
    computable_decodeState.comp (Computable.fst.comp Primrec.unpair.to_comp)
  exact Computable.encode.comp ((Computable.fst.comp hd).pair
    (Computable.list_concat.comp (Computable.snd.comp hd)
      (Computable.snd.comp Primrec.unpair.to_comp)))

private theorem computable_output (hP : Computable (dialogue P)) : Computable (output P) :=
  Computable.encode.comp (Computable.sumCasesOn (computable_move hP) (Computable.const none).to₂
    Computable.snd.to₂)

private theorem busy_enc (nk : ℕ) (rs : List ℕ) :
    busy P (enc nk rs) =
      Sum.elim (fun _ => 1) (fun _ => 0) (OracleComp.nextMove (run P nk) rs) := by
  simp only [busy, enc, decodeState_encode, dialogue, run]

private theorem nextQuery_enc (nk : ℕ) (rs : List ℕ) :
    nextQuery P (enc nk rs) = Sum.elim id (fun _ => 0) (OracleComp.nextMove (run P nk) rs) := by
  simp only [nextQuery, enc, decodeState_encode, dialogue, run]

private theorem output_enc (nk : ℕ) (rs : List ℕ) :
    output P (enc nk rs) = Encodable.encode
      ((OracleComp.nextMove (run P nk) rs).elim (fun _ => default) id) := by
  simp only [output, enc, decodeState_encode, dialogue, run]
  cases OracleComp.nextMove ((P nk.unpair.1) nk.unpair.2).run rs <;> rfl

private theorem push_enc (nk : ℕ) (rs : List ℕ) (r : ℕ) :
    push (Nat.pair (enc nk rs) r) = enc nk (rs ++ [r]) := by
  simp only [push, enc, Nat.unpair_pair, decodeState_encode]

/-- One step of the encoded run. -/
private theorem hasUniformCode_step (hP : Computable (dialogue P)) : HasUniformCode id fun g s =>
    if busy P s = 0 then Part.some s else (g (nextQuery P s)).map fun r => push (Nat.pair s r) := by
  refine (HasUniformCode.ite (computable_busy hP)
    ((HasUniformCode.of_computable computable_push).comp
      ((HasUniformCode.of_primrec Nat.Primrec.id).pair
        ((HasUniformCode.oracle (o := id)).comp
          (HasUniformCode.of_computable (computable_nextQuery hP)))))).of_eq fun g s => ?_
  split_ifs
  · rfl
  · have e : Part.some (nextQuery P s) >>= g = g (nextQuery P s) := Part.bind_some _ _
    simp [Seq.seq, Part.bind_some_eq_map, Part.map_map, Function.comp_def, e]

private theorem step_enc (g : ℕ →. ℕ) (nk : ℕ) (rs : List ℕ) :
    (if busy P (enc nk rs) = 0 then Part.some (enc nk rs)
      else (g (nextQuery P (enc nk rs))).map fun r => push (Nat.pair (enc nk rs) r)) =
      (OracleComp.stepReplies g (run P nk) rs).map (enc nk) := by
  rw [busy_enc, nextQuery_enc, OracleComp.stepReplies]
  cases OracleComp.nextMove (run P nk) rs with
  | inl q => simp only [Part.map_map, Function.comp_def, push_enc]; rfl
  | inr _ => simp

/-- The encoded state of the run `p.unpair.1` after `p.unpair.2` steps. -/
private theorem hasUniformCode_replies (hP : Computable (dialogue P)) : HasUniformCode id fun g p =>
    (OracleComp.replies g (run P p.unpair.1) p.unpair.2).map (enc p.unpair.1) := by
  have hbase : Computable fun nk => enc nk [] :=
    Computable.encode.comp (Primrec.unpair.to_comp.pair (Computable.const []))
  have hrr : Nat.Primrec fun p => p.unpair.2.unpair.2 := Nat.Primrec.right.comp Nat.Primrec.right
  refine (HasUniformCode.prec (HasUniformCode.of_computable hbase)
    ((hasUniformCode_step hP).comp (HasUniformCode.of_primrec hrr))).of_eq fun g p => ?_
  rw [Nat.unpaired]
  induction p.unpair.2 with
  | zero => rfl
  | succ t ih =>
    simp only
    rw [ih, OracleComp.replies, Part.map_bind]
    change ((OracleComp.replies g (run P p.unpair.1) t).map (enc p.unpair.1)).bind _ = _
    rw [Part.bind_map]
    refine congrArg _ (funext fun rs => ?_)
    simp only [Nat.unpair_pair, ← step_enc]
    exact Part.bind_some _ _

/-- The first step at which the run `nk` has a result. -/
private theorem hasUniformCode_haltTime (hP : Computable (dialogue P)) :
    HasUniformCode id fun g nk => Nat.rfind fun t =>
      (OracleComp.replies g (run P nk) t).map fun rs =>
        (OracleComp.nextMove (run P nk) rs).isRight := by
  refine (HasUniformCode.rfind ((HasUniformCode.of_computable (computable_busy hP)).comp
    (hasUniformCode_replies hP))).of_eq fun g nk => ?_
  refine congrArg _ (funext fun t => ?_)
  simp only [Nat.unpair_pair]
  change Part.map _ (((OracleComp.replies g (run P nk) t).map (enc nk)).bind _) = _
  rw [Part.bind_map]
  simp only [Function.comp_def, busy_enc, Part.bind_some_eq_map, Part.map_map]
  refine congrArg (Part.map · _) (funext fun rs => ?_)
  cases OracleComp.nextMove (run P nk) rs <;> rfl

/-- The encoded result of the run with fuel `nk.unpair.2` on input `nk.unpair.1`. -/
private theorem hasUniformCode_attempt (hP : Computable (dialogue P)) :
    HasUniformCode id fun g nk => (attempt g (P nk.unpair.1) nk.unpair.2).map Encodable.encode := by
  refine ((HasUniformCode.of_computable (computable_output hP)).comp
    ((hasUniformCode_replies hP).comp ((HasUniformCode.of_primrec Nat.Primrec.id).pair
      (hasUniformCode_haltTime hP)))).of_eq fun g nk => ?_
  change _ = (OracleComp.interpret g (run P nk)).map Encodable.encode
  rw [OracleComp.interpret_eq_rfind, Part.map_bind]
  simp only [Seq.seq, id_eq, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc, Function.comp_def,
    Part.bind_some_eq_map, Part.map_map]
  change Part.map (output P) ((Part.some (Nat.pair nk)).bind _) = _
  simp only [Part.bind_some, Nat.unpair_pair, Part.map_bind, Part.map_map, Function.comp_def,
    output_enc]

/-- The least fuel for which the run on input `n` finishes. -/
private theorem hasUniformCode_fuel (hP : Computable (dialogue P)) :
    HasUniformCode id fun g n => Nat.rfind fun k => (attempt g (P n) k).map Option.isSome := by
  have hsub : Computable fun e : ℕ => 1 - e :=
    (Primrec₂.to_comp Primrec.nat_sub).comp (Computable.const 1) Computable.id
  refine (HasUniformCode.rfind ((HasUniformCode.of_computable hsub).comp
    (hasUniformCode_attempt hP))).of_eq fun g n => ?_
  refine congrArg _ (funext fun k => ?_)
  simp only [Nat.unpair_pair]
  change Part.map _ (((attempt g (P n) k).map Encodable.encode).bind _) = _
  rw [Part.bind_map]
  simp only [Function.comp_def, Part.bind_some_eq_map, Part.map_map]
  refine congrArg (Part.map · _) (funext fun r => ?_)
  cases r <;> simp [Encodable.encode_some, Encodable.encode_nat]

private theorem bind_rfind_congr {α : Type} {p : ℕ →. Bool} {f f' : ℕ → Part α}
    (h : ∀ k ∈ Nat.rfind p, f k = f' k) : (Nat.rfind p).bind f = (Nat.rfind p).bind f' := by
  ext a
  simp only [Part.mem_bind_iff]
  exact ⟨fun ⟨k, hk, ha⟩ => ⟨k, hk, h k hk ▸ ha⟩, fun ⟨k, hk, ha⟩ => ⟨k, hk, (h k hk).symm ▸ ha⟩⟩

/-- **Program to code.** A family of clocked programs whose dialogue is computable is computed by
a single oracle code, relative to every partial oracle. The code follows the definition of
`ClockedComp.eval`: it searches for the least fuel that finishes, running each fuel by
iterating the dialogue and querying the oracle at each requested point. -/
theorem exists_code_eval (hP : Computable (dialogue P)) :
    ∃ c : Nat.RecursiveIn.Code, ∀ g : ℕ →. ℕ, c.eval g = fun n => eval g (P n) := by
  have hpred : Computable fun e : ℕ => e - 1 :=
    (Primrec₂.to_comp Primrec.nat_sub).comp Computable.id (Computable.const 1)
  obtain ⟨c, hc⟩ := ((HasUniformCode.of_computable hpred).comp ((hasUniformCode_attempt hP).comp
    ((HasUniformCode.of_primrec Nat.Primrec.id).pair (hasUniformCode_fuel hP)))).of_eq
      (G := fun g n => eval g (P n)) fun g n => by
        simp only [Seq.seq, id_eq, Part.bind_eq_bind, Part.bind_map, Part.bind_assoc,
          Part.bind_some_eq_map]
        change Part.map _ ((Part.some (Nat.pair n)).bind _) = _
        simp only [Part.bind_some, Nat.unpair_pair, Part.map_bind, Part.map_map,
          Function.comp_def]
        change _ = (Nat.rfind fun k => (attempt g (P n) k).map Option.isSome).bind fun k =>
          (attempt g (P n) k).bind fun r => (r : Part ℕ)
        refine bind_rfind_congr fun k hk => ?_
        obtain ⟨r, hr, hs⟩ := (Part.mem_map_iff _).1 (Nat.rfind_spec hk)
        obtain ⟨b, rfl⟩ := Option.isSome_iff_exists.1 hs
        rw [Part.eq_some_iff.2 hr, Part.map_some, Part.bind_some]
        simp [Encodable.encode_some, Encodable.encode_nat]
  exact ⟨c, hc⟩

/-- Every family of clocked programs with computable dialogue computes a function recursive in
the oracle it queries. -/
theorem recursiveIn_eval (hP : Computable (dialogue P)) (g : ℕ →. ℕ) :
    Nat.RecursiveIn {g} fun n => eval g (P n) := by
  obtain ⟨c, hc⟩ := exists_code_eval hP
  exact Nat.RecursiveIn.Code.exists_code.2 ⟨c, hc g⟩

end Compile

section Play

open Computable

variable {σ τ β γ : Type}

/-- The play of a family of clocked programs over `natOracleSpec`: for an input, a fuel and the
answers received so far, the next query, or the result of the run together with the unused
answers. -/
def play (P : σ → ClockedComp natOracleSpec β) : (σ × ℕ) × List ℕ → ℕ ⊕ (Option β × List ℕ)
  | ((x, k), rs) => OracleComp.play ((P x) k).run rs

@[simp] theorem play_apply (P : σ → ClockedComp natOracleSpec β) (x : σ) (k : ℕ) (rs : List ℕ) :
    play P ((x, k), rs) = OracleComp.play ((P x) k).run rs := rfl

/-- Play the run with fuel `k` of `P >>= f`: play `P`, then `f` on its result with the answers
left over. -/
theorem play_run_bind (P : ClockedComp natOracleSpec β) (f : β → ClockedComp natOracleSpec γ)
    (k : ℕ) (rs : List ℕ) :
    OracleComp.play ((P >>= f) k).run rs = Sum.elim Sum.inl (fun p => Option.elim p.1
      (Sum.inr (none, p.2)) fun a => OracleComp.play ((f a) k).run p.2)
      (OracleComp.play (P k).run rs) := by
  change OracleComp.play ((P k >>= fun a => f a k).run) rs = _
  rw [OptionT.run_bind, Option.elimM, OracleComp.play_bind]
  cases OracleComp.play (P k).run rs with
  | inl q => rfl
  | inr p => rcases p with ⟨_ | a, rs'⟩ <;> rfl

section Rfind

variable (p : σ × ℕ → ClockedComp natOracleSpec Bool) (x : σ) (k : ℕ)

/-- One trial of the search with fuel `k`: on `inr (i, rs)`, play `p (x, i)`; stop with its query,
with `none` if it runs out of fuel, with `some i` if it returns `true`, and go on to `i + 1` if it
returns `false`. -/
private def rfindStep (t : (ℕ ⊕ (Option ℕ × List ℕ)) ⊕ (ℕ × List ℕ)) :
    (ℕ ⊕ (Option ℕ × List ℕ)) ⊕ (ℕ × List ℕ) :=
  Sum.elim Sum.inl (fun c => Sum.elim (fun q => Sum.inl (Sum.inl q))
    (fun r => Option.elim r.1 (Sum.inl (Sum.inr (none, r.2)))
      fun b => cond b (Sum.inl (Sum.inr (some c.1, r.2))) (Sum.inr (c.1 + 1, r.2)))
    (play p (((x, c.1), k), c.2))) t

private def rfindDone (t : (ℕ ⊕ (Option ℕ × List ℕ)) ⊕ (ℕ × List ℕ)) : ℕ ⊕ (Option ℕ × List ℕ) :=
  Sum.elim id (fun c => Sum.inr (none, c.2)) t

private theorem rfindStep_iterate_inl (d : ℕ ⊕ (Option ℕ × List ℕ)) :
    ∀ n, (rfindStep p x k)^[n] (Sum.inl d) = Sum.inl d
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact rfindStep_iterate_inl d n

private theorem play_rfindFrom : ∀ (r i : ℕ) (rs : List ℕ),
    OracleComp.play (rfindFrom (fun i => p (x, i)) k r i).run rs =
      rfindDone ((rfindStep p x k)^[r] (Sum.inr (i, rs)))
  | 0, i, rs => rfl
  | r + 1, i, rs => by
    change OracleComp.play ((p (x, i) k >>= fun b =>
      if b then pure i else rfindFrom (fun i => p (x, i)) k r (i + 1)).run) rs = _
    rw [OptionT.run_bind, Option.elimM, OracleComp.play_bind, Function.iterate_succ_apply]
    change _ = rfindDone ((rfindStep p x k)^[r] (Sum.elim _ _ (play p (((x, i), k), rs))))
    rw [play_apply]
    rcases OracleComp.play (p (x, i) k).run rs with q | ⟨_ | _ | _, rs'⟩
    all_goals first
      | exact play_rfindFrom r (i + 1) rs'
      | exact (congrArg rfindDone (rfindStep_iterate_inl p x k _ r)).symm

end Rfind

private theorem play_natRec (P : σ → ClockedComp natOracleSpec β)
    (g : σ × ℕ × β → ClockedComp natOracleSpec β) (x : σ) (k : ℕ) (rs : List ℕ) :
    ∀ n, OracleComp.play ((Nat.rec (motive := fun _ => ClockedComp natOracleSpec β) (P x)
        (fun y ih => ih >>= fun i => g (x, y, i)) n) k).run rs =
      Nat.rec (motive := fun _ => ℕ ⊕ (Option β × List ℕ)) (play P ((x, k), rs))
        (fun y t => Sum.elim Sum.inl (fun p => Option.elim p.1 (Sum.inr (none, p.2))
          fun i => play g (((x, y, i), k), p.2)) t) n
  | 0 => rfl
  | n + 1 => by
    change OracleComp.play (((Nat.rec (motive := fun _ => ClockedComp natOracleSpec β) (P x)
        (fun y ih => ih >>= fun i => g (x, y, i)) n) >>= fun i => g (x, n, i)) k).run rs = _
    rw [play_run_bind, play_natRec P g x k rs n]
    rfl

private theorem rec_eq_iterate {α : Type} (f : α → α) (s : α) :
    ∀ n, Nat.rec (motive := fun _ => α) s (fun _ t => f t) n = f^[n] s
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', ← rec_eq_iterate f s n]

variable [Primcodable σ] [Primcodable τ] [Primcodable β] [Primcodable γ]

/-- A family with computable play has a computable dialogue. -/
theorem computable_dialogue_of_play {P : ℕ → ClockedComp natOracleSpec ℕ}
    (hP : Computable (play P)) : Computable (dialogue P) := by
  refine (sumCasesOn hP (sumInl.comp snd).to₂ (sumInr.comp (fst.comp snd)).to₂).of_eq
    fun x => ?_
  rw [show dialogue P x = Sum.map id Prod.fst (play P x) from
    OracleComp.nextMove_eq_play _ _]
  cases play P x <;> rfl

/-! Closure of computable plays under the program constructors. -/

theorem computable_play_comp {P : σ → ClockedComp natOracleSpec β} (hP : Computable (play P))
    {g : τ → σ} (hg : Computable g) : Computable (play fun y => P (g y)) :=
  hP.comp (((hg.comp (fst.comp fst)).pair (snd.comp fst)).pair snd)

theorem computable_play_pure {f : σ → β} (hf : Computable f) :
    Computable (play fun x => (pure (f x) : ClockedComp natOracleSpec β)) :=
  (sumInr.comp ((option_some.comp (hf.comp (fst.comp fst))).pair snd)).of_eq fun _ => rfl

theorem computable_play_query {f : σ → ℕ} (hf : Computable f) :
    Computable (play fun x => ClockedComp.query (spec := natOracleSpec) (f x)) := by
  refine (option_casesOn (Primrec.list_head?.to_comp.comp snd)
    (sumInl.comp (hf.comp (fst.comp fst)))
    (sumInr.comp ((option_some.comp snd).pair
      (Primrec.list_tail.to_comp.comp (snd.comp fst)))).to₂).of_eq fun x => ?_
  rcases x with ⟨⟨x, k⟩, _ | ⟨r, rs⟩⟩ <;> rfl

theorem computable_play_bind {P : σ → ClockedComp natOracleSpec β}
    {f : σ → β → ClockedComp natOracleSpec γ} (hP : Computable (play P))
    (hf : Computable (play fun y : σ × β => f y.1 y.2)) :
    Computable (play fun x => P x >>= f x) := by
  have hg : Computable₂ fun (x : (σ × ℕ) × List ℕ) (p : Option β × List ℕ) =>
      Option.elim p.1 (Sum.inr (none, p.2) : ℕ ⊕ (Option γ × List ℕ))
        fun a => play (fun y : σ × β => f y.1 y.2) (((x.1.1, a), x.1.2), p.2) := by
    refine (option_casesOn (fst.comp snd) (sumInr.comp ((const none).pair (snd.comp snd)))
      (hf.comp ((((fst.comp (fst.comp (fst.comp fst))).pair snd).pair
        (snd.comp (fst.comp (fst.comp fst)))).pair (snd.comp (snd.comp fst)))).to₂).to₂.of_eq
      fun x => ?_
    rcases x with ⟨_, ⟨_ | _, _⟩⟩ <;> rfl
  refine (sumCasesOn hP (sumInl.comp snd).to₂ hg).of_eq fun x => ?_
  rcases x with ⟨⟨x, k⟩, rs⟩
  change _ = OracleComp.play ((P x >>= f x) k).run rs
  rw [play_run_bind]
  change _ = Sum.elim _ _ (play P ((x, k), rs))
  cases play P ((x, k), rs) with
  | inl q => rfl
  | inr p => rcases p with ⟨_ | a, rs'⟩ <;> rfl

theorem computable_play_map {P : σ → ClockedComp natOracleSpec β} {f : σ → β → γ}
    (hP : Computable (play P)) (hf : Computable₂ f) :
    Computable (play fun x => f x <$> P x) := by
  refine (computable_play_bind hP (f := fun x a => pure (f x a))
    (computable_play_pure (hf.comp fst snd))).of_eq fun x => ?_
  rcases x with ⟨⟨x, k⟩, rs⟩
  simp only [play_apply, map_eq_bind_pure_comp, Function.comp_def]

theorem computable_play_rfind {p : σ × ℕ → ClockedComp natOracleSpec Bool}
    (hp : Computable (play p)) : Computable (play fun x => rfind fun i => p (x, i)) := by
  -- the search state `inr (i, rs)` in context `z = ((a, t), (i, rs))`
  have hplay : Computable fun z : (((σ × ℕ) × List ℕ) × ((ℕ ⊕ (Option ℕ × List ℕ)) ⊕
      (ℕ × List ℕ))) × (ℕ × List ℕ) => play p (((z.1.1.1.1, z.2.1), z.1.1.1.2), z.2.2) :=
    hp.comp ((((fst.comp (fst.comp (fst.comp fst))).pair (fst.comp snd)).pair
      (snd.comp (fst.comp (fst.comp fst)))).pair (snd.comp snd))
  have hcond : Computable₂ fun (w : ((((σ × ℕ) × List ℕ) × ((ℕ ⊕ (Option ℕ × List ℕ)) ⊕
      (ℕ × List ℕ))) × (ℕ × List ℕ)) × (Option Bool × List ℕ)) (b : Bool) =>
      (cond b (Sum.inl (Sum.inr (some w.1.2.1, w.2.2))) (Sum.inr (w.1.2.1 + 1, w.2.2)) :
        (ℕ ⊕ (Option ℕ × List ℕ)) ⊕ (ℕ × List ℕ)) :=
    (Computable.cond snd
      (sumInl.comp (sumInr.comp ((option_some.comp (fst.comp (snd.comp (fst.comp fst)))).pair
        (snd.comp (snd.comp fst)))))
      (sumInr.comp ((Primrec.succ.to_comp.comp (fst.comp (snd.comp (fst.comp fst)))).pair
        (snd.comp (snd.comp fst))))).to₂
  have hrun : Computable₂ fun (z : (((σ × ℕ) × List ℕ) × ((ℕ ⊕ (Option ℕ × List ℕ)) ⊕
      (ℕ × List ℕ)))) (c : ℕ × List ℕ) =>
      (Sum.elim (fun q => Sum.inl (Sum.inl q))
        (fun r => Option.elim r.1 (Sum.inl (Sum.inr (none, r.2)))
          fun b => cond b (Sum.inl (Sum.inr (some c.1, r.2))) (Sum.inr (c.1 + 1, r.2)))
        (play p (((z.1.1.1, c.1), z.1.1.2), c.2)) : (ℕ ⊕ (Option ℕ × List ℕ)) ⊕ (ℕ × List ℕ)) := by
    refine (sumCasesOn hplay (sumInl.comp (sumInl.comp snd)).to₂
      (option_casesOn (fst.comp snd) (sumInl.comp (sumInr.comp ((const none).pair
        (snd.comp snd)))) hcond).to₂).to₂.of_eq fun z => ?_
    rcases h : play p (((z.1.1.1.1, z.2.1), z.1.1.1.2), z.2.2) with q | ⟨_ | _ | _, rs⟩ <;>
      simp [h]
  have hstep : Computable₂ fun (a : (σ × ℕ) × List ℕ)
      (t : (ℕ ⊕ (Option ℕ × List ℕ)) ⊕ (ℕ × List ℕ)) => rfindStep p a.1.1 a.1.2 t := by
    refine (sumCasesOn snd (sumInl.comp snd).to₂ hrun).to₂.of_eq fun z => ?_
    rcases z with ⟨a, _ | _⟩ <;> rfl
  have hdone : Computable fun t : (ℕ ⊕ (Option ℕ × List ℕ)) ⊕ (ℕ × List ℕ) => rfindDone t :=
    (sumCasesOn Computable.id snd.to₂ (sumInr.comp ((const none).pair (snd.comp snd))).to₂).of_eq
      fun t => by cases t <;> rfl
  refine (hdone.comp (nat_rec (snd.comp fst) (sumInr.comp ((const 0).pair snd))
    (hstep.comp fst (snd.comp snd)).to₂)).of_eq fun a => ?_
  rcases a with ⟨⟨x, k⟩, rs⟩
  change _ = OracleComp.play (rfindFrom (fun i => p (x, i)) k k 0).run rs
  rw [play_rfindFrom, ← rec_eq_iterate]

theorem computable_play_natRec {m : σ → ℕ} {P : σ → ClockedComp natOracleSpec β}
    {g : σ × ℕ × β → ClockedComp natOracleSpec β} (hm : Computable m)
    (hP : Computable (play P)) (hg : Computable (play g)) :
    Computable (play fun x => Nat.rec (motive := fun _ => ClockedComp natOracleSpec β) (P x)
      (fun y ih => ih >>= fun i => g (x, y, i)) (m x)) := by
  have hstep : Computable₂ fun (a : (σ × ℕ) × List ℕ) (yt : ℕ × (ℕ ⊕ (Option β × List ℕ))) =>
      (Sum.elim Sum.inl (fun p => Option.elim p.1 (Sum.inr (none, p.2))
        fun i => play g (((a.1.1, yt.1, i), a.1.2), p.2)) yt.2 : ℕ ⊕ (Option β × List ℕ)) := by
    have hgc : Computable₂ fun (w : (((σ × ℕ) × List ℕ) × (ℕ × (ℕ ⊕ (Option β × List ℕ)))) ×
        (Option β × List ℕ)) (i : β) => play g (((w.1.1.1.1, w.1.2.1, i), w.1.1.1.2), w.2.2) :=
      (hg.comp ((((fst.comp (fst.comp (fst.comp (fst.comp fst)))).pair
          ((fst.comp (snd.comp (fst.comp fst))).pair snd)).pair
          (snd.comp (fst.comp (fst.comp (fst.comp fst))))).pair
          (snd.comp (snd.comp fst)))).to₂
    have hopt : Computable₂ fun (w : ((σ × ℕ) × List ℕ) × (ℕ × (ℕ ⊕ (Option β × List ℕ))))
        (p : Option β × List ℕ) => (Option.elim p.1 (Sum.inr (none, p.2))
          fun i => play g (((w.1.1.1, w.2.1, i), w.1.1.2), p.2) : ℕ ⊕ (Option β × List ℕ)) := by
      unfold Computable₂
      refine (option_casesOn (fst.comp snd)
        (sumInr.comp ((const none).pair (snd.comp snd))) hgc).of_eq fun z => ?_
      rcases z with ⟨w, ⟨_ | _, _⟩⟩ <;> rfl
    unfold Computable₂
    refine (sumCasesOn (snd.comp snd) (sumInl.comp snd).to₂ hopt).of_eq fun z => ?_
    rcases z with ⟨a, y, _ | ⟨_ | _, rs⟩⟩ <;> rfl
  refine (nat_rec (hm.comp (fst.comp fst)) hP hstep).of_eq fun a => ?_
  rcases a with ⟨⟨x, k⟩, rs⟩
  exact (play_natRec P g x k rs (m x)).symm

end Play

end ClockedComp

end Cslib

open Cslib

namespace Nat.RecursiveIn.Code

/-- Compile an oracle code to a clocked program querying the oracle, constructor by constructor:
composition is `bind`, primitive recursion is Lean recursion on the counter, and unbounded search
is `ClockedComp.rfind`. -/
def toClocked : Code → ℕ → ClockedComp natOracleSpec ℕ
  | zero => fun _ => pure 0
  | succ => fun n => pure (n + 1)
  | left => fun n => pure n.unpair.1
  | right => fun n => pure n.unpair.2
  | oracle => fun n => ClockedComp.query n
  | pair cf cg => fun n => do
      let a ← toClocked cf n
      let b ← toClocked cg n
      pure (Nat.pair a b)
  | comp cf cg => fun n => toClocked cg n >>= toClocked cf
  | prec cf cg => Nat.unpaired fun a m =>
      m.rec (toClocked cf a) fun y ih => ih >>= fun i => toClocked cg (Nat.pair a (Nat.pair y i))
  | rfind' cf => Nat.unpaired fun a m =>
      (· + m) <$> ClockedComp.rfind fun i =>
        (fun x => decide (x = 0)) <$> toClocked cf (Nat.pair a (i + m))

private theorem stable_toClocked_and_eval (g : ℕ →. ℕ) :
    ∀ (c : Code) (n : ℕ), ClockedComp.Stable g (c.toClocked n) ∧
      ClockedComp.eval g (c.toClocked n) = c.eval g n
  | zero, n => ⟨.pure _, ClockedComp.eval_pure g 0⟩
  | succ, n => ⟨.pure _, ClockedComp.eval_pure g _⟩
  | left, n => ⟨.pure _, ClockedComp.eval_pure g _⟩
  | right, n => ⟨.pure _, ClockedComp.eval_pure g _⟩
  | oracle, n => ⟨.query n, ClockedComp.eval_query g n⟩
  | pair cf cg, n => by
    obtain ⟨hf, ef⟩ := stable_toClocked_and_eval g cf n
    obtain ⟨hg, eg⟩ := stable_toClocked_and_eval g cg n
    refine ⟨hf.bind fun _ => hg.bind fun _ => .pure _, ?_⟩
    rw [toClocked, ClockedComp.eval_bind g hf fun _ => hg.bind fun _ => .pure _]
    simp only [ClockedComp.eval_bind g hg fun _ => .pure _, ClockedComp.eval_pure g, ef, eg, eval,
      seq_eq_bind_map, map_eq_pure_bind, bind_assoc, pure_bind]
    rfl
  | comp cf cg, n => by
    obtain ⟨hg, eg⟩ := stable_toClocked_and_eval g cg n
    have hf := fun a => stable_toClocked_and_eval g cf a
    refine ⟨hg.bind fun a => (hf a).1, ?_⟩
    simp only [toClocked]
    rw [ClockedComp.eval_bind g hg fun a => (hf a).1, eg, eval]
    simp only [(hf _).2]
    rfl
  | prec cf cg, n => by
    have hf := stable_toClocked_and_eval g cf
    have hg := stable_toClocked_and_eval g cg
    simp only [toClocked, eval, Nat.unpaired]
    induction n.unpair.2 with
    | zero => exact hf _
    | succ m ih =>
      obtain ⟨hs, he⟩ := ih
      refine ⟨hs.bind fun _ => (hg _).1, ?_⟩
      rw [ClockedComp.eval_bind g hs fun _ => (hg _).1, he]
      simp only [(hg _).2]
      rfl
  | rfind' cf, n => by
    have hf := stable_toClocked_and_eval g cf
    simp only [toClocked, eval, Nat.unpaired]
    have hp : ∀ i, ClockedComp.Stable g ((fun x => decide (x = 0)) <$>
        toClocked cf (Nat.pair n.unpair.1 (i + n.unpair.2))) := fun i => (hf _).1.map _
    refine ⟨(ClockedComp.Stable.rfind hp).map _, ?_⟩
    rw [ClockedComp.eval_map g (.rfind hp), ClockedComp.eval_rfind g hp]
    simp only [ClockedComp.eval_map g (hf _).1, (hf _).2]
    rfl

/-- The compiled program of a code is stable against every partial oracle. -/
theorem stable_toClocked (g : ℕ →. ℕ) (c : Code) (n : ℕ) :
    ClockedComp.Stable g (c.toClocked n) :=
  (stable_toClocked_and_eval g c n).1

/-- **Code to program.** The compiled program computes the code relative to every partial
oracle. -/
theorem eval_toClocked (g : ℕ →. ℕ) (c : Code) (n : ℕ) :
    ClockedComp.eval g (c.toClocked n) = c.eval g n :=
  (stable_toClocked_and_eval g c n).2

section Dialogue

open Computable

/-- The compiled program of a code has a computable play. -/
theorem computable_play_toClocked (c : Code) : Computable (ClockedComp.play c.toClocked) := by
  induction c with
  | zero => exact ClockedComp.computable_play_pure (const 0)
  | succ => exact ClockedComp.computable_play_pure (_root_.Primrec.succ).to_comp
  | left => exact ClockedComp.computable_play_pure (fst.comp Computable.unpair)
  | right => exact ClockedComp.computable_play_pure (snd.comp Computable.unpair)
  | oracle => exact ClockedComp.computable_play_query Computable.id
  | pair cf cg ihf ihg =>
    exact ClockedComp.computable_play_bind ihf
      (ClockedComp.computable_play_bind (ClockedComp.computable_play_comp ihg fst)
        (ClockedComp.computable_play_pure
          ((Primrec₂.to_comp Primrec₂.natPair).comp (snd.comp fst) snd)))
  | comp cf cg ihf ihg =>
    exact ClockedComp.computable_play_bind ihg (ClockedComp.computable_play_comp ihf snd)
  | prec cf cg ihf ihg =>
    simpa only [toClocked] using ClockedComp.computable_play_natRec (m := fun n : ℕ => n.unpair.2)
      (P := fun n : ℕ => toClocked cf n.unpair.1)
      (g := fun z : ℕ × ℕ × ℕ => toClocked cg (Nat.pair z.1.unpair.1 (Nat.pair z.2.1 z.2.2)))
      (snd.comp Computable.unpair)
      (ClockedComp.computable_play_comp ihf (fst.comp Computable.unpair))
      (ClockedComp.computable_play_comp ihg
        ((Primrec₂.to_comp Primrec₂.natPair).comp (fst.comp (Computable.unpair.comp fst))
          ((Primrec₂.to_comp Primrec₂.natPair).comp (fst.comp snd) (snd.comp snd))))
  | rfind' cf ihf =>
    have hp := ClockedComp.computable_play_map
      (P := fun z : ℕ × ℕ => toClocked cf (Nat.pair z.1.unpair.1 (z.2 + z.1.unpair.2)))
      (f := fun _ x => decide (x = 0))
      (ClockedComp.computable_play_comp ihf
        ((Primrec₂.to_comp Primrec₂.natPair).comp (fst.comp (Computable.unpair.comp fst))
          ((Primrec₂.to_comp _root_.Primrec.nat_add).comp snd
            (snd.comp (Computable.unpair.comp fst)))))
      (((Primrec₂.to_comp _root_.Primrec.eq.decide).comp snd (const 0)).to₂)
    simpa only [toClocked] using
      ClockedComp.computable_play_map (ClockedComp.computable_play_rfind hp)
        (f := fun (n : ℕ) (r : ℕ) => r + n.unpair.2)
        ((Primrec₂.to_comp _root_.Primrec.nat_add).comp snd
          (snd.comp (Computable.unpair.comp fst))).to₂

/-- The dialogue of the compiled program of a code is computable. -/
theorem computable_dialogue_toClocked (c : Code) :
    Computable (ClockedComp.dialogue c.toClocked) :=
  ClockedComp.computable_dialogue_of_play (computable_play_toClocked c)

/-- **Codes and clocked programs compute the same functions.** Relative to a partial oracle `g`,
a partial function is recursive in `g` if and only if it is computed against `g` by a family of
clocked programs querying `g` whose dialogue is computable. -/
theorem recursiveIn_iff_exists_clockedComp {g : ℕ →. ℕ} {F : ℕ →. ℕ} :
    Nat.RecursiveIn {g} F ↔ ∃ P : ℕ → ClockedComp natOracleSpec ℕ,
      Computable (ClockedComp.dialogue P) ∧ ∀ n, ClockedComp.eval g (P n) = F n := by
  refine ⟨fun h => ?_, fun ⟨P, hP, hF⟩ => (ClockedComp.recursiveIn_eval hP _).of_eq hF⟩
  obtain ⟨c, rfl⟩ := exists_code.1 h
  exact ⟨c.toClocked, computable_dialogue_toClocked c, eval_toClocked g c⟩

end Dialogue

end Nat.RecursiveIn.Code
