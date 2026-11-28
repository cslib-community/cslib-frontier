/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.BoundaryGroup
public import CslibFrontier.Computability.PolyTime.CSP.BoundaryFusion
public import CslibFrontier.Computability.PolyTime.CSP.BoundaryHiding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Prefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.Tactic.Linarith
import CslibFrontier.Tactic.EncLen

/-!
# Plain native cost of closing one metadata run

The actual run tail clocks the fold. Every reachable body retains the original relation
payload and scope lengths; every name is selected from the original body/ports. After the
first fusion, the literal prefix restriction bounds the whole table independently of raw
entry magnitudes. An internal polynomial envelope covers ALL prefixes, including the raw
initial table. The envelope is a storage bound, not an exact clock. No tidy API is used.
-/

public section

namespace Cslib.Complexity.CSP.CrossInsertion

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph Turing.MultiTapeTM Cslib.BitString

variable {Rel : Type}

/-- Framed State first (binary body names/ports/table), then the framed list of binary
ORIGINAL metadata keys. This is the generic uncurried input, with no layout change. -/
abbrev encStateMetadata (encRel : Rel ↪ List Bool) :=
  encPair (encState encRel) (encList encNat)

private def tasks (p : State Rel × List ℕ) : List ℕ :=
  if p.2.length=p.1.ports.length then
    p.2.takeWhile (fun b => decide (b=p.2.headD 0)) |>.tail else []

private theorem tasks_bound (p : State Rel × List ℕ) :
    (tasks p).length≤p.1.ports.length-1 := by
  unfold tasks
  split
  · have h := (List.takeWhile_sublist (fun b => decide (b=p.2.headD 0)) (l := p.2)).length_le
    simp only [List.length_tail]; omega
  · simp

private theorem fold_resource (I : State Rel) (ts : List ℕ)
    (hlen : ts.length ≤ I.ports.length - 1) :
    let J := ts.foldl (fun J _ => fuseHead J) I
    ∃ f : ℕ → ℕ, J.body=I.body.relabel f ∧ J.ports=(I.ports.drop ts.length).map f ∧
      (∀ z∈I.body.vars++I.ports, f z∈I.body.vars++I.ports) ∧
      (ts=[] → J=I) ∧ (ts≠[] → J.rotation.successor.length=
        2*(I.body.occurrences.length+I.ports.length-ts.length) ∧
        ∀ v∈J.rotation.successor, v<2*(I.body.occurrences.length+I.ports.length-ts.length)) := by
  induction ts using List.reverseRecOn with
  | nil =>
    exact ⟨id, (List.map_id'' (fun c => by cases c; simp [Constraint.relabel]) _).symm, by simp,
      by simp, by simp, by simp⟩
  | append_singleton ts t ih =>
    simp only [List.length_append, List.length_singleton] at hlen
    obtain ⟨f, hb, hp, hn, _, _⟩ := ih (by omega)
    set J := ts.foldl (fun J _ => fuseHead J) I with hJ_def
    have hP : J.ports.length = I.ports.length - ts.length := by simp [hp]
    have htwo : 2 ≤ J.ports.length := by omega
    rcases he : J.ports with _ | ⟨x, _ | ⟨y, ps⟩⟩
    · simp [he] at htwo
    · simp [he] at htwo
    · let u := Function.update id y x
      have hx : x ∈ I.body.vars ++ I.ports := by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (hp ▸ he ▸ List.mem_cons_self)
        exact hn z (List.mem_append_right _ ((List.drop_sublist _ _).subset hz))
      dsimp only
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hJ_def]
      refine ⟨u ∘ f, ?_, ?_, ?_, by simp, ?_⟩
      · simp only [fuseHead, he, hb, CSP.relabel, List.map_map]
        exact List.map_congr_left fun c _ => by
          cases c; simp [Constraint.relabel, Function.comp_def, List.map_map, u]
      · have ht : (y :: ps) = (I.ports.drop ts.length).tail.map f := by
          simpa only [he, List.tail_cons, ← List.map_tail] using congrArg List.tail hp
        simp only [fuseHead, he]
        simp [ht, ← List.drop_one, List.drop_drop, u]
      · intro z hz
        by_cases h : f z = y
        · simpa only [Function.comp_apply, u, Function.update_apply, h, ↓reduceIte] using hx
        · simpa only [Function.comp_apply, u, Function.update_of_ne h, id_eq] using hn z hz
      · intro _
        have hm : J.body.occurrences.length = I.body.occurrences.length := by
          rw [← CSP.vars_length_eq_occurrences, hb, CSP.vars_relabel, List.length_map,
            CSP.vars_length_eq_occurrences]
        have hsize : 2 * (J.body.occurrences.length + (ps.length + 1)) =
            2 * (I.body.occurrences.length + I.ports.length - (ts ++ [t]).length) := by
          simp only [he, List.length_cons] at hP
          simp only [List.length_append, List.length_singleton]; omega
        simp only [fuseHead, he, equalDropCertificate, length_restrictPrefix]
        exact ⟨hsize, fun v hv => (entries_restrictPrefix_lt _ _ v hv).trans_eq hsize⟩


private def scale (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ) : ℕ :=
  (encStateMetadata encRel p).length+
    (encList encNat (p.1.body.vars++p.1.ports)).length+
    p.1.body.length+p.1.body.occurrences.length+p.1.ports.length+1

private theorem scale_poly (encRel : Rel ↪ List Bool) :
    PolyBounded (fun p => (encStateMetadata encRel p).length) (scale encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hb := encState_body_polyTime encRel hi
  have hp := encState_ports_polyTime encRel hi
  have hv := (computableInPolyTime_vars encRel encNat).comp hb
  have hn := ComputableInPolyTime.listAppend' hv hp
  have hQ : PolyBounded (fun p => (encStateMetadata encRel p).length)
      (fun p => p.1.body.length) := by
    simpa only [Function.comp_apply,encUnary_apply,List.length_replicate] using
      ((ComputableInPolyTime.length_list (encConstraint encRel encNat)).comp hb).polyBounded_length
  have hM : PolyBounded (fun p => (encStateMetadata encRel p).length)
      (fun p => p.1.body.occurrences.length) := by
    simpa only [Function.comp_apply,encUnary_apply,List.length_replicate,
      CSP.vars_length_eq_occurrences] using
        ((computableInPolyTime_length_vars encRel encNat).comp hb).polyBounded_length
  have hP : PolyBounded (fun p => (encStateMetadata encRel p).length)
      (fun p => p.1.ports.length) := by
    simpa only [Function.comp_apply,encUnary_apply,List.length_replicate] using
      ((ComputableInPolyTime.length_list encNat).comp hp).polyBounded_length
  exact ((((PolyBounded.self.add hn.polyBounded_length).add hQ).add hM).add hP).add (.const 1)

private theorem prefix_size (encRel : Rel ↪ List Bool) (p : State Rel × List ℕ)
    (ts : List ℕ) (hp : ts <+: tasks p) :
    (encState encRel (ts.foldl (fun J _ => fuseHead J) p.1)).length ≤
      512*(scale encRel p)^3 := by
  let N := scale encRel p
  let I := p.1
  let J := ts.foldl (fun J _ => fuseHead J) I
  have hts : ts.length≤I.ports.length-1 := hp.length_le.trans (tasks_bound p)
  obtain ⟨f,hb,ht,hn,he,hd⟩ := fold_resource I ts hts
  have hS : (encState encRel I).length ≤ N := by enc_len [I, N, scale, encStateMetadata]
  have hN : 1≤N := by dsimp [N,scale]; omega
  by_cases hz : ts=[]
  · rw [he hz]
    exact hS.trans (by nlinarith [Nat.zero_le (N*N*N)])
  · obtain ⟨hD,hV⟩ := hd hz
    have hQ : I.body.length≤N := by dsimp [N,scale,I]; omega
    have hM : I.body.occurrences.length≤N := by dsimp [N,scale,I]; omega
    have hP : I.ports.length≤N := by dsimp [N,scale,I]; omega
    have hnames (z : ℕ) (hz : z∈I.body.vars++I.ports) : (encNat z).length≤N :=
      (SizedListEncoding.length_elem_le (encA := encNat)
        (encL := encList encNat) (I.body.vars++I.ports) z hz).trans (by dsimp [N,scale,I]; omega)
    have hrow : ∀ c∈J.body, (encConstraint encRel encNat c).length≤4*(N+1)^2 := by
      rintro c hc
      obtain ⟨d, hdc, rfl⟩ := List.mem_map.mp (hb ▸ hc)
      have hdc' : (encConstraint encRel encNat d).length≤N := by
        have hbody : (encCSP encRel encNat I.body).length ≤ (encState encRel I).length := by
          enc_len [encState_apply, encStateFields]
        exact (SizedListEncoding.length_elem_le (encA := encConstraint encRel encNat)
          (encL := encCSP encRel encNat) I.body d hdc).trans (hbody.trans hS)
      have hr : (encRel d.rel).length≤N := le_trans (show (encRel d.rel).length≤
        (encConstraint encRel encNat d).length by enc_len [encConstraint_apply]) hdc'
      have hs : d.scope.length≤N := (SizedListEncoding.length_le (encA := encNat)
        (encL := encList encNat) d.scope).trans (le_trans (show (encList encNat d.scope).length≤
          (encConstraint encRel encNat d).length by enc_len [encConstraint_apply]) hdc')
      have hw := length_encList_le encNat (d.scope.map f) fun z hz => by
        obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hz
        exact hnames _ (hn v (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d,hdc,hv'⟩)))
      simp only [List.length_map] at hw
      rw [encConstraint_apply,length_encPair]
      change 2*(encRel d.rel).length+1+(encList encNat (d.scope.map f)).length≤_
      nlinarith [hw.trans (Nat.mul_le_mul_right _ hs)]
    have hq : J.body.length ≤ N := by rwa [hb, CSP.relabel, List.length_map]
    have hb'' := (length_encList_le (encConstraint encRel encNat) J.body hrow).trans
      (Nat.mul_le_mul_right _ hq)
    have hp' : J.ports.length≤N := by rw [ht,List.length_map,List.length_drop]; omega
    have hvp (z : ℕ) (hz : z∈J.ports) : (encNat z).length≤N := by
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (ht ▸ hz)
      exact hnames _ (hn v (List.mem_append_right _ ((List.drop_sublist _ _).subset hv)))
    have hports := (length_encList_le encNat J.ports hvp).trans
      (Nat.mul_le_mul_right _ hp')
    have hd' : J.rotation.successor.length≤4*N := by rw [hD]; omega
    have hv : ∀ v∈J.rotation.successor, (encNat v).length≤4*N := fun v hv => by
      have hval := hV v hv
      simpa only [encNat_apply,Nat.size_eq_bits_len] using (Nat.size_le_self v).trans (by omega)
    have htable := (length_encList_le encNat J.rotation.successor hv).trans
      (Nat.mul_le_mul_right _ hd')
    change (encState encRel J).length≤512*N^3
    simp only [encState_apply,encStateFields,length_encPair,
      Graph.encRotationCertificate_apply,Graph.encRotationCertificateFields]
    nlinarith [Nat.zero_le (N*N*N),Nat.zero_le (N*N)]

/-- Close one actual run in plain polynomial time on EVERY raw State and binary metadata
list. Source list projections and unary counts fund the internal prefix envelope; malformed
initial entries remain data. No validity, arity, name/table bound or runtime provider is used. -/
theorem computableInPolyTime_closeFirstMetadataRun (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : State Rel × List ℕ => closeFirstMetadataRun p.1 p.2)
      (encStateMetadata encRel) (encState encRel) := by
  have hi := ComputableInPolyTime.fst (encState encRel) (encList encNat)
  have hk := ComputableInPolyTime.snd (encState encRel) (encList encNat)
  have hl : ComputableInPolyTime
      (fun p : State Rel × List ℕ => decide (p.2.length=p.1.ports.length))
      (encStateMetadata encRel) encBool := by fun_prop
  have hbad : ComputableInPolyTime
      (fun p : State Rel × List ℕ => decide (p.2.length≠p.1.ports.length))
      (encStateMetadata encRel) encBool := by fun_prop
  have hhead := (ComputableInPolyTime.headD (encA := encNat) 0).comp hk
  have hrun := ComputableInPolyTime.takeWhileWithInput
    (pred := fun p b => decide (b=p.2.headD 0)) hk
    (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _)
      (hhead.comp (ComputableInPolyTime.fst _ _)))
  have ht : ComputableInPolyTime tasks (encStateMetadata encRel) (encList encNat) :=
    ComputableInPolyTime.ite_decide hl
      ((ComputableInPolyTime.tail (encA := encNat)).comp hrun) (ComputableInPolyTime.const [])
  have hstep := (computableInPolyTime_fuseHead encRel).comp
    (ComputableInPolyTime.fst (encState encRel) encNat)
  have hfold := (ComputableInPolyTime.foldl_spec (step := fun J (_ : ℕ) => fuseHead J) ht hi hstep
    (fun p consumed J => J=consumed.foldl (fun J _ => fuseHead J) p.1)
    (fun _ => rfl)
    (fun _ c J _ _ hJ => by simp only [hJ, List.foldl_append, List.foldl_cons, List.foldl_nil])
    ((PolyBounded.const 512).mul ((scale_poly encRel).pow 3))
    (fun p c J hp hJ => hJ ▸ prefix_size encRel p c hp)).1
  have hclosed := (computableInPolyTime_hideHead encRel).comp hfold
  have hempty := (ComputableInPolyTime.listIsEmpty (encA := encNat)).comp hk
  refine (ComputableInPolyTime.ite_decide hbad hi (hempty.ite hi hclosed)).of_enc_eq
    fun ⟨I,keys⟩ => congrArg (encState encRel) ?_
  by_cases h : keys.length=I.ports.length
  · cases keys <;> simp [closeFirstMetadataRun,tasks,h]
    rfl
  · simp [closeFirstMetadataRun,h]

end Cslib.Complexity.CSP.CrossInsertion
