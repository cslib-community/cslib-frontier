/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationGerms
public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitOrder
import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters

/-!
# Local relocation of an actual embedded vertex

`relocateVertex` keeps the graph and indexed edge occurrences. Its nonincident routes are
literal originals; incident routes retain their exterior and receive one spoke per incident
end. `IsEmbedding.exists_vertex_relocation_radius` chooses the restriction radius internally
and preserves embedding and literal clockwise order for every new center in its open ball.

This is original finite PL geometry. It supplies neither global frozen placement nor an
ambient transport, edge-vertex parity move, HT or query sufficiency. These remain open in
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

private theorem relocatedRoute_endpoint {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (a : ℂ) (e : Fin G.edges.length) (b : Bool) :
    (if Dart.vertex (e, false) ≠ v ∧ Dart.vertex (e, true) ≠ v then D.route e else
    restoreLast v v (Dart.vertex (e, true)) a a
      (restoreFirst v v (Dart.vertex (e, false)) a a (D.outsideRoute v ρ e))).endpoint b =
      Function.update D.vertex v a (Dart.vertex (e, b)) := by
  by_cases h : Dart.vertex (e, false) ≠ v ∧ Dart.vertex (e, true) ≠ v
  · rw [ite_eq_left h, D.endpoint_eq]
    cases b
    · exact (Function.update_of_ne h.1 a D.vertex).symm
    · exact (Function.update_of_ne h.2 a D.vertex).symm
  · rw [ite_eq_right h]
    have hfirst (p : Route) :
        (restoreFirst v v (Dart.vertex (e, false)) a a p).start =
          if Dart.vertex (e, false) = v then a else p.start := by
      by_cases he : Dart.vertex (e, false) = v
      · simpa only [restoreFirst, he, Route.endpoint, Bool.false_eq_true, ↓reduceIte] using
          Route.endpoint_prepend a p false
      · simp only [restoreFirst, he, ↓reduceIte]
    have hlast (p : Route) :
        (restoreFirst v v (Dart.vertex (e, false)) a a p).finish = p.finish :=
      endpoint_restoreFirst v v (Dart.vertex (e, false)) a a p true
    cases b
    · rw [endpoint_restoreLast]
      change (restoreFirst v v (Dart.vertex (e, false)) a a
        (D.outsideRoute v ρ e)).start = _
      rw [hfirst]
      by_cases he : Dart.vertex (e, false) = v
      · simp [he]
      · rw [ite_eq_right he, Function.update_of_ne he]
        simpa only [ite_eq_right he, Route.endpoint, Bool.false_eq_true, ↓reduceIte] using
          D.endpoint_outsideRoute v ρ e false
    · rw [endpoint_restoreLast]
      simp only [↓reduceIte, hlast]
      by_cases he : Dart.vertex (e, true) = v
      · simp [he]
      · rw [ite_eq_right he, Function.update_of_ne he]
        simpa only [ite_eq_right he, Route.endpoint, ↓reduceIte] using
          D.endpoint_outsideRoute v ρ e true

/-- Move one named vertex, keeping every nonincident route literally unchanged. Incident
routes keep the actual cut exterior and get a spoke at EACH incident end, including loops.
The constructor has no geometric validity premise; its preservation theorem chooses the radius. -/
@[expose] noncomputable def relocateVertex {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (a : ℂ) : PolygonalDrawing G where
  vertex := Function.update D.vertex v a
  route := fun e => if Dart.vertex (e, false) ≠ v ∧ Dart.vertex (e, true) ≠ v then D.route e else
    restoreLast v v (Dart.vertex (e, true)) a a
      (restoreFirst v v (Dart.vertex (e, false)) a a (D.outsideRoute v ρ e))
  endpoint_eq := by exact relocatedRoute_endpoint D v ρ a

private noncomputable abbrev relocatedRoute {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (a : ℂ) (e : Fin G.edges.length) : Route :=
  (D.relocateVertex v ρ a).route e

private theorem outsideRoute_unaffected {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (e : Fin G.edges.length)
    (h₀ : Dart.vertex (e, false) ≠ v) (h₁ : Dart.vertex (e, true) ≠ v) :
    D.outsideRoute v ρ e = D.route e := by
  simp only [outsideRoute, restrictionTime, ite_eq_right h₀, ite_eq_right h₁]
  cases hp : D.route e with
  | mk n point =>
    change Route.mk n _ = Route.mk n point
    congr 1
    funext i
    by_cases hz : i.val = 0
    · have hi : i = 0 := Fin.ext hz
      subst i
      simp [Route.eval]
    · by_cases hl : i.val = n + 1
      · have hi : i = Fin.last (n + 1) := Fin.ext hl
        subst i
        simp [Route.eval, Route.segments]
      · simp [hz, hl, Route.segments]

private theorem relocatedRoute_attachments {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (a : ℂ) (e : Fin G.edges.length) :
    relocatedRoute D v ρ a e =
      restoreLast v v (Dart.vertex (e, true)) a a
        (restoreFirst v v (Dart.vertex (e, false)) a a (D.outsideRoute v ρ e)) := by
  change (if _ then _ else _) = _
  split_ifs with h
  · rw [outsideRoute_unaffected D v ρ e h.1 h.2]
    simp only [restoreFirst, restoreLast, ite_eq_right h.1, ite_eq_right h.2]
  · rfl

-- This actual-constructor classification records only the position bridges needed below.
-- The ALL-real segment split itself is the existing attachment API.
private theorem relocated_cases {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (a : ℂ) (e : Fin G.edges.length)
    (i : Fin (relocatedRoute D v ρ a e).segments) (t : ℝ) :
    (∃ j : Fin (D.outsideRoute v ρ e).segments,
      (relocatedRoute D v ρ a e).eval i t = (D.outsideRoute v ρ e).eval j t ∧
      (relocatedRoute D v ρ a e).position i t =
        (attachmentCount v v (Dart.vertex (e, false)) : ℝ) +
          (D.outsideRoute v ρ e).position j t) ∨
    (∃ b : Bool, Dart.vertex (e, b) = v ∧
      (relocatedRoute D v ρ a e).eval i t =
        AffineMap.lineMap a (D.cutPort ρ (e, b)) (Route.endTime b t) ∧
      (Route.endTime b t = 0 → (relocatedRoute D v ρ a e).AtEnd i t b)) := by
  let p := D.outsideRoute v ρ e
  have hp₀ := D.endpoint_outsideRoute v ρ e false
  have hp₁ := D.endpoint_outsideRoute v ρ e true
  have hroute := relocatedRoute_attachments D v ρ a e
  revert i
  generalize hq : relocatedRoute D v ρ a e = q
  have hq' := hq.symm.trans hroute
  clear hq hroute
  by_cases h₀ : Dart.vertex (e, false) = v <;>
    by_cases h₁ : Dart.vertex (e, true) = v
  · simp only [restoreFirst, restoreLast, h₀, h₁, ↓reduceIte] at hq'
    subst q
    intro i
    rcases Route.attach_eval_cases a p a i t with ⟨j, heq, hpos⟩ | ⟨heq, hpos⟩ | ⟨heq, hpos⟩
    · exact Or.inl ⟨j, heq, by simpa [attachmentCount, or_self, h₀] using hpos⟩
    · refine Or.inr ⟨false, h₀, ?_, ?_⟩
      · simpa only [Route.endpoint, Route.endTime, Bool.false_eq_true, h₀, ↓reduceIte] using
          heq.trans
          (congrArg (fun z => AffineMap.lineMap a z t) hp₀)
      · intro ht
        change t = 0 at ht
        simpa [Route.AtEnd, ht] using hpos
    · refine Or.inr ⟨true, h₁, ?_, ?_⟩
      · simp only [Route.endTime, ↓reduceIte]
        rw [AffineMap.lineMap_apply_one_sub]
        simpa only [Route.endpoint, h₁, ↓reduceIte] using heq.trans
          (congrArg (fun z => AffineMap.lineMap z a t) hp₁)
      · intro ht
        have ht1 : t = 1 := by change 1 - t = 0 at ht; linarith
        norm_num [p, Route.AtEnd, Route.segments, ht1, Nat.cast_add] at hpos ⊢
        linarith
  · simp only [restoreFirst, restoreLast, h₀, h₁, ↓reduceIte] at hq'
    subst q
    intro i
    rcases Route.prepend_eval_cases a p i t with ⟨j, heq, hpos⟩ | ⟨heq, hpos⟩
    · exact Or.inl ⟨j, heq, by simpa [attachmentCount, or_self, h₀] using hpos⟩
    · refine Or.inr ⟨false, h₀, ?_, ?_⟩
      · simpa only [Route.endpoint, Route.endTime, Bool.false_eq_true, h₀, ↓reduceIte] using
          heq.trans
          (congrArg (fun z => AffineMap.lineMap a z t) hp₀)
      · intro ht
        change t = 0 at ht
        simpa [Route.AtEnd, ht] using hpos
  · simp only [restoreFirst, restoreLast, h₀, h₁, ↓reduceIte] at hq'
    subst q
    intro i
    rcases Route.append_eval_cases p a i t with ⟨j, heq, hpos⟩ | ⟨heq, hpos⟩
    · exact Or.inl ⟨j, heq, by simpa [attachmentCount, or_self, h₀] using hpos⟩
    · refine Or.inr ⟨true, h₁, ?_, ?_⟩
      · simp only [Route.endTime, ↓reduceIte]
        rw [AffineMap.lineMap_apply_one_sub]
        simpa only [Route.endpoint, h₁, ↓reduceIte] using heq.trans
          (congrArg (fun z => AffineMap.lineMap z a t) hp₁)
      · intro ht
        have ht1 : t = 1 := by change 1 - t = 0 at ht; linarith
        simpa [Route.AtEnd, Route.segments, ht1, Nat.cast_add] using hpos
  · simp only [restoreFirst, restoreLast, h₀, h₁, ↓reduceIte] at hq'
    subst q
    intro i
    exact Or.inl ⟨i, rfl, by simp [attachmentCount, or_self, h₀]⟩

private theorem relocated_outside_end {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (a : ℂ) (e : Fin G.edges.length)
    (i : Fin (relocatedRoute D v ρ a e).segments)
    (j : Fin (D.outsideRoute v ρ e).segments) (t : ℝ) (b : Bool)
    (hpos : (relocatedRoute D v ρ a e).position i t =
      (attachmentCount v v (Dart.vertex (e, false)) : ℝ) +
          (D.outsideRoute v ρ e).position j t)
    (hat : (D.outsideRoute v ρ e).AtEnd j t b) (hinactive : Dart.vertex (e, b) ≠ v) :
    (relocatedRoute D v ρ a e).AtEnd i t b := by
  have hn : (relocatedRoute D v ρ a e).segments =
      (D.outsideRoute v ρ e).segments + attachmentCount v v (Dart.vertex (e, false)) +
        (if Dart.vertex (e, true) = v then 1 else 0) := by
    rw [relocatedRoute_attachments, segments_restoreLast, segments_restoreFirst]
    simp only [attachmentCount, or_self]
  cases b
  · change (D.outsideRoute v ρ e).position j t = 0 at hat
    change (relocatedRoute D v ρ a e).position i t = 0
    simpa only [attachmentCount, or_self, ite_eq_right hinactive, Nat.cast_zero,
      zero_add, hat] using hpos
  · change (D.outsideRoute v ρ e).position j t =
      ((D.outsideRoute v ρ e).segments : ℝ) at hat
    change (relocatedRoute D v ρ a e).position i t = _
    rw [hn, ite_eq_right hinactive, Nat.add_zero, Nat.cast_add]
    rw [hpos, hat, add_comm]
    simp only [↓reduceIte]

private theorem relocated_simple {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ b, (D.outsideRoute v ρ e).AtEnd i t b ∧ Dart.vertex (e, b) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, b))
    (hsimple : ∀ e, (D.outsideRoute v ρ e).IsSimple)
    {a : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (e : Fin G.edges.length) :
    (relocatedRoute D v ρ a e).IsSimple := by
  by_cases h₀ : Dart.vertex (e, false) = v <;>
    by_cases h₁ : Dart.vertex (e, true) = v
  · rw [relocatedRoute_attachments]
    simp only [restoreLast, restoreFirst, ite_eq_left h₀, ite_eq_left h₁]
    apply hD.attach_outsideRoute_simple v hρ hcut ha ha e h₀ h₁ (hsimple e)
    intro s t hs ht heq
    apply fan_contact ha _ _ _ hs ht heq
    · rw [Metric.mem_sphere]; simpa only [h₀] using hD.dist_cutPort hρ.le (e, false)
    · rw [Metric.mem_sphere]; simpa only [h₁] using hD.dist_cutPort hρ.le (e, true)
    · intro heq
      have hd := hD.cutPort_injective hρ (e, false) (e, true) (h₀.trans h₁.symm) heq
      exact Bool.false_ne_true (congrArg Prod.snd hd)
  · rw [relocatedRoute_attachments]
    simp only [restoreLast, restoreFirst, ite_eq_left h₀, ite_eq_right h₁]
    exact hD.prepend_outsideRoute_simple v hρ hcut ha e h₀ (hsimple e)
  · rw [relocatedRoute_attachments]
    simp only [restoreLast, restoreFirst, ite_eq_right h₀, ite_eq_left h₁]
    exact hD.append_outsideRoute_simple v hρ hcut ha e h₁ (hsimple e)
  · have hn : Dart.vertex (e, false) ≠ v ∧ Dart.vertex (e, true) ≠ v := ⟨h₀, h₁⟩
    simpa only [relocatedRoute, relocateVertex, ite_eq_left hn] using hD.simple e

private theorem relocated_active_germ {G : Graph} (D : PolygonalDrawing G)
    (v : ℕ) (ρ : ℝ) (a : ℂ) (d : Dart G) (hd : d.vertex = v) :
    (D.relocateVertex v ρ a).germ d = D.cutPort ρ d - a := by
  rcases d with ⟨e, b⟩
  change (relocatedRoute D v ρ a e).germ b = _
  rw [relocatedRoute_attachments]
  have hp := D.endpoint_outsideRoute v ρ e b
  rw [ite_eq_left hd] at hp
  cases b
  · rw [germ_restoreLast_false]
    simp only [restoreFirst, ite_eq_left hd, Route.germ_prepend, Bool.false_eq_true, ↓reduceIte]
    simpa only [Route.endpoint, Bool.false_eq_true, ↓reduceIte] using
      congrArg (fun z => z - a) hp
  · simp only [restoreLast, ite_eq_left hd, Route.germ_append, ↓reduceIte]
    have hf := endpoint_restoreFirst v v (Dart.vertex (e, false)) a a
      (D.outsideRoute v ρ e) true
    simp only [Route.endpoint, ↓reduceIte] at hf hp
    rw [hf, hp]

private theorem relocated_inactive_germ {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (a : ℂ) (d : Dart G) (hd : d.vertex ≠ v) :
    ∃ c : ℝ, 0 < c ∧ (D.relocateVertex v ρ a).germ d = c • D.germ d := by
  rcases d with ⟨e, b⟩
  obtain ⟨h₀, h₁, hsum⟩ := hD.restrictionTime_bounds v hρ hlen e
  let s := D.restrictionTime v ρ (e, false)
  let t := D.restrictionTime v ρ (e, true)
  refine ⟨(D.route e).cutUpper t ((D.route e).endSegment b) -
    (D.route e).cutLower s ((D.route e).endSegment b),
    sub_pos.mpr ((D.route e).cut_bounds h₀ h₁ hsum _).2.1, ?_⟩
  change (relocatedRoute D v ρ a e).germ b = _
  rw [relocatedRoute_attachments]
  have hg : (restoreLast v v (Dart.vertex (e, true)) a a
      (restoreFirst v v (Dart.vertex (e, false)) a a (D.outsideRoute v ρ e))).germ b =
      (D.outsideRoute v ρ e).germ b := by
    cases b
    · rw [germ_restoreLast_false, restoreFirst_eq_self v v _ (by simpa only [or_self] using hd)]
    · rw [restoreLast_eq_self v v _ (by simpa only [or_self] using hd), germ_restoreFirst_true]
  rw [hg]
  exact (D.route e).germ_cutEnds s t b

private theorem outside_contact_inactive {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (e f : Fin G.edges.length) (hef : e ≠ f)
    (i : Fin (D.outsideRoute v ρ e).segments) (j : Fin (D.outsideRoute v ρ f).segments)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : (D.outsideRoute v ρ e).eval i s = (D.outsideRoute v ρ f).eval j t) :
    ∃ b c, (D.outsideRoute v ρ e).AtEnd i s b ∧
      (D.outsideRoute v ρ f).AtEnd j t c ∧ Dart.vertex (e, b) = Dart.vertex (f, c) ∧
      Dart.vertex (e, b) ≠ v ∧ Dart.vertex (f, c) ≠ v := by
  obtain ⟨b, c, hb, hc, hv⟩ := hD.outsideRoute_edge_contacts v hρ hlen e f hef i j hs ht heq
  have hne : Dart.vertex (e, b) ≠ v := by
    intro hactive
    have hactive' : Dart.vertex (f, c) = v := hv.symm.trans hactive
    have he := (D.outsideRoute v ρ e).at_eq_endpoint i hs b hb
    have hf := (D.outsideRoute v ρ f).at_eq_endpoint j ht c hc
    rw [D.endpoint_outsideRoute, ite_eq_left hactive] at he
    rw [D.endpoint_outsideRoute, ite_eq_left hactive'] at hf
    have hports := hD.cutPort_injective hρ (e, b) (f, c) hv
      (he.symm.trans (heq.trans hf))
    exact hef (congrArg Prod.fst hports)
  exact ⟨b, c, hb, hc, hv, hne, fun h => hne (hv.trans h)⟩

private theorem relocated_edge_contacts {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ b, (D.outsideRoute v ρ e).AtEnd i t b ∧ Dart.vertex (e, b) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, b))
    {a : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ)
    (e f : Fin G.edges.length) (hef : e ≠ f)
    (i : Fin (relocatedRoute D v ρ a e).segments)
    (j : Fin (relocatedRoute D v ρ a f).segments) (s t : ℝ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : (relocatedRoute D v ρ a e).eval i s = (relocatedRoute D v ρ a f).eval j t) :
    ∃ b c, (relocatedRoute D v ρ a e).AtEnd i s b ∧
      (relocatedRoute D v ρ a f).AtEnd j t c ∧ Dart.vertex (e, b) = Dart.vertex (f, c) := by
  rcases relocated_cases D v ρ a e i s with ⟨k, hek, hpos⟩ | ⟨b, hb, heb, hat⟩ <;>
    rcases relocated_cases D v ρ a f j t with ⟨l, hfl, hpos'⟩ | ⟨c, hc, hfc, hat'⟩
  · obtain ⟨b, c, hb, hc, hv, hbi, hci⟩ := outside_contact_inactive hD v hρ hlen
      e f hef k l s t hs ht (hek.symm.trans (heq.trans hfl))
    exact ⟨b, c, relocated_outside_end D v ρ a e i k s b hpos hb hbi,
      relocated_outside_end D v ρ a f j l t c hpos' hc hci, hv⟩
  · obtain ⟨_, b, hmatch, _⟩ := hD.spoke_outsideRoute_contact v hρ hcut ha
      (f, c) hc e k (Route.endTime_mem c ht) hs (hfc.symm.trans (heq.symm.trans hek))
    exact False.elim (hef (congrArg Prod.fst hmatch).symm)
  · obtain ⟨_, c, hmatch, _⟩ := hD.spoke_outsideRoute_contact v hρ hcut ha
      (e, b) hb f l (Route.endTime_mem b hs) ht (heb.symm.trans (heq.trans hfl))
    exact False.elim (hef (congrArg Prod.fst hmatch))
  · have hports : D.cutPort ρ (e, b) ≠ D.cutPort ρ (f, c) := by
      intro h
      exact hef (congrArg Prod.fst (hD.cutPort_injective hρ (e, b) (f, c)
        (hb.trans hc.symm) h))
    have hsphere (d : Dart G) (hd : d.vertex = v) :
        D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
      rw [Metric.mem_sphere]; simpa only [hd] using hD.dist_cutPort hρ.le d
    obtain ⟨hs0, ht0⟩ := fan_contact ha (hsphere (e, b) hb) (hsphere (f, c) hc)
      hports (Route.endTime_mem b hs) (Route.endTime_mem c ht)
      (heb.symm.trans (heq.trans hfc))
    exact ⟨b, c, hat hs0, hat' ht0, hb.trans hc.symm⟩

private theorem relocated_vertex_contacts {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart G, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (hpoints : ∀ w ∈ G.vertices, D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ b, (D.outsideRoute v ρ e).AtEnd i t b ∧ Dart.vertex (e, b) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, b))
    {a : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ)
    (e : Fin G.edges.length) (i : Fin (relocatedRoute D v ρ a e).segments)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) (w : ℕ) (hw : w ∈ G.vertices)
    (heq : (relocatedRoute D v ρ a e).eval i t = Function.update D.vertex v a w) :
    ∃ b, (relocatedRoute D v ρ a e).AtEnd i t b ∧ Dart.vertex (e, b) = w := by
  rcases relocated_cases D v ρ a e i t with ⟨j, hej, hpos⟩ | ⟨b, hb, heb, hat⟩
  · have hwv : w ≠ v := by
      intro h; subst w
      rw [Function.update_self] at heq
      exact hD.outsideRoute_not_mem_ball v hρ hcut e j ht
        ((hej.symm.trans heq).symm ▸ ha)
    rw [Function.update_of_ne hwv] at heq
    obtain ⟨b, hat, hv⟩ := hD.outsideRoute_vertex_contacts v hρ hlen e j ht w hw
      (hej.symm.trans heq)
    exact ⟨b, relocated_outside_end D v ρ a e i j t b hpos hat
      (fun h => hwv (hv.symm.trans h)), hv⟩
  · have hsphere : D.cutPort ρ (e, b) ∈ Metric.sphere (D.vertex v) ρ := by
      rw [Metric.mem_sphere]; simpa only [hb] using hD.dist_cutPort hρ.le (e, b)
    have heval := heb.symm.trans heq
    have hwv : w = v := by
      by_contra hne
      rw [Function.update_of_ne hne] at heval
      apply hne
      apply hpoints w hw
      exact heval ▸ (convex_closedBall (D.vertex v) ρ).lineMap_mem
        (Metric.ball_subset_closedBall ha) (Metric.sphere_subset_closedBall hsphere)
        (Route.endTime_mem b ht)
    subst w
    rw [Function.update_self] at heval
    have hne : a ≠ D.cutPort ρ (e, b) := by
      intro h
      exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hsphere (h ▸ ha)
    have ht0 := AffineMap.lineMap_injective ℝ hne
      (heval.trans (AffineMap.lineMap_apply_zero a (D.cutPort ρ (e, b))).symm)
    exact ⟨b, hat ht0, hb⟩

/-- Every interior relocation in an internally chosen ball is an embedding on the SAME
indexed graph. Moved germs are the actual new spokes, inactive germs change only by a positive
real factor, and the literal clockwise order of every distinct same-vertex triple is preserved.
This is local relocation, not global frozen placement, an ambient extension or a parity move. -/
theorem IsEmbedding.exists_vertex_relocation_radius {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.vertices) :
    ∃ ρ > 0, ∀ a ∈ Metric.ball (D.vertex v) ρ,
      (D.relocateVertex v ρ a).IsEmbedding ∧
      (∀ d : Dart G, d.vertex = v →
        (D.relocateVertex v ρ a).germ d = D.cutPort ρ d - a) ∧
      (∀ d : Dart G, d.vertex ≠ v → ∃ c : ℝ, 0 < c ∧
        (D.relocateVertex v ρ a).germ d = c • D.germ d) ∧
      (∀ x y z : Dart G, x.vertex = y.vertex → y.vertex = z.vertex →
        x ≠ y → y ≠ z → x ≠ z →
        (sbtw ((D.relocateVertex v ρ a).direction z)
          ((D.relocateVertex v ρ a).direction y) ((D.relocateVertex v ρ a).direction x) ↔
          sbtw (D.direction z) (D.direction y) (D.direction x))) := by
  obtain ⟨ρ, hρ, hpoints, hlocal, hlen⟩ := hD.exists_restriction_radius v hv
  have hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ b, (D.outsideRoute v ρ e).AtEnd i t b ∧ Dart.vertex (e, b) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, b) := by
    intro e i t ht hz
    exact hD.outsideRoute_ball_contact v hρ hlen hlocal e i ht hz
  refine ⟨ρ, hρ, fun a ha => ?_⟩
  have hemb : (D.relocateVertex v ρ a).IsEmbedding := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx y hy heq
      change Function.update D.vertex v a x = Function.update D.vertex v a y at heq
      have hnot (w : ℕ) (hw : w ∈ G.vertices) (hne : w ≠ v) : D.vertex w ≠ a := by
        intro h
        exact hne (hpoints w hw (h.symm ▸ Metric.ball_subset_closedBall ha))
      by_cases hxv : x = v <;> by_cases hyv : y = v
      · exact hxv.trans hyv.symm
      · subst x
        rw [Function.update_self, Function.update_of_ne hyv] at heq
        exact False.elim (hnot y hy hyv heq.symm)
      · subst y
        rw [Function.update_self, Function.update_of_ne hxv] at heq
        exact False.elim (hnot x hx hxv heq)
      · rw [Function.update_of_ne hxv, Function.update_of_ne hyv] at heq
        exact hD.vertices_injective hx hy heq
    · exact relocated_simple hD v hρ hcut (fun e => hD.outsideRoute_simple v hρ hlen e) ha
    · exact relocated_vertex_contacts hD v hρ hlen hpoints hcut ha
    · exact relocated_edge_contacts hD v hρ hlen hcut ha
  refine ⟨hemb, relocated_active_germ D v ρ a, relocated_inactive_germ hD v hρ hlen a, ?_⟩
  intro x y z hxy hyz hnxy hnyz hnxz
  by_cases hx : x.vertex = v
  · have hy : y.vertex = v := hxy.symm.trans hx
    have hz : z.vertex = v := hyz.symm.trans hy
    have hsphere (d : Dart G) (hd : d.vertex = v) :
        D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
      rw [Metric.mem_sphere]; simpa only [hd] using hD.dist_cutPort hρ.le d
    have hports (d e : Dart G) (hde : d.vertex = e.vertex) (hne : d ≠ e) :
        D.cutPort ρ d ≠ D.cutPort ρ e :=
      fun h => hne (hD.cutPort_injective hρ d e hde h)
    have horder := sbtw_arg_sub_iff_of_mem_ball ha (Metric.mem_ball_self hρ)
      (hsphere z hz) (hsphere y hy) (hsphere x hx)
      (hports z y hyz.symm hnyz.symm) (hports y x hxy.symm hnxy.symm)
      (hports z x (hxy.trans hyz).symm hnxz.symm)
    have hnew (d : Dart G) (hd : d.vertex = v) :
        (D.relocateVertex v ρ a).direction d = ((D.cutPort ρ d - a).arg : Real.Angle) := by
      rw [direction, relocated_active_germ D v ρ a d hd]
    have hold (d : Dart G) (hd : d.vertex = v) :
        ((D.cutPort ρ d - D.vertex v).arg : Real.Angle) = D.direction d := by
      rw [← hd, D.arg_cutPort_sub hρ d (hD.germ_ne_zero d)]
      rfl
    simpa only [hnew z hz, hnew y hy, hnew x hx, hold z hz, hold y hy, hold x hx] using horder
  · have hy : y.vertex ≠ v := fun h => hx (hxy.trans h)
    have hz : z.vertex ≠ v := fun h => hy (hyz.trans h)
    have hdir (d : Dart G) (hd : d.vertex ≠ v) :
        (D.relocateVertex v ρ a).direction d = D.direction d := by
      obtain ⟨c, hc, hg⟩ := relocated_inactive_germ hD v hρ hlen a d hd
      simp only [direction, hg, Complex.real_smul, Complex.arg_real_mul _ hc]
    rw [hdir x hx, hdir y hy, hdir z hz]

end Cslib.Complexity.Graph.PolygonalDrawing
