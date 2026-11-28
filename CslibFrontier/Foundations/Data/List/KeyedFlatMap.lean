/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib Data/List)

public import CslibFrontier.Init

/-!
# Selecting a unique keyed block in a flat map

Scanning a list for a unique key and returning that entry's block reads exactly the selected
entry. Values and blocks may repeat; only keys must be distinct.
-/

public section

namespace List

/-- A keyed block scan reads the selected entry exactly when the list has distinct keys. -/
theorem flatMap_ite_key_eq {α β ι : Type*} [DecidableEq ι]
    (l : List α) (key : α → ι) (f : α → List β) (hn : (l.map key).Nodup)
    {a : α} (ha : a ∈ l) :
    (l.flatMap fun b => if key b = key a then f b else []) = f a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [List.flatMap_cons, ite_eq_left rfl, List.flatMap_eq_nil_iff.mpr fun b hb =>
        ite_eq_right fun he => hnd.1 (List.mem_map.mpr ⟨b, hb, he⟩), List.append_nil]
    · rw [List.flatMap_cons,
        ite_eq_right fun he => hnd.1 (List.mem_map.mpr ⟨a, ha, he.symm⟩), List.nil_append]
      exact ih hnd.2 ha

end List
