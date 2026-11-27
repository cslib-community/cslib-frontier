/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Representation
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Context

/-!
# AVL validity at a linked subtree focus

A linked focus inside a matched valid AVL tree itself matches a valid AVL subtree.
This connects pointer-machine ancestor contexts to the existing AVL invariants.
-/

public section
namespace Cslib.DataStructure.AVLTree.PointerMachine
open Cslib.PointerMachine SearchTree.PointerMachine
variable {M : Model} {extra : ℕ} [LinearOrder M.Value]

/-- Extract the existing valid AVL subtree at a linked focus. The surrounding frames are
proof data; following parent or child links does not require a machine stack. -/
theorem Matches.exists_valid_focus {encode : ℕ → M.Value} {field : Fin (extra + 1)}
    {cs : List (Frame M extra)} {tree : BinaryTree (Label M extra)} {t : AVLTree M.Value}
    (matched : Matches encode field (plug cs tree) t) (valid : t.Valid) :
    ∃ u, Matches encode field tree u ∧ u.Valid := by
  induction cs generalizing tree t with
  | nil => exact ⟨t, matched, valid⟩
  | cons frame cs ih =>
    cases frame with
    | left label sibling =>
      obtain ⟨u, mu, vu⟩ := ih matched valid
      cases u with
      | nil => cases mu
      | node key height l r =>
        obtain ⟨_, _, ml, _⟩ := mu
        obtain ⟨⟨ol, _, _, _⟩, ⟨_, hl, _⟩, ⟨_, _, bl, _⟩⟩ := vu
        exact ⟨l, ml, ol, hl, bl⟩
    | right sibling label =>
      obtain ⟨u, mu, vu⟩ := ih matched valid
      cases u with
      | nil => cases mu
      | node key height l r =>
        obtain ⟨_, _, _, mr⟩ := mu
        obtain ⟨⟨_, ord, _, _⟩, ⟨_, _, hr⟩, ⟨_, _, _, br⟩⟩ := vu
        exact ⟨r, mr, ord, hr, br⟩

end Cslib.DataStructure.AVLTree.PointerMachine
