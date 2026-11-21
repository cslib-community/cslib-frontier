/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.SkipFrame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGameLeaf

open Turing MultiTapeTM MultiTapeATM.WordGameLeaf

-- A false payload bit belongs to the frame, while the terminating false marker advances onto
-- the first flag. The controller's storage, arbitrary output, and all other cursors survive.
example {k : ℕ} {input : List Bool} (i : Fin k) (flags : List Bool)
    (storage : Cfg k Bool Unit input) :
    let tape := frame [false, true] ++ flags
    (SkipFrame.machine i).runFrom (config i (some (SkipFrame.machine i).q₀) tape 0 storage) 5 =
      config i none tape 5 storage := by
  let tape := frame [false, true] ++ flags
  let cfg := config i (none : Option Unit) tape 0 storage
  have h := SkipFrame.runFrom i [false, true] flags cfg
    (by simp [cfg, config, tape]) (by simp [cfg, config])
  have hl : (frame [false, true]).length = 5 := by simp
  simpa only [cfg, config, Cfg.withState, tape, Function.update_idem, hl] using h
