/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertChecker
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData0
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData1
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData2
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData3
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData4
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData5
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData6
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.PairBound.CertData7

/-!
# Top-level certificate assembly for `rootBoxI`

Combines the eight independent certificate shards `CertData0`..`CertData7`
into a single top-level witness discharging `rootBoxI`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.PairBound.Cert.rootBoxI_certified`:
  `rootBoxI` is discharged into `Certified2` sub-boxes.
-/

public section

namespace Cslib.Circuits.Frontier.Gaussian.PairBound.Cert

private def topSubs : SubTree :=
  .node 21
  (.node 10
  (.node 5
  (.node 2
  (.node 1
  (.leaf 0 midBox3b0)
  (.leaf 1 midBox7b0))
  (.node 3
  (.leaf 2 midBox7b1)
  (.node 4
  (.leaf 3 midBox5b0)
  (.leaf 4 midBox4b0))))
  (.node 7
  (.node 6
  (.leaf 5 midBox2b0)
  (.leaf 6 midBox4b1))
  (.node 8
  (.leaf 7 midBox7b2)
  (.node 9
  (.leaf 8 midBox2b1)
  (.leaf 9 midBox2b2)))))
  (.node 15
  (.node 12
  (.node 11
  (.leaf 10 midBox4b2)
  (.leaf 11 midBox0b0))
  (.node 13
  (.leaf 12 midBox1b0)
  (.node 14
  (.leaf 13 midBox7b3)
  (.leaf 14 midBox6b0))))
  (.node 18
  (.node 16
  (.leaf 15 midBox6b1)
  (.node 17
  (.leaf 16 midBox0b1)
  (.leaf 17 midBox1b1)))
  (.node 19
  (.leaf 18 midBox4b3)
  (.node 20
  (.leaf 19 midBox3b1)
  (.leaf 20 midBox6b2))))))
  (.node 32
  (.node 26
  (.node 23
  (.node 22
  (.leaf 21 midBox5b1)
  (.leaf 22 midBox1b2))
  (.node 24
  (.leaf 23 midBox4b4)
  (.node 25
  (.leaf 24 midBox0b2)
  (.leaf 25 midBox0b3))))
  (.node 29
  (.node 27
  (.leaf 26 midBox5b2)
  (.node 28
  (.leaf 27 midBox2b3)
  (.leaf 28 midBox1b3)))
  (.node 30
  (.leaf 29 midBox2b4)
  (.node 31
  (.leaf 30 midBox7b4)
  (.leaf 31 midBox3b2)))))
  (.node 37
  (.node 34
  (.node 33
  (.leaf 32 midBox3b3)
  (.leaf 33 midBox2b5))
  (.node 35
  (.leaf 34 midBox6b3)
  (.node 36
  (.leaf 35 midBox3b4)
  (.leaf 36 midBox3b5))))
  (.node 40
  (.node 38
  (.leaf 37 midBox2b6)
  (.node 39
  (.leaf 38 midBox5b3)
  (.leaf 39 midBox1b4)))
  (.node 41
  (.leaf 40 midBox7b5)
  (.node 42
  (.leaf 41 midBox1b5)
  (.leaf 42 midBox7b6))))))

private theorem topSubs_ok : SubTreeAll Certified2 topSubs :=
  ⟨⟨⟨⟨⟨midCert_3_0,
  midCert_7_0⟩,
  ⟨midCert_7_1,
  ⟨midCert_5_0,
  midCert_4_0⟩⟩⟩,
  ⟨⟨midCert_2_0,
  midCert_4_1⟩,
  ⟨midCert_7_2,
  ⟨midCert_2_1,
  midCert_2_2⟩⟩⟩⟩,
  ⟨⟨⟨midCert_4_2,
  midCert_0_0⟩,
  ⟨midCert_1_0,
  ⟨midCert_7_3,
  midCert_6_0⟩⟩⟩,
  ⟨⟨midCert_6_1,
  ⟨midCert_0_1,
  midCert_1_1⟩⟩,
  ⟨midCert_4_3,
  ⟨midCert_3_1,
  midCert_6_2⟩⟩⟩⟩⟩,
  ⟨⟨⟨⟨midCert_5_1,
  midCert_1_2⟩,
  ⟨midCert_4_4,
  ⟨midCert_0_2,
  midCert_0_3⟩⟩⟩,
  ⟨⟨midCert_5_2,
  ⟨midCert_2_3,
  midCert_1_3⟩⟩,
  ⟨midCert_2_4,
  ⟨midCert_7_4,
  midCert_3_2⟩⟩⟩⟩,
  ⟨⟨⟨midCert_3_3,
  midCert_2_5⟩,
  ⟨midCert_6_3,
  ⟨midCert_3_4,
  midCert_3_5⟩⟩⟩,
  ⟨⟨midCert_2_6,
  ⟨midCert_5_3,
  midCert_1_4⟩⟩,
  ⟨midCert_7_5,
  ⟨midCert_1_5,
  midCert_7_6⟩⟩⟩⟩⟩⟩

private def topProg : Prog :=
  .seq (.seq (.seq (.seq (.seq (.seq (.step (.split 2 89999000))
  (.seq (.step .clamp)
  (.step (.split 2 84998500))))
  (.seq (.seq (.step .clamp)
  (.step (.split 3 5000500)))
  (.seq (.step .clamp)
  (.step (.split 4 5000500)))))
  (.seq (.seq (.seq (.step .clamp)
  (.step (.split 0 97140000)))
  (.seq (.step .clamp)
  (.step (.split 1 97140000))))
  (.seq (.seq (.step .clamp)
  (.step (.split 2 82498250)))
  (.seq (.step (.subbox 0))
  (.step .clamp)))))
  (.seq (.seq (.seq (.step (.split 3 2500250))
  (.seq (.step .clamp)
  (.step (.split 4 2500250))))
  (.seq (.seq (.step .clamp)
  (.step (.split 0 95710000)))
  (.seq (.step (.subbox 1))
  (.step (.subbox 2)))))
  (.seq (.seq (.seq (.step (.subbox 3))
  (.step (.subbox 4)))
  (.seq (.step (.subbox 5))
  (.step (.subbox 6))))
  (.seq (.seq (.step (.subbox 7))
  (.step (.subbox 8)))
  (.seq (.step .clamp)
  (.step (.split 5 (-2830936))))))))
  (.seq (.seq (.seq (.seq (.step (.subbox 9))
  (.seq (.step .clamp)
  (.step (.split 0 97140000))))
  (.seq (.seq (.step .clamp)
  (.step (.split 1 97140000)))
  (.seq (.step .clamp)
  (.step (.split 3 5000500)))))
  (.seq (.seq (.seq (.step .clamp)
  (.step (.split 4 5000500)))
  (.seq (.step .clamp)
  (.step (.split 2 87498750))))
  (.seq (.seq (.step .clamp)
  (.step (.split 4 2500250)))
  (.seq (.step .clamp)
  (.step (.split 0 95710000))))))
  (.seq (.seq (.seq (.step .clamp)
  (.seq (.step (.split 1 95710000))
  (.step (.subbox 10))))
  (.seq (.seq (.step (.subbox 11))
  (.step (.subbox 12)))
  (.seq (.step .clamp)
  (.step (.split 3 2500250)))))
  (.seq (.seq (.seq (.step .clamp)
  (.step (.split 1 95710000)))
  (.seq (.step .clamp)
  (.step (.split 0 95710000))))
  (.seq (.seq (.step (.subbox 13))
  (.step (.subbox 14)))
  (.seq (.step (.subbox 15))
  (.step .clamp)))))))
  (.seq (.seq (.seq (.seq (.seq (.step (.split 0 95710000))
  (.seq (.step (.subbox 16))
  (.step (.subbox 17))))
  (.seq (.seq (.step .clamp)
  (.step (.split 4 2500250)))
  (.seq (.step (.subbox 18))
  (.step .clamp))))
  (.seq (.seq (.seq (.step (.split 3 2500250))
  (.step .clamp))
  (.seq (.step (.split 1 95710000))
  (.step .clamp)))
  (.seq (.seq (.step (.split 0 95710000))
  (.step .clamp))
  (.seq (.step (.split 5 (-194308)))
  (.step (.subbox 19))))))
  (.seq (.seq (.seq (.step .clamp)
  (.seq (.step (.split 2 88748874))
  (.step (.subbox 20))))
  (.seq (.seq (.step (.subbox 21))
  (.step (.subbox 22)))
  (.seq (.step (.subbox 23))
  (.step .clamp))))
  (.seq (.seq (.seq (.step (.split 0 95710000))
  (.step .clamp))
  (.seq (.step (.split 1 95710000))
  (.step .clamp)))
  (.seq (.seq (.step (.split 5 (-378908)))
  (.step (.subbox 24)))
  (.seq (.step .clamp)
  (.step (.split 2 88748874)))))))
  (.seq (.seq (.seq (.seq (.step .clamp)
  (.seq (.step (.split 4 3750374))
  (.step (.subbox 25))))
  (.seq (.seq (.step .clamp)
  (.step (.split 3 3750374)))
  (.seq (.step (.subbox 26))
  (.step (.subbox 27)))))
  (.seq (.seq (.seq (.step (.subbox 28))
  (.step (.subbox 29)))
  (.seq (.step (.subbox 30))
  (.step .clamp)))
  (.seq (.seq (.step (.split 2 87498750))
  (.step (.subbox 31)))
  (.seq (.step (.subbox 32))
  (.step (.subbox 33))))))
  (.seq (.seq (.seq (.seq (.step (.subbox 34))
  (.step (.subbox 35)))
  (.seq (.step (.split 2 94999500))
  (.step .clamp)))
  (.seq (.seq (.step (.split 5 (-3570500)))
  (.step (.subbox 36)))
  (.seq (.step (.split 0 97140000))
  (.step (.split 1 97140000)))))
  (.seq (.seq (.seq (.step (.split 3 5000500))
  (.step (.split 4 5000500)))
  (.seq (.step (.subbox 37))
  (.step (.subbox 38))))
  (.seq (.seq (.step (.subbox 39))
  (.step (.subbox 40)))
  (.seq (.step (.subbox 41))
  (.step (.subbox 42))))))))

theorem rootBoxI_certified :
    ∃ (subs : SubTree) (p : Prog),
      SubTreeAll Certified2 subs ∧ checkBox subs p rootBoxI = true :=
  ⟨topSubs, topProg, topSubs_ok, by decide⟩

end Cslib.Circuits.Frontier.Gaussian.PairBound.Cert
