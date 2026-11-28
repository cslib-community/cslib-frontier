/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Electrical.LinearCircuit
public import CslibFrontier.Foundations.Data.Nat.ToDigits

/-!
# Netlist text: a SPICE subset for linear circuits

A reader (`Cslib.Electrical.Text.parse`) for the netlists of `Cslib.Electrical.Netlist`, in a
subset of the SPICE netlist format, with one directive of its own (`.probe`, below). The format
follows the ngspice manual [Vogt2026] where the two overlap (§2.1.1 for the file structure,
§2.1.3 for fields, numbers and node names, §2.4 for the title, `.end` and comment lines, §4.1 for
the independent sources); the tests use node names of the form a schematic editor writes
(`/out`, `Net-_R1-Pad2_`), but no exporter's actual output has been checked against this
reader. An exported netlist is accepted only after its analysis and output lines (`.tran`,
`.ac`, `.save`, `.control` blocks, …) are replaced by `.probe` lines.

## The grammar

The text is a list of lines, separated by `\n`; a line's words are separated by spaces, tabs or
carriage returns, so leading and trailing blanks and `\r\n` line ends are allowed.

* The **first line is the title** and is ignored, whatever it contains, as in SPICE (§2.1.1,
  §2.4.1). A `.title` line elsewhere is rejected.
* Blank lines and **comment lines**, whose first word starts with `*` (§2.4.3), are ignored.
  End-of-line comments (`$`, `;`, `//`, §2.4.4) are not supported: these characters are not
  name characters, or (for `//`) not allowed in a name, so a line containing one is rejected.
* The netlist ends with a line consisting of the word `.end` (in either case) alone (§2.4.2).
  A text without such a line is rejected, and so is a `.end` line with more words. Only blank
  lines may follow it; any other line after it, including a comment, is rejected, so no input
  is silently dropped. (§2.1.1 asks for a newline after `.end`; this reader does not.)
* An **element line** starts with the element name; its first letter, in either case, gives
  the element:

  | line | element |
  |---|---|
  | `Rname n+ n- value` | resistor, `value` ohms |
  | `Cname n+ n- value` | capacitor, `value` farads |
  | `Lname n+ n- value` | inductor, `value` henries |
  | `Vname n+ n- [[dc] value] [ac [1]]` | voltage source `v(n+) - v(n-) = value` |
  | `Iname n+ n- [[dc] value] [ac [1]]` | current source, `value` A from `n+` through it to `n-` |
  | `Gname n+ n- nc+ nc- value` | VCCS: current `value · v(nc+, nc-)` (S) from `n+` to `n-` |
  | `Ename n+ n- nc+ nc- value` | VCVS: `v(n+) - v(n-) = value · v(nc+, nc-)` |

  These are the element laws and the sign conventions of `Cslib.Electrical.Element`, which are
  SPICE's (§4.1 for the sources). A source's value defaults to `0`, and `dc` must be followed by
  a value.
* **Input ports** (an interpretation of this library, not SPICE's). In SPICE, `ac mag` marks a
  source as the stimulus of small-signal AC analysis and does not change its DC or transient
  value (§4.1). Here a source marked `ac` (with magnitude `1`, written or implied; §4.1's
  general form leaves the magnitude optional, and a phase is rejected) is an input port of unit
  gain: its value is `value + u_k` for an arbitrary input signal `u_k`, with the input ports
  numbered `0, 1, …` in the order of their lines. For a circuit of the elements above, the
  transfer function from `u_k` to a probe is then what ngspice's AC analysis computes when that
  source is the only one marked `ac`.
* An **output line** selects a probe: `.probe v n1 [n2]` is the voltage `v(n1) - v(n2)` (with
  `n2 = 0` if omitted) and `.probe i name` the current of the element `name`, in the direction
  of its element law; probes are numbered in the order of their lines. This syntax is this
  library's own: ngspice's `.probe` directive (§11.6.5) has another syntax (`.probe v(node)`,
  `.probe I(device)`, …) and another meaning (it saves vectors in a simulation), and its forms
  are rejected here.

**Nodes.** The node `0` is the ground. Every other node name is numbered `1, 2, …` in the order
of first appearance on the element lines (positive, negative, then control nodes). Names are
compared exactly, and a text with two distinct names that differ only in case is rejected, since
ngspice does not distinguish them (§2.1.3.4). The name `gnd` (in any case) is rejected: ngspice
reads it as the ground (§2.1.3.5). Node and element names consist of letters, digits and
`_ - / + . #`, without `//`; two elements with the same name (up to case) are rejected.

**Values** are exact rationals: an optional sign, decimal digits, an optional fractional part
`.digits` with at least one digit, an optional exponent `e[sign]digits` and an optional scale
suffix, in either case, `t` (`10¹²`), `g` (`10⁹`), `meg` (`10⁶`), `k` (`10³`), `m` (`10⁻³`), `u`
(`10⁻⁶`), `n` (`10⁻⁹`), `p` (`10⁻¹²`) or `f` (`10⁻¹⁵`) (§2.1.3.2). Thus `1.e2`, `1.` and `.5`
are rejected, and so are the suffixes `mil` and `a`. Nothing may follow the suffix: ngspice
ignores trailing letters (§2.1.3.3), so that `1F` is `10⁻¹⁵` there, and a unit written after a
value is rejected rather than guessed.

**Rejected.** Every other line is rejected with a message, and nothing is silently omitted:
other elements (diodes, transistors, subcircuit instances `X`, mutual inductances `K`,
current-controlled sources `F`, `H`, behavioural sources `B`), every other directive
(`.include`, `.lib`, `.model`, `.subckt`, `.param`, `.options`, analyses such as `.tran` or
`.ac`), continuation lines (`+`), parameter expressions and malformed values. A netlist that
`parse` accepts may still fail `Cslib.Electrical.Netlist.check` (a nonpositive `R`, `C` or `L`),
and then no certificate is accepted for it.

## Main definitions

* `Cslib.Electrical.Text.ParsedNetlist`: a netlist with its probes and the names of its nodes
  and elements.
* `Cslib.Electrical.Text.parse`: the reader.

## References

* [Vogt2026]: H. Vogt, G. Atkinson, D. Warning, P. Nenzi, *Ngspice User's Manual, Version 46*,
  March 31st, 2026; the sections cited above were read in that version.
-/

@[expose] public section

namespace Cslib.Electrical.Text

/-! ### Lines and words -/

/-- Whether `c` separates words: a space, a tab or a carriage return. -/
def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

/-- The pieces of `cs` between the characters satisfying `p` (with empty pieces). -/
def splitBy (p : Char → Bool) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    let r := splitBy p cs
    if p c then [] :: r else (c :: r.headD []) :: r.tail

/-- The lines of a text. -/
def lines (cs : List Char) : List (List Char) := splitBy (· == '\n') cs

/-- The words of a line. -/
def words (l : List Char) : List (List Char) := (splitBy isBlank l).filter (!·.isEmpty)

/-- The lower-case form of a word. -/
def lower (w : List Char) : List Char := w.map Char.toLower

/-! ### Values -/

/-- The decimal digits at the front of `cs`, and the rest. -/
def digits : List Char → List Char × List Char
  | c :: cs => if c.isDigit then ((c :: (digits cs).1), (digits cs).2) else ([], c :: cs)
  | [] => ([], [])

/-- The value of decimal digits. -/
def digitsVal (ds : List Char) : ℕ := ds.foldl Nat.digitStep 0

/-- An optional sign: `true` for `-`. -/
def sign : List Char → Bool × List Char
  | '-' :: cs => (true, cs)
  | '+' :: cs => (false, cs)
  | cs => (false, cs)

/-- The power of ten of a scale suffix (lower case). -/
def suffixExp : List Char → Option ℤ
  | [] => some 0
  | ['t'] => some 12
  | ['g'] => some 9
  | ['m', 'e', 'g'] => some 6
  | ['k'] => some 3
  | ['m'] => some (-3)
  | ['u'] => some (-6)
  | ['n'] => some (-9)
  | ['p'] => some (-12)
  | ['f'] => some (-15)
  | _ => none

/-- The optional exponent `e[sign]digits` at the front of `cs`, and the rest. A trailing `e`
without digits is left in the rest, where no suffix accepts it. -/
def exponent (cs : List Char) : ℤ × List Char :=
  match cs with
  | c :: cs' =>
    if c == 'e' || c == 'E' then
      let (neg, ds) := sign cs'
      let (d, rest) := digits ds
      if d.isEmpty then (0, cs) else ((if neg then -1 else 1) * (digitsVal d : ℤ), rest)
    else (0, cs)
  | [] => (0, [])

/-- The optional fractional part `.digits` at the front of `cs`, and the rest. A `.` without
digits is left in the rest, where no suffix accepts it. -/
def fraction : List Char → List Char × List Char
  | '.' :: cs => match digits cs with
    | ([], _) => ([], '.' :: cs)
    | r => r
  | cs => ([], cs)

/-- **A value**: `[sign] digits [. digits] [e [sign] digits] [suffix]`, exactly, with at least
one digit before and (if there is a `.`) after the dot. -/
def value? (w : List Char) : Option ℚ :=
  let (neg, w) := sign w
  let (ip, w) := digits w
  let (fp, w) := fraction w
  let (e, w) := exponent w
  if ip.isEmpty then none else
    match suffixExp (lower w) with
    | none => none
    | some s =>
      some ((if neg then -1 else 1) *
        (((digitsVal ip : ℚ) + (digitsVal fp : ℚ) / 10 ^ fp.length) * (10 : ℚ) ^ (e + s)))

/-! ### Cards -/

/-- A line of the text that describes part of the circuit, with node names not yet resolved. -/
inductive Card where
  /-- An element line: the name, the nodes (two, or four for a controlled source), the value
  and whether a source is an input port. -/
  | element (name : List Char) (nodes : List (List Char)) (value : ℚ) (ac : Bool)
  /-- `.probe v p q`. -/
  | probeV (p q : List Char)
  /-- `.probe i name`. -/
  | probeI (name : List Char)
  deriving DecidableEq

/-- Whether `c` may occur in a name. -/
def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '/' || c == '+' || c == '.' || c == '#'

/-- Whether a word contains `//`, which ngspice reads as the start of an end-of-line comment. -/
def hasDoubleSlash : List Char → Bool
  | '/' :: '/' :: _ => true
  | _ :: cs => hasDoubleSlash cs
  | [] => false

/-- Whether `w` is a well-formed name: nonempty, of name characters, without `//`. -/
def isName (w : List Char) : Bool := !w.isEmpty && w.all isNameChar && !hasDoubleSlash w

/-- Whether `w` is a well-formed node name: a name other than `gnd`. -/
def isNodeName (w : List Char) : Bool := isName w && lower w != "gnd".toList

/-- The number of nodes of an element with first letter `c` (lower case): `2` for `R`, `C`, `L`,
`V`, `I`, `4` for `G`, `E`, and `0` (unsupported) otherwise. -/
def arity (c : Char) : ℕ :=
  if c == 'r' || c == 'c' || c == 'l' || c == 'v' || c == 'i' then 2
  else if c == 'g' || c == 'e' then 4 else 0

/-- Whether the element with first letter `c` (lower case) is an independent source. -/
def isSource (c : Char) : Bool := c == 'v' || c == 'i'

/-- The value of a source, `[[dc] value]` (`0` if omitted), and the rest. -/
def sourceValue : List (List Char) → Except String (ℚ × List (List Char))
  | [] => .ok (0, [])
  | w :: ws =>
    if lower w == "dc".toList then
      match ws with
      | w' :: ws' => match value? w' with
        | some q => .ok (q, ws')
        | none => .error "malformed source"
      | [] => .error "malformed source"
    else match value? w with
      | some q => .ok (q, ws)
      | none => .ok (0, w :: ws)

/-- The value and input flag of a source: `[[dc] value] [ac [1]]`. -/
def sourceSpec (ws : List (List Char)) : Except String (ℚ × Bool) :=
  match sourceValue ws with
  | .error e => .error e
  | .ok (v, ws) =>
  match ws with
  | [] => .ok (v, false)
  | [a] => if lower a == "ac".toList then .ok (v, true) else .error "malformed source"
  | [a, m] =>
    if lower a == "ac".toList && value? m == some 1 then .ok (v, true)
    else .error "unsupported source: only `ac 1` input ports"
  | _ => .error "malformed source"

/-- An element line. -/
def elementCard (name : List Char) (ws : List (List Char)) : Except String Card :=
  match name with
  | [] => .error "empty name"
  | c :: _ =>
    let k := c.toLower
    let n := arity k
    if n = 0 then .error ("unsupported element: " ++ String.ofList name) else
    if !isName name then .error "malformed name" else
    let nodes := ws.take n
    if nodes.length != n || !nodes.all isNodeName then .error "malformed nodes" else
    if isSource k then
      match sourceSpec (ws.drop n) with
      | .ok (v, ac) => .ok (.element name nodes v ac)
      | .error e => .error e
    else
      match ws.drop n with
      | [w] => match value? w with
        | some v => .ok (.element name nodes v false)
        | none => .error ("malformed value: " ++ String.ofList w)
      | _ => .error "malformed element"

/-- A probe line, after `.probe`. -/
def probeCard : List (List Char) → Except String Card
  | [k, p] => if lower k == ['v'] && isNodeName p then .ok (.probeV p ['0'])
      else if lower k == ['i'] && isName p then .ok (.probeI p) else .error "malformed probe"
  | [k, p, q] => if lower k == ['v'] && isNodeName p && isNodeName q then .ok (.probeV p q)
      else .error "malformed probe"
  | _ => .error "malformed probe"

/-- The cards of the lines after the title, up to the `.end` line, which must be present, alone
on its line and followed by blank lines only. -/
def cards : List (List Char) → Except String (List Card)
  | [] => .error "missing .end"
  | l :: ls =>
    match words l with
    | [] => cards ls
    | w :: ws =>
      if w.head? == some '*' then cards ls
      else if lower w == ".end".toList then
        if !ws.isEmpty then .error "malformed .end"
        else if ls.all fun l => (words l).isEmpty then .ok []
        else .error "text after .end"
      else if lower w == ".probe".toList then
        match probeCard ws, cards ls with
        | .ok c, .ok cs => .ok (c :: cs)
        | .error e, _ => .error e
        | _, .error e => .error e
      else if w.head? == some '.' then .error ("unsupported directive: " ++ String.ofList w)
      else
        match elementCard w ws, cards ls with
        | .ok c, .ok cs => .ok (c :: cs)
        | .error e, _ => .error e
        | _, .error e => .error e

/-! ### Resolving names -/

deriving instance DecidableEq for Element, Branch, Netlist, Probe

/-- A netlist read from text: the circuit, its probes, and the names of its nodes `1, 2, …` and
of its branches, in order. -/
structure ParsedNetlist where
  /-- The circuit. -/
  netlist : Netlist
  /-- The output probes. -/
  probes : List Probe
  /-- The names of the nodes `1, …, netlist.nodes`. -/
  nodeNames : List (List Char)
  /-- The names of the branches, in order. -/
  branchNames : List (List Char)
  deriving DecidableEq

/-- The node names of the element cards, in order of appearance, without the ground. -/
def nodeRefs (cs : List Card) : List (List Char) :=
  cs.flatMap fun
    | .element _ nodes _ _ => nodes.filter (· != ['0'])
    | _ => []

/-- The number of node `w` in the table `names` (`0` for the ground). -/
def nodeIndex (names : List (List Char)) (w : List Char) : ℕ :=
  if w = ['0'] then 0 else names.idxOf w + 1

/-- The element of an element card, with the nodes numbered by `names` and input port `k` if it
is an input port. -/
def toBranch (names : List (List Char)) (k : ℕ) : Card → Branch
  | .element name nodes v ac =>
    let n := fun i => nodeIndex names (nodes.getD i [])
    let input := if ac then some k else none
    ⟨n 0, n 1, match (name.headD 'x').toLower with
      | 'r' => .resistor v
      | 'c' => .capacitor v
      | 'l' => .inductor v
      | 'v' => .voltageSource v input
      | 'i' => .currentSource v input
      | 'g' => .vccs v (n 2) (n 3)
      | _ => .vcvs v (n 2) (n 3)⟩
  | _ => default

/-- The branches of the element cards, numbering the input ports in order. -/
def branchesOf (names : List (List Char)) : ℕ → List Card → List Branch
  | _, [] => []
  | k, (c@(.element _ _ _ ac)) :: cs =>
    toBranch names k c :: branchesOf names (if ac then k + 1 else k) cs
  | k, _ :: cs => branchesOf names k cs

/-- The number of input ports among the cards. -/
def inputCount (cs : List Card) : ℕ :=
  (cs.filter fun | .element _ _ _ ac => ac | _ => false).length

/-- The names of the element cards. -/
def elementNames (cs : List Card) : List (List Char) :=
  cs.filterMap fun | .element name _ _ _ => some name | _ => none

/-- The probe of a probe card. -/
def toProbe (names enames : List (List Char)) : Card → Except String Probe
  | .probeV p q =>
    if (p = ['0'] ∨ p ∈ names) ∧ (q = ['0'] ∨ q ∈ names) then
      .ok (.voltage (nodeIndex names p) (nodeIndex names q))
    else .error "probe of an unknown node"
  | .probeI n => if n ∈ enames then .ok (.current (enames.idxOf n)) else
      .error "probe of an unknown element"
  | _ => .error "not a probe"

/-- Whether a card is a probe card. -/
def isProbeCard : Card → Bool
  | .element .. => false
  | _ => true

/-- The probes of the probe cards. -/
def probesOf (names enames : List (List Char)) (cs : List Card) : Except String (List Probe) :=
  (cs.filter isProbeCard).mapM (toProbe names enames)

/-- **Resolving the names of the cards.** -/
def resolve (cs : List Card) : Except String ParsedNetlist :=
  let names := (nodeRefs cs).eraseDups
  let enames := elementNames cs
  if !(names.map lower).Nodup then .error "node names that differ only in case" else
  if !(enames.map lower).Nodup then .error "duplicate element names" else
  match probesOf names enames cs with
  | .error e => .error e
  | .ok probes =>
    .ok { netlist := { nodes := names.length, inputs := inputCount cs
                       branches := branchesOf names 0 cs }
          probes := probes, nodeNames := names, branchNames := enames }

/-- **The reader**: the netlist described by a text, or the reason it is rejected. The first line
is the title and is skipped. -/
def parse (s : String) : Except String ParsedNetlist :=
  match cards (lines s.toList).tail with
  | .ok cs => resolve cs
  | .error e => .error e

end Cslib.Electrical.Text
