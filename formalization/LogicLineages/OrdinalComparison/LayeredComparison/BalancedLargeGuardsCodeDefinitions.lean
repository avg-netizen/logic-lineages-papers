module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode
open CommonHeadLargeGuards (masks maskCoefficient)
open CommonHeadCode (constant conjunction disjunction negative conjoin disjoin)

/-- The existing postfix BASE-guard code, without an ordinal-valued opcode. -/
abbrev Code := CommonHeadCode.Code

/-- Literal ordered raw codes of normal heads. Repetitions are retained. This
is a semantic calibration map, not a new normal-notation codec. -/
def encodeHeads (heads : List NONote) : List Nat :=
  heads.map (fun h => rawNoteEncode h.1)

/-- Missing head positions use the raw code of the actual zero notation.
Coefficient and head-list lengths need not agree on arbitrary raw inputs. -/
def headCode (heads : List Nat) (i : Nat) : Nat := heads.getD i 0

/-- Equal raw codes of actual normal heads mean equal heads. The guard still
compares the two original input labels, rather than comparing head codes at
runtime. -/
def keyEqualCode (heads : List Nat) (i j : Nat) : Code :=
  if headCode heads i = headCode heads j then [(2,i,j)] else constant false

/-- Literal hereditary CNF comparison decides the fixed head order. Natural
ordering of raw codes is never used. Equality retains the input-order guard. -/
def keyLessCode (heads : List Nat) (i j : Nat) : Code :=
  if rawComparisonCode (headCode heads i) (headCode heads j) = 0 then constant true
  else if headCode heads i = headCode heads j then [(3,i,j)] else constant false

/-- Ascending original labels, with one positive or negative membership
guard for every label. Extra mask bits are ignored; missing bits are false. -/
def maskCode (heads : List Nat) (m i : Nat) (mask : List Bool) : Code :=
  conjoin ((List.range m).map (fun j =>
    if mask.getD j false then keyEqualCode heads i j
    else negative (keyEqualCode heads i j)))

/-- The inherited mask enumeration and stable filter preserve their exact
list order. Integer coefficients, zero coefficients and duplicates survive
unchanged; no block collection is performed by the constructor. -/
def blockCode (heads : List Nat) (cs : List Int) (i : Nat) (desired : Int) : Code :=
  disjoin (((masks cs.length).filter
    (fun mask => Int.sign (maskCoefficient cs mask) = desired)).map
      (maskCode heads cs.length i))

def canceledCode (heads : List Nat) (cs : List Int) : Code :=
  conjoin ((List.range cs.length).map (fun i => blockCode heads cs i 0))

/-- Every greater actual key is required to cancel, including greater keys
whose original occurrences precede this one in the list. -/
def maximalCode (heads : List Nat) (cs : List Int) (i : Nat) : Code :=
  conjoin ((List.range cs.length).map (fun j =>
    disjunction (negative (keyLessCode heads i j)) (blockCode heads cs j 0)))

def differenceSignCode (left right : Nat) (desired : Int) : Code :=
  if desired = -1 then [(3,left,right)]
  else if desired = 0 then [(2,left,right)]
  else if desired = 1 then [(3,right,left)]
  else constant false

/-- The final labels are the two lower expressions, in left/right order.
This generic constructor does not construct or independently value them. -/
def signCode (heads : List Nat) (cs : List Int) (desired : Int) : Code :=
  disjunction
    (conjunction (canceledCode heads cs)
      (differenceSignCode cs.length (cs.length + 1) desired))
    (if desired = 0 then constant false else
      disjoin ((List.range cs.length).map (fun i =>
        conjunction (blockCode heads cs i desired) (maximalCode heads cs i))))

/-- Bounds use the supplied original threshold and EVERY original occurrence.
The resulting code is in the existing eight-tag postfix guard language. -/
def largeCode (L : Nat) (heads : List Nat) (cs : List Int) (desired : Int) : Code :=
  conjunction (conjoin ((List.range cs.length).map (fun i => [(4,L,i)])))
    (signCode heads cs desired)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCode
