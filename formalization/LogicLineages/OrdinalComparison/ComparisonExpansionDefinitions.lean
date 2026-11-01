module
public import LogicLineages.OrdinalComparison.SourceCarrierClosureDefinitions
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainDefinitions
public import LogicLineages.OrdinalComparison.SourceSuccessorCallsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison

def encodedComparisonWord (n : Nat) : List (Nat × Nat) :=
  (Encodable.decode (α := List (Nat × Nat)) (n/2).unpair.1).getD []

def encodedComparisonOuter (n : Nat) : Nat × Nat := (encodedComparisonWord n).reverse.headD (0,0)

/-- Literal prefix RANGE code even for the empty prefix; the actual checked
successor normalizer consumes this code, not the canonical P/R stripped sort. -/
def encodedComparisonRangePrefix (n : Nat) : Nat :=
  2*Nat.pair (Encodable.encode (encodedComparisonWord n).reverse.tail.reverse) (n/2).unpair.2+1

def encodedComparisonPositiveChildren (n m : Nat) : List (Nat × Nat) :=
  let heads := encodedDisplayedSourceHeads n++encodedDisplayedSourceHeads m
  heads.flatMap (fun a => heads.flatMap (fun b =>
    if a=b then [] else [(encodedSourcePeakWord a.1 a.2,encodedSourcePeakWord b.1 b.2)]))

/-- Orient the larger outer principal first. The one genuine finite successor
pass is COMBINED with its final recursive child, never recursively called as
an unchanged intermediate comparison state. -/
def encodedComparisonMixedChildren (high low : Nat) : List (Nat × Nat) :=
  let outer := encodedComparisonOuter high
  let lower := encodedComparisonOuter low
  let result := encodedSuccessorNormalization (encodedComparisonRangePrefix high) outer.1 lower.1 outer.2
  if result.2.1=lower.1 then [(encodedComparisonStripOuter result.1,encodedComparisonStripOuter low)]
  else [(result.1,encodedComparisonStripOuter low)]

/-- Finite EXACT numerical source child programme. PP deliberately compares
all distinct original displayed pairs; superfluous comparisons are finite and
strictly decrease original h. Source rows later select the relevant results. -/
def encodedComparisonChildren (n m : Nat) : List (Nat × Nat) :=
  if encodedComparisonSourceDomain n≠1 ∨ encodedComparisonSourceDomain m≠1 then []
  else if n%2=0 then
    if m%2=0 then encodedComparisonPositiveChildren (n/2) (m/2)
    else (encodedDisplayedSourceHeads (n/2)).map (fun p => (m,encodedSourcePeakWord p.1 p.2))
  else if m%2=0 then
    (encodedDisplayedSourceHeads (m/2)).map (fun p => (n,encodedSourcePeakWord p.1 p.2))
  else
    let a := encodedComparisonOuter n
    let b := encodedComparisonOuter m
    if a.1=b.1 then [(encodedComparisonStripOuter n,encodedComparisonStripOuter m)]
    else if rawComparisonCode a.1 b.1=2 then encodedComparisonMixedChildren n m
    else encodedComparisonMixedChildren m n

end LogicLineages.OrdinalComparison
