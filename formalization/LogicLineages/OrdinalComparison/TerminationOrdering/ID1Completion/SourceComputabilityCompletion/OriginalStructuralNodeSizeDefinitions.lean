module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSize
open NumberedAuxiliaryCoding InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Encoding-tree node count, including argument-list nil and cons. This is
NOT PrimaryEquivalence.size, which omits list-constructor overhead. -/
def nodeCount {Symbol : Type} : Code Symbol → Nat
  | .var _ | .bottom _ | .argumentsNil => 1
  | .lam _ child | .ordinary _ child => 1 + nodeCount child
  | .app _ first second | .argumentsCons _ first second => 1 + nodeCount first + nodeCount second
  | .numbered _ _ _ first _ second => 1 + nodeCount first + nodeCount second

/-- Independent return algebra. The existing raw visit schedule, arbitrary
metadata, malformed leaves, failure policy and numeric fuel are unchanged. -/
def rebuildValue (raw first second : Nat) : Nat :=
  if arityValue raw = 1 then 1 + first else 1 + first + second

def transitionValue (state : Nat) : Nat :=
  if (Nat.unpair state).1 = 1 then
    let work := (Nat.unpair (Nat.unpair state).2).1
    let results := (Nat.unpair (Nat.unpair state).2).2
    if work = 0 then state else
      let frame := (Nat.unpair (work - 1)).1
      let rest := (Nat.unpair (work - 1)).2
      let tag := (Nat.unpair frame).1
      let p := (Nat.unpair frame).2
      if tag = 0 then
        let d := (Nat.unpair p).1
        let k := (Nat.unpair (Nat.unpair p).2).1
        let raw := (Nat.unpair (Nat.unpair p).2).2
        if arityValue raw = 1 then
          let childCutoff := if tagValue raw = 1 then k + 1 else k
          Nat.pair 1 (Nat.pair
            (1 + Nat.pair (visitValue d childCutoff (firstValue raw))
              (1 + Nat.pair (finishValue raw) rest)) results)
        else if arityValue raw = 2 then
          Nat.pair 1 (Nat.pair
            (1 + Nat.pair (visitValue d k (firstValue raw))
              (1 + Nat.pair (visitValue d k (secondValue raw))
                (1 + Nat.pair (finishValue raw) rest))) results)
        else Nat.pair 1 (Nat.pair rest (1 + Nat.pair (1) results))
      else if tag = 1 then
        if arityValue p = 1 then
          if results = 0 then 0 else
            Nat.pair 1 (Nat.pair rest (1 + Nat.pair
              (rebuildValue p (Nat.unpair (results - 1)).1 0) (Nat.unpair (results - 1)).2))
        else if arityValue p = 2 then
          if results = 0 then 0 else
            let afterSecond := (Nat.unpair (results - 1)).2
            if afterSecond = 0 then 0 else
              Nat.pair 1 (Nat.pair rest (1 + Nat.pair
                (rebuildValue p (Nat.unpair (afterSecond - 1)).1 (Nat.unpair (results - 1)).1)
                (Nat.unpair (afterSecond - 1)).2))
        else 0
      else 0
  else 0

def iterateValue (count initial : Nat) : Nat := Nat.rec initial (fun _ state => transitionValue state) count
def rawValue (raw : Nat) : Nat := outputValue (iterateValue (fuelValue raw) (initialValue 0 0 raw))

def leafReturned : Program 1 := liveOf rest (consOf (constant 1 1) results)
def returnedOne : Program 1 := liveOf rest (consOf (succOf (headOf results)) (tailOf results))
def returnedTwo : Program 1 := liveOf rest
  (consOf (succOf (addOf (headOf (tailOf results)) (headOf results))) (tailOf (tailOf results)))

def transition : Program 1 :=
  InternalAcceptance.branch (sameOf status (constant 1 1)) (constant 1 0)
    (InternalAcceptance.branch work (.projection 0)
      (InternalAcceptance.branch (sameOf frameTag (constant 1 0))
        (InternalAcceptance.branch (sameOf frameTag (constant 1 1)) (constant 1 0)
          (InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 1))
            (InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 2)) (constant 1 0)
              (InternalAcceptance.branch results (constant 1 0)
                (InternalAcceptance.branch (tailOf results) (constant 1 0) (returnedTwo))))
            (InternalAcceptance.branch results (constant 1 0) (returnedOne))))
        (InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 1))
          (InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 2)) (leafReturned) expandedTwo)
          expandedOne)))


def iterate : Program 2 := .recursion (.projection (0 : Fin 1))
  (.composition transition (fun _ : Fin 1 => .projection (1 : Fin 3)))
def run : Program 3 := .composition iterate ![fuel,initial]
def raw : Program 1 := .composition output
  (fun _ : Fin 1 => .composition run ![constant 1 0,constant 1 0,.projection 0])
/-- Packed outer type contributes no syntax node. -/
def packed : Program 1 := .composition raw (fun _ : Fin 1 => InternalUnpair.right)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSize
