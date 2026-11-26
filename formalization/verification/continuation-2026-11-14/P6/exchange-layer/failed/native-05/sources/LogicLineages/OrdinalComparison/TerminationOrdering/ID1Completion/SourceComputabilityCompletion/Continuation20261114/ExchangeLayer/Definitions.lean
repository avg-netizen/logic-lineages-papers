module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact-one Boolean disjunction, built from the existing conditional. -/
def any (p q : Program 19) : Program 19 :=
  InternalAcceptance.branch (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize p)
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize q) (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize p)
def both := @InternalAcceptance.conjunction 19
def eqField (i j : Fin 19) : Program 19 :=
  .composition InternalEqualityTest.equalityTest ![.projection i,.projection j]
def constant (k : Nat) : Program 19 :=
  match k with
  | 0 => InternalAcceptance.constantZero 19
  | k+1 => .composition .succ (fun _ : Fin 1 => constant k)
def tagIs (k : Nat) : Program 19 :=
  .composition InternalEqualityTest.equalityTest ![.projection 0,constant k]
def choose (p yes no : Program 19) : Program 19 := InternalAcceptance.branch p no yes
def lambdaCase : Program 19 := both (eqField 1 8) (.projection 14)
def applicationCase : Program 19 := both (eqField 1 8)
  (any (both (eqField 6 13) (.projection 14)) (both (eqField 5 12) (.projection 15)))
def ordinaryCase : Program 19 :=
  any (both (.projection 16) (eqField 18 17)) (both (eqField 2 9) (.projection 14))
def numberedCase : Program 19 :=
  both (both (eqField 3 10) (both (eqField 1 8) (eqField 4 11)))
    (any (any (both (eqField 6 13) (.projection 16))
      (both (both (eqField 2 9) (eqField 6 13)) (.projection 14)))
      (both (both (eqField 2 9) (eqField 5 12)) (.projection 15)))
/-- The original five active tags; tag 7 shares the literal application-shaped test. -/
def layer : Program 19 := choose (eqField 0 7)
  (choose (tagIs 1) lambdaCase (choose (tagIs 2) applicationCase
    (choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase
      (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))))))
  (InternalAcceptance.constantZero 19)
/-- Fields 0..6 and 7..13 are the literal original Fields tuples. Slots 14/15
are original answer positions 0/3, slot16 is actual headMove, 17/18 head results. -/
def input (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n) : List.Vector Nat 19 :=
  let x := p.2.1
  let y := p.2.2.1
  List.Vector.ofFn ![x.1,Encodable.encode x.2.1,Encodable.encode x.2.2.1,x.2.2.2.1,
    Encodable.encode x.2.2.2.2.1,Encodable.encode x.2.2.2.2.2.1,Encodable.encode x.2.2.2.2.2.2,
    y.1,Encodable.encode y.2.1,Encodable.encode y.2.2.1,y.2.2.2.1,
    Encodable.encode y.2.2.2.2.1,Encodable.encode y.2.2.2.2.2.1,Encodable.encode y.2.2.2.2.2.2,
    (p.2.2.2.getD 0 false).toNat,(p.2.2.2.getD 3 false).toNat,
    (NumberedExchangeCode.headMove arity p.1.1 p.1.2 x.2.2.1 x.2.2.2.2.2.1
      y.2.2.1 y.2.2.2.2.2.1).toNat,
    Encodable.encode (headResult (decodeHead x.2.2.1)),
    Encodable.encode (headResult (decodeHead y.2.2.1))]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer
