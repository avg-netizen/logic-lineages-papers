module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationFrameValue (d e fp ap parent parentWork state : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hw : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode parentWork parent z)))
    (hs : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing state (suc z) parentWork))) :
    Nonempty (Derivation body Gamma
      (InternalApplicationStepPeel.graph5 applicationFrame state d e fp ap z)) := by
  let xs : Fin 5 → OTerm α :=
    Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons z Fin.elim0))))
  have happ : Nonempty (Derivation body Gamma (programGraph
      (.composition packedApplication ![.projection 0,.projection 1,.projection 2,.projection 3])
      parent xs)) := by
    apply compositionValue packedApplication _ parent xs
      (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) hp
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
        (fun k => Fin.elim0 k)))) i
  have hwork : Nonempty (Derivation body Gamma (programGraph
      (consOf (.composition packedApplication ![.projection 0,.projection 1,
        .projection 2,.projection 3]) (.projection 4)) parentWork xs)) :=
    binaryValue InternalListCodec.consCode _ _ parentWork parent z xs hw happ
      (projectionValue 4 xs)
  exact binaryValue InternalPairing.pairing _ _ state (suc z) parentWork xs hs
    (InternalLessThanSupportProof.oneConstantValue xs) hwork

theorem expandedFrameValue (d e fp ap arrow fn arg argWork joined state : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (hg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode argWork arg z)))
    (hj : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode joined fn argWork)))
    (hs : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) joined))) :
    Nonempty (Derivation body Gamma
      (InternalApplicationStepPeel.graph5 expandedFrame state d e fp ap z)) := by
  let xs : Fin 5 → OTerm α :=
    Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons z Fin.elim0))))
  have harrow := binaryValue InternalListCodec.consCode (.projection 0) (.projection 1)
    arrow d e xs ha (projectionValue 0 xs) (projectionValue 1 xs)
  have hfn := binaryValue InternalPairing.pairing
    (consOf (.projection 0) (.projection 1)) (.projection 2)
    fn arrow fp xs hf harrow (projectionValue 2 xs)
  have harg := binaryValue InternalPairing.pairing (.projection 0) (.projection 3)
    arg d ap xs hg (projectionValue 0 xs) (projectionValue 3 xs)
  have hwork := binaryValue InternalListCodec.consCode
    (pairOf (.projection 0) (.projection 3)) (.projection 4)
    argWork arg z xs hw harg (projectionValue 4 xs)
  have hjoined := binaryValue InternalListCodec.consCode _ _ joined fn argWork xs hj hfn hwork
  exact binaryValue InternalPairing.pairing _ _ state (suc z) joined xs hs
    (InternalLessThanSupportProof.oneConstantValue xs) hjoined

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureFrameProof
