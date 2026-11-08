module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem graph6Rename {α β : Type} (p : Program 6)
    (out a b c d e f : OTerm α) (j : α → β) :
    (graph6 p out a b c d e f).relabel j =
      graph6 p (out.relabel j) (a.relabel j) (b.relabel j) (c.relabel j)
        (d.relabel j) (e.relabel j) (f.relabel j) := by
  simp only [graph6,programRename,consTermRename,emptyRename]

def childrenQ : Program 6 := pairOf (.projection 2) (.projection 3)
def bodyQ : Program 6 := pairOf (.projection 0) childrenQ
def nodeQ : Program 6 := pairOf (two 6) bodyQ
def appQ : Program 6 := pairOf (.projection 1) nodeQ
def visitQ : Program 6 := visitOf appQ
def workQ : Program 6 := consOf visitQ (.projection 4)
def payloadQ : Program 6 := pairOf workQ (.projection 5)
def arrowQ : Program 6 := consOf (.projection 0) (.projection 1)
def functionQ : Program 6 := pairOf arrowQ (.projection 2)
def argumentQ : Program 6 := pairOf (.projection 0) (.projection 3)
def functionVisitQ : Program 6 := visitOf functionQ
def argumentVisitQ : Program 6 := visitOf argumentQ
def typesQ : Program 6 := pairOf (.projection 0) (.projection 1)
def finishQ : Program 6 := finishOf (.projection 0) (.projection 1)
def finishWorkQ : Program 6 := consOf finishQ (.projection 4)
def argumentWorkQ : Program 6 := consOf argumentVisitQ finishWorkQ
def expandedWorkQ : Program 6 := consOf functionVisitQ argumentWorkQ
def expandedPayloadQ : Program 6 := pairOf expandedWorkQ (.projection 5)
def queries : Fin 19 → Program 6 :=
  ![childrenQ,bodyQ,nodeQ,appQ,visitQ,workQ,payloadQ,arrowQ,functionQ,argumentQ,
    functionVisitQ,argumentVisitQ,typesQ,finishQ,finishWorkQ,argumentWorkQ,
    expandedWorkQ,expandedPayloadQ,expandedState]

theorem transitionFromQueries (guard leaf : Program 1) (combine : Program 4)
    (d e fp ap value tail results state : OTerm α) (ys : Fin 19 → OTerm α)
    (hvalue : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap)))
    (hstate : Nonempty (Derivation body Gamma (graph3 visitState state value tail results)))
    (hguard : Nonempty (Derivation body Gamma (graph1 guard (suc z) value)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail (Fin.cons results Fin.elim0))))))))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) (ys 18) state)) := by
  let xs : Fin 6 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail (Fin.cons results Fin.elim0)))))
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) fp ap xs (hq 0) (projectionValue 2 xs) (projectionValue 3 xs)
  have hb := binaryRecover InternalPairing.pairing (.projection 0) childrenQ
    (ys 1) d (ys 0) xs (hq 1) (projectionValue 0 xs) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (two 6) bodyQ
    (ys 2) positionTerm (ys 1) xs (hq 2) (twoValue xs) (hq 1)
  have ha := binaryRecover InternalPairing.pairing (.projection 1) nodeQ
    (ys 3) e (ys 2) xs (hq 3) (projectionValue 1 xs) (hq 2)
  have happ := packedAtPairs d e fp ap (ys 0) (ys 1) (ys 2) (ys 3) hc hb hn ha
  have heq := valueUnique packedApplication value (ys 3)
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) hvalue happ
  have hstate' := headTransport visitState state value (ys 3)
    (Fin.cons tail (Fin.cons results Fin.elim0)) heq hstate
  have hguard' := headTransport guard (suc z) value (ys 3) Fin.elim0 heq hguard
  have hv := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 6) appQ
    (ys 4) z (ys 3) xs (hq 4) (constantZeroValue xs) (hq 3)
  have hw := binaryRecover InternalListCodec.consCode visitQ (.projection 4)
    (ys 5) (ys 4) tail xs (hq 5) (hq 4) (projectionValue 4 xs)
  have hp := binaryRecover InternalPairing.pairing workQ (.projection 5)
    (ys 6) (ys 5) results xs (hq 6) (hq 5) (projectionValue 5 xs)
  let vs : Fin 3 → OTerm α := Fin.cons (ys 3) (Fin.cons tail (Fin.cons results Fin.elim0))
  have hv' := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 3) (.projection 0)
    (ys 4) z (ys 3) vs hv (constantZeroValue vs) (projectionValue 0 vs)
  have hw' := binaryValue InternalListCodec.consCode (visitOf (.projection 0)) (.projection 1)
    (ys 5) (ys 4) tail vs hw hv' (projectionValue 1 vs)
  have hp' := binaryValue InternalPairing.pairing (consOf (visitOf (.projection 0)) (.projection 1)) (.projection 2)
    (ys 6) (ys 5) results vs hp hw' (projectionValue 2 vs)
  have hpair := binaryRecover InternalPairing.pairing _ _ state (suc z) (ys 6) vs
    hstate' (InternalLessThanSupportProof.oneConstantValue vs) hp'
  have hstatus : Nonempty (Derivation body Gamma (graph1 status (suc z) state)) := pairLeft state (suc z) (ys 6) hpair
  have hpayload := pairRight state (suc z) (ys 6) hpair
  have hwork : Nonempty (Derivation body Gamma (graph1 work (ys 5) state)) :=
    unaryValue InternalUnpair.left InternalUnpair.right (ys 5) (ys 6) ss (pairLeft (ys 6) (ys 5) results hp) hpayload
  have hresults : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.results results state)) :=
    unaryValue InternalUnpair.right InternalUnpair.right results (ys 6) ss (pairRight (ys 6) (ys 5) results hp) hpayload
  have hd := InternalListCodecSupportProof.consDestruction (ys 5) (ys 4) tail hw
  have hcurrent : Nonempty (Derivation body Gamma (graph1 currentFrame (ys 4) state)) :=
    unaryValue InternalListCodec.headCode work (ys 4) (ys 5) ss (andLeft hd) hwork
  have hrest : Nonempty (Derivation body Gamma (graph1 rest tail state)) :=
    unaryValue InternalListCodec.tailCode work tail (ys 5) ss (andLeft (andRight hd)) hwork
  have hframeTag : Nonempty (Derivation body Gamma (graph1 frameTag z state)) :=
    unaryValue InternalUnpair.left currentFrame z (ys 4) ss (pairLeft (ys 4) z (ys 3) hv) hcurrent
  have hcurrentValue : Nonempty (Derivation body Gamma (graph1 currentValue (ys 3) state)) :=
    unaryValue InternalUnpair.right currentFrame (ys 3) (ys 4) ss (pairRight (ys 4) z (ys 3) hv) hcurrent
  have fields := fieldsAtPairs currentValue state (ys 3) d e fp ap (ys 0) (ys 1) (ys 2) hcurrentValue hc hb hn ha
  have htype := andLeft fields
  have hdom := andLeft (andRight (andRight fields))
  have hfp := andLeft (andRight (andRight (andRight fields)))
  have hap := andRight (andRight (andRight (andRight fields)))
  have har := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 7) d e xs (hq 7) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := binaryRecover InternalPairing.pairing arrowQ (.projection 2)
    (ys 8) (ys 7) fp xs (hq 8) (hq 7) (projectionValue 2 xs)
  have hg := binaryRecover InternalPairing.pairing (.projection 0) (.projection 3)
    (ys 9) d ap xs (hq 9) (projectionValue 0 xs) (projectionValue 3 xs)
  have hfv := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 6) functionQ
    (ys 10) z (ys 8) xs (hq 10) (constantZeroValue xs) (hq 8)
  have hav := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 6) argumentQ
    (ys 11) z (ys 9) xs (hq 11) (constantZeroValue xs) (hq 9)
  have hty := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 12) d e xs (hq 12) (projectionValue 0 xs) (projectionValue 1 xs)
  have hfin := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) typesQ
    (ys 13) (suc z) (ys 12) xs (hq 13) (InternalLessThanSupportProof.oneConstantValue xs) (hq 12)
  have hfw := binaryRecover InternalListCodec.consCode finishQ (.projection 4)
    (ys 14) (ys 13) tail xs (hq 14) (hq 13) (projectionValue 4 xs)
  have haw := binaryRecover InternalListCodec.consCode argumentVisitQ finishWorkQ
    (ys 15) (ys 11) (ys 14) xs (hq 15) (hq 11) (hq 14)
  have hew := binaryRecover InternalListCodec.consCode functionVisitQ argumentWorkQ
    (ys 16) (ys 10) (ys 15) xs (hq 16) (hq 10) (hq 15)
  have hep := binaryRecover InternalPairing.pairing expandedWorkQ (.projection 5)
    (ys 17) (ys 16) results xs (hq 17) (hq 16) (projectionValue 5 xs)
  have he := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) expandedPayloadQ
    (ys 18) (suc z) (ys 17) xs (hq 18) (InternalLessThanSupportProof.oneConstantValue xs) (hq 17)
  have hArrow := binaryValue InternalListCodec.consCode currentDomain currentType (ys 7) d e ss har hdom htype
  have hFunction : Nonempty (Derivation body Gamma (graph1 currentFunction (ys 8) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 8) (ys 7) fp ss hf hArrow hfp
  have hArgument : Nonempty (Derivation body Gamma (graph1 currentArgument (ys 9) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 9) d ap ss hg hdom hap
  have hFV := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1) currentFunction
    (ys 10) z (ys 8) ss hfv (constantZeroValue ss) hFunction
  have hAV := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1) currentArgument
    (ys 11) z (ys 9) ss hav (constantZeroValue ss) hArgument
  have hTypes := binaryValue InternalPairing.pairing currentDomain currentType (ys 12) d e ss hty hdom htype
  have hFinish := binaryValue InternalPairing.pairing (InternalLessThan.constantOne 1) (pairOf currentDomain currentType)
    (ys 13) (suc z) (ys 12) ss hfin (InternalLessThanSupportProof.oneConstantValue ss) hTypes
  have hFW := binaryValue InternalListCodec.consCode (finishOf currentDomain currentType) rest
    (ys 14) (ys 13) tail ss hfw hFinish hrest
  have hAW := binaryValue InternalListCodec.consCode (visitOf currentArgument) (consOf (finishOf currentDomain currentType) rest)
    (ys 15) (ys 11) (ys 14) ss haw hAV hFW
  have hEW := binaryValue InternalListCodec.consCode (visitOf currentFunction)
    (consOf (visitOf currentArgument) (consOf (finishOf currentDomain currentType) rest))
    (ys 16) (ys 10) (ys 15) ss hew hFV hAW
  have hEP := binaryValue InternalPairing.pairing _ InternalApplicationResultStack.results
    (ys 17) (ys 16) results ss hep hEW hresults
  have hExpanded : Nonempty (Derivation body Gamma (graph1 expanded (ys 18) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 18) (suc z) (ys 17) ss he
      (InternalLessThanSupportProof.oneConstantValue ss) hEP
  have rootFields := fieldsAtPairs (.projection 0) (ys 3) (ys 3) d e fp ap
    (ys 0) (ys 1) (ys 2) (projectionValue 0 (Fin.cons (ys 3) Fin.elim0)) hc hb hn ha
  have htagAccept := sameAccept _ (two 1) positionTerm (Fin.cons (ys 3) Fin.elim0)
    (andLeft (andRight rootFields)) (twoValue _)
  have hopen : Nonempty (Derivation body Gamma (graph1 (openGuard guard) (suc z) (ys 3))) :=
    conjunctionAccept _ guard (Fin.cons (ys 3) Fin.elim0) htagAccept hguard'
  have hopenAt := unaryValue (openGuard guard) currentValue (suc z) (ys 3) ss hopen hcurrentValue
  have hFrameAccept := sameAccept frameTag (InternalAcceptance.constantZero 1) z ss hframeTag (constantZeroValue ss)
  have hStatusAccept := sameAccept status (InternalLessThan.constantOne 1) (suc z) ss hstatus
    (InternalLessThanSupportProof.oneConstantValue ss)
  apply successorBranchIntro _ _ _ (ys 18) z ss hStatusAccept
  apply branchValue work (.projection 0) _ (ys 18) (ys 5) state (ys 18) ss hwork (projectionValue 0 ss)
  · apply successorBranchIntro _ _ _ (ys 18) z ss hFrameAccept
    exact successorBranchIntro _ _ _ (ys 18) z ss hopenAt hExpanded
  · exact InternalControlGraphProof.conditionalAtNonzero (ys 5) state (ys 18) (andRight (andRight hd))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitSupportProof
