module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def childrenQ : Program 5 := pairOf (.projection 2) (.projection 3)
def bodyQ : Program 5 := pairOf (.projection 0) childrenQ
def nodeQ : Program 5 := pairOf (two 5) bodyQ
def appQ : Program 5 := pairOf (.projection 1) nodeQ
def workQ : Program 5 := consOf appQ (.projection 4)
def arrowQ : Program 5 := consOf (.projection 0) (.projection 1)
def functionQ : Program 5 := pairOf arrowQ (.projection 2)
def argumentQ : Program 5 := pairOf (.projection 0) (.projection 3)
def suffixQ : Program 5 := consOf argumentQ (.projection 4)
def newWorkQ : Program 5 := consOf functionQ suffixQ
def resultQ : Program 5 := pairOf (InternalLessThan.constantOne 5) newWorkQ
def queries : Fin 11 → Program 5 :=
  ![childrenQ,bodyQ,nodeQ,appQ,workQ,arrowQ,functionQ,argumentQ,suffixQ,newWorkQ,resultQ]

theorem transitionFromQueries (node leaf : Program 1)
    (d e fp ap tail state : OTerm α) (ys : Fin 11 → OTerm α)
    (hstate : Nonempty (Derivation body Gamma
      (InternalApplicationStepPeel.graph5 applicationFrame state d e fp ap tail)))
    (hnode : Nonempty (Derivation body Gamma (graph1 node (suc z) e)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail Fin.elim0)))))))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) (ys 10) state)) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail Fin.elim0))))
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) fp ap xs (hq 0) (projectionValue 2 xs) (projectionValue 3 xs)
  have hb := binaryRecover InternalPairing.pairing (.projection 0) childrenQ
    (ys 1) d (ys 0) xs (hq 1) (projectionValue 0 xs) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (two 5) bodyQ
    (ys 2) positionTerm (ys 1) xs (hq 2) (twoValue xs) (hq 1)
  have ha := binaryRecover InternalPairing.pairing (.projection 1) nodeQ
    (ys 3) e (ys 2) xs (hq 3) (projectionValue 1 xs) (hq 2)
  have hw := binaryRecover InternalListCodec.consCode appQ (.projection 4)
    (ys 4) (ys 3) tail xs (hq 4) (hq 3) (projectionValue 4 xs)
  have har := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 5) d e xs (hq 5) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := binaryRecover InternalPairing.pairing arrowQ (.projection 2)
    (ys 6) (ys 5) fp xs (hq 6) (hq 5) (projectionValue 2 xs)
  have hg := binaryRecover InternalPairing.pairing (.projection 0) (.projection 3)
    (ys 7) d ap xs (hq 7) (projectionValue 0 xs) (projectionValue 3 xs)
  have hsuf := binaryRecover InternalListCodec.consCode argumentQ (.projection 4)
    (ys 8) (ys 7) tail xs (hq 8) (hq 7) (projectionValue 4 xs)
  have hnw := binaryRecover InternalListCodec.consCode functionQ suffixQ
    (ys 9) (ys 6) (ys 8) xs (hq 9) (hq 6) (hq 8)
  have hr := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 5) newWorkQ
    (ys 10) (suc z) (ys 9) xs (hq 10) (InternalLessThanSupportProof.oneConstantValue xs) (hq 9)
  have happ : Nonempty (Derivation body Gamma (programGraph
      (.composition packedApplication ![.projection 0,.projection 1,.projection 2,.projection 3]) (ys 3) xs)) := by
    apply compositionValue packedApplication _ (ys 3) xs
      (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0))))
      (packedAtPairs d e fp ap (ys 0) (ys 1) (ys 2) (ys 3) hc hb hn ha)
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k)))) i
  have hwork : Nonempty (Derivation body Gamma (programGraph
      (consOf (.composition packedApplication ![.projection 0,.projection 1,.projection 2,.projection 3])
        (.projection 4)) (ys 4) xs)) :=
    binaryValue InternalListCodec.consCode _ _ (ys 4) (ys 3) tail xs hw happ (projectionValue 4 xs)
  have hpair := binaryRecover InternalPairing.pairing _ _ state (suc z) (ys 4) xs
    hstate (InternalLessThanSupportProof.oneConstantValue xs) hwork
  have hstatus : Nonempty (Derivation body Gamma (graph1 status (suc z) state)) :=
    pairLeft state (suc z) (ys 4) hpair
  have hwork' : Nonempty (Derivation body Gamma (graph1 work (ys 4) state)) :=
    pairRight state (suc z) (ys 4) hpair
  have hd := InternalListCodecSupportProof.consDestruction (ys 4) (ys 3) tail hw
  have hcurrent : Nonempty (Derivation body Gamma (graph1 current (ys 3) state)) :=
    unaryValue InternalListCodec.headCode work (ys 3) (ys 4) ss (andLeft hd) hwork'
  have hrest : Nonempty (Derivation body Gamma (graph1 rest tail state)) :=
    unaryValue InternalListCodec.tailCode work tail (ys 4) ss (andLeft (andRight hd)) hwork'
  have fields := fieldsAtPairs current state (ys 3) d e fp ap (ys 0) (ys 1) (ys 2)
    hcurrent hc hb hn ha
  have htype := andLeft fields
  have htag := andLeft (andRight fields)
  have hdom := andLeft (andRight (andRight fields))
  have hfp := andLeft (andRight (andRight (andRight fields)))
  have hap := andRight (andRight (andRight (andRight fields)))
  have hArrow := binaryValue InternalListCodec.consCode currentDomain currentType (ys 5) d e ss har hdom htype
  have hFunction : Nonempty (Derivation body Gamma (graph1 currentFunction (ys 6) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 6) (ys 5) fp ss hf hArrow hfp
  have hArgument : Nonempty (Derivation body Gamma (graph1 currentArgument (ys 7) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 7) d ap ss hg hdom hap
  have hSuffix := binaryValue InternalListCodec.consCode currentArgument rest (ys 8) (ys 7) tail ss hsuf hArgument hrest
  have hNewWork := binaryValue InternalListCodec.consCode currentFunction (consOf currentArgument rest)
    (ys 9) (ys 6) (ys 8) ss hnw hFunction hSuffix
  have hExpanded : Nonempty (Derivation body Gamma (graph1 expanded (ys 10) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 10) (suc z) (ys 9) ss hr
      (InternalLessThanSupportProof.oneConstantValue ss) hNewWork
  have hNodeAt := unaryValue node currentType (suc z) e ss hnode htype
  have hNodeAccept := sameAccept _ (InternalLessThan.constantOne 1) (suc z) ss hNodeAt
    (InternalLessThanSupportProof.oneConstantValue ss)
  have hTagAccept := sameAccept currentTag (two 1) positionTerm ss htag (twoValue ss)
  have hStatusAccept := sameAccept status (InternalLessThan.constantOne 1) (suc z) ss hstatus
    (InternalLessThanSupportProof.oneConstantValue ss)
  apply successorBranchIntro _ _ _ (ys 10) z ss hStatusAccept
  apply branchValue work (.projection 0) _ (ys 10) (ys 4) state (ys 10) ss hwork'
    (projectionValue 0 ss)
  · apply successorBranchIntro _ _ _ (ys 10) z ss hTagAccept
    exact successorBranchIntro _ _ _ (ys 10) z ss hNodeAccept hExpanded
  · exact InternalControlGraphProof.conditionalAtNonzero (ys 4) state (ys 10) (andRight (andRight hd))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
