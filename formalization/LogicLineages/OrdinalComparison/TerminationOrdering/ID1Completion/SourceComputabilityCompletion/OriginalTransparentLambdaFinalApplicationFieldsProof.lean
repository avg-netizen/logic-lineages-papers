module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeel
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover both type fields and both payloads from the unchanged original packed
application constructor, without interpreting any child as a typed term. -/
theorem packedStateFields (state d e fp ap parent : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 OriginalHereditaryValidity.currentRaw parent state)))
    (hp : Nonempty (Derivation body Delta (graph4 packedApplication parent d e fp ap))) :
    Nonempty (Derivation body Delta
      (graph1 (outerType OriginalHereditaryValidity.currentRaw) e state ⊓
        (graph1 (appDomain OriginalHereditaryValidity.currentRaw) d state ⊓
          (graph1 (functionPayload OriginalHereditaryValidity.currentRaw) fp state ⊓
            graph1 (argumentPayload OriginalHereditaryValidity.currentRaw) ap state)))) := by
  let children : Program 4 := pairOf (.projection 2) (.projection 3)
  let middle : Program 4 := pairOf (.projection 0) children
  let node : Program 4 := pairOf (two 4) middle
  let qs : Fin 3 → Program 4 := ![children,middle,node]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [conjunctionRename,graph1Rename]
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
  have hm := binaryRecover InternalPairing.pairing (.projection 0) children
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (two 4) middle
    (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
  have hpar := binaryRecover InternalPairing.pairing (.projection 1) node
    (parent.relabel j) (e.relabel j) (ys 2) xx hp' (projectionValue 1 xx) (hq 2)
  let ss : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
  have fields := fieldsAtPairs OriginalHereditaryValidity.currentRaw (state.relabel j) (parent.relabel j)
    (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2)
    hr' hc hm hn hpar
  exact andIntro (andLeft fields) (andRight (andRight fields))

open OriginalHereditaryValidity OriginalHereditaryValidityInternalStateSupportProof
open InternalApplicationValidityClosure

theorem currentChildren (state arrow d e fp ap fn arg parent parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (applicationConstructors arrow d e fp ap fn arg parent)))
    (hi : Nonempty (Derivation body Delta (graph2 initial state parent parameter))) :
    Nonempty (Derivation body Delta
      (graph1 currentFunction fn state ⊓ graph1 currentArgument arg state)) := by
  have hr := andLeft (initialSelectors state parent parameter hi)
  have hp := andRight (andRight (andRight hc))
  have fields := packedStateFields state d e fp ap parent hr hp
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hdom : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.domain d parent)) :=
    andRight (OriginalConstructorShapeApplicationProof.packedFields d e fp ap parent hp)
  have hd : Nonempty (Derivation body Delta (graph1 currentDomain d state)) :=
    unaryValue OriginalLambdaConstructor.domain currentRaw d parent xs hdom hr
  have he : Nonempty (Derivation body Delta (graph1 currentType e state)) := andLeft fields
  have har := binaryValue InternalListCodec.consCode currentDomain currentType arrow d e xs (andLeft hc) hd he
  exact andIntro
    (binaryValue InternalPairing.pairing (consOf currentDomain currentType)
      (functionPayload currentRaw) fn arrow fp xs (andLeft (andRight hc)) har
      (andLeft (andRight (andRight fields))))
    (binaryValue InternalPairing.pairing currentDomain (argumentPayload currentRaw)
      arg d ap xs (andLeft (andRight (andRight hc))) hd (andRight (andRight (andRight fields))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationFieldsProof
