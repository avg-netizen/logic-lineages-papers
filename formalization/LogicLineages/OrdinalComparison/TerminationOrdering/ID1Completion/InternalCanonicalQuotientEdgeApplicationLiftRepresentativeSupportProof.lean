module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalApplicationStepPeelComponentsProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalCanonicalResultFoldOpening
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Construct the literal G from its four independent original facts. -/
theorem packedGuard (V member : Program 1) (arrow d e fp ap f a parent : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing f arrow fp)))
    (ha : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing a d ap)))
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hv : Nonempty (Derivation body Gamma (graph1 V (suc z) parent)))
    (hvf : Nonempty (Derivation body Gamma (graph1 V (suc z) f)))
    (hva : Nonempty (Derivation body Gamma (graph1 V (suc z) a)))
    (hm : Nonempty (Derivation body Gamma (graph1 member (suc z) e))) :
    Nonempty (Derivation body Gamma (graph1 (rootGuard V member) (suc z) parent)) := by
  let ch : Program 4 := pairOf (.projection 2) (.projection 3)
  let mid : Program 4 := pairOf (.projection 0) ch
  let pay : Program 4 := pairOf (two 4) mid
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases (![ch,mid,pay] : Fin 3 → Program 4) xs _
  intro β j ys Delta hj hq
  simp only [graph1Rename,sucRelabel,zRelabel]
  have har' := renameInto har j Delta hj
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  have hp' := renameInto hp j Delta hj
  have hv' := renameInto hv j Delta hj
  have hvf' := renameInto hvf j Delta hj
  have hva' := renameInto hva j Delta hj
  have hm' := renameInto hm j Delta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel] at har' hf' ha' hp' hv' hvf' hva' hm'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm β := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
  have hb := binaryRecover InternalPairing.pairing (.projection 0) ch
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (two 4) mid
    (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
  have ho := binaryRecover InternalPairing.pairing (.projection 1) pay
    (parent.relabel j) (e.relabel j) (ys 2) xx hp' (projectionValue 1 xx) (hq 2)
  let ss : Fin 1 → OTerm β := Fin.cons (parent.relabel j) Fin.elim0
  have fields := fieldsAtPairs (.projection 0) (parent.relabel j) (parent.relabel j)
    (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2)
    (projectionValue 0 ss) hc hb hn ho
  have he := andLeft fields
  have hd := andLeft (andRight (andRight fields))
  have hfp := andLeft (andRight (andRight (andRight fields)))
  have hap := andRight (andRight (andRight (andRight fields)))
  have harrow := binaryValue InternalListCodec.consCode rootDomain rootCodomain
    (arrow.relabel j) (d.relabel j) (e.relabel j) ss har' hd he
  have hfn := binaryValue InternalPairing.pairing (consOf rootDomain rootCodomain)
    (InternalApplicationStepPeel.functionPayload (.projection 0))
    (f.relabel j) (arrow.relabel j) (fp.relabel j) ss hf' harrow hfp
  have harg := binaryValue InternalPairing.pairing rootDomain
    (InternalApplicationStepPeel.argumentPayload (.projection 0))
    (a.relabel j) (d.relabel j) (ap.relabel j) ss ha' hd hap
  exact conjunctionAccept _ _ ss hv'
    (conjunctionAccept _ _ ss (unaryValue V functionChild (suc z) (f.relabel j) ss hvf' hfn)
      (conjunctionAccept _ _ ss (unaryValue V argumentChild (suc z) (a.relabel j) ss hva' harg)
        (unaryValue member rootCodomain (suc z) (e.relabel j) ss hm' he)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftRepresentativeSupportProof
