module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelComponentsProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalCanonicalResultFoldOpening
open InternalCanonicalResultFoldOpeningBoundsProof InternalCanonicalResultFoldOpeningQueryProof
open InternalTagArithmeticSyntaxProof (suc z)
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Invert the actual parameterized opening guard using ten original total
queries. No source validity, type, membership or canonicality is required. -/
theorem openingCases (guard : Program 2) (input parameter : OTerm α) (psi : Formula α)
    (hopen : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP guard)
        InternalOriginalStepGuard.one input parameter)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (payload arrow d e fp ap fn arg : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg
          (input.relabel j))) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload (input.relabel j))) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)) →
      Nonempty (Derivation body Delta (InternalLessThan.strictLess fp payload)) →
      Nonempty (Derivation body Delta (InternalLessThan.strictLess ap payload)) →
      Nonempty (Derivation body Delta
        (graph2 guard InternalOriginalStepGuard.one (input.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply queryCases queries (Fin.cons input Fin.elim0) psi
  intro β j ys Delta hj hqueries
  have hopen' := InternalGraphCompositionFunctionalityProof.renameInto hopen j Delta hj
  simp only [graph2Rename, InternalOriginalStepGuard.one,
    InternalTagArithmeticSyntaxProof.sucRelabel, InternalTagArithmeticSyntaxProof.zRelabel] at hopen'
  have hq : ∀ i, Nonempty (Derivation body Delta
      (graph1 (queries i) (ys i) (input.relabel j))) := by
    intro i
    simpa only [consTermRename,emptyRename] using hqueries i
  let xs : Fin 1 → OrdinaryArithmetic.Term β := Fin.cons (input.relabel j) Fin.elim0
  have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (input.relabel j) xs
    (hq 0) (projectionValue 0 xs)
  have hl := unaryRecover InternalUnpair.left (.projection 0) (ys 5) (input.relabel j) xs
    (hq 5) (projectionValue 0 xs)
  have hm := unaryRecover InternalUnpair.right qPayload (ys 1) (ys 0) xs (hq 1) (hq 0)
  have hc := unaryRecover InternalUnpair.right qMiddle (ys 2) (ys 1) xs (hq 2) (hq 1)
  have hd := unaryRecover InternalUnpair.left qMiddle (ys 4) (ys 1) xs (hq 4) (hq 1)
  have hfp := unaryRecover InternalUnpair.left qChildren (ys 6) (ys 2) xs (hq 6) (hq 2)
  have hap := unaryRecover InternalUnpair.right qChildren (ys 7) (ys 2) xs (hq 7) (hq 2)
  have har := binaryRecover InternalListCodec.consCode rootDomain rootCodomain
    (ys 3) (ys 4) (ys 5) xs (hq 3) (hq 4) (hq 5)
  have hfn := binaryRecover InternalPairing.pairing qArrow qFunctionPayload
    (ys 8) (ys 3) (ys 6) xs (hq 8) (hq 3) (hq 6)
  have harg := binaryRecover InternalPairing.pairing rootDomain qArgumentPayload
    (ys 9) (ys 4) (ys 7) xs (hq 9) (hq 4) (hq 7)
  have ho := conjunctionRecover _ _
    (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hopen'
  have htagTest := InternalParameterizedApplicationResultStackWiringProof.liftRecover
    (InternalApplicationStepPeel.same
      (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1))
    (suc z) (input.relabel j) (parameter.relabel j) (andLeft ho)
  have ht := sameRightRecover (InternalApplicationStepPeel.constructorTag (.projection 0))
    (two 1) positionTerm xs htagTest (twoValue xs)
  have htag := unaryRecover InternalUnpair.left qPayload positionTerm (ys 0) xs ht (hq 0)
  have hpv := reconstructPair (input.relabel j) (ys 5) (ys 0) hl hr
  have hpn := reconstructPair (ys 0) positionTerm (ys 1) htag hm
  have hpb := reconstructPair (ys 1) (ys 4) (ys 2) hd hc
  have hpch := reconstructPair (ys 2) (ys 6) (ys 7) hfp hap
  have happ := packedAtPairs (ys 4) (ys 5) (ys 6) (ys 7) (ys 2) (ys 1) (ys 0) (input.relabel j)
    hpch hpb hpn hpv
  have hpay : Nonempty (Derivation body Delta
      (InternalPairingSumBounds.applicationPayloadWitnesses
        (ys 0) (ys 1) (ys 2) (ys 4) (ys 6) (ys 7))) := by
    apply andIntro ?_ (andIntro hpb hpch)
    simpa only [positionTermEq, InternalPairingSumBounds.pairGraph, graph2] using hpn
  have hb := payloadStrictChildren (ys 0) (ys 1) (ys 2) (ys 4) (ys 6) (ys 7) hpay
  exact k β j Delta (ys 0) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) hj
    (andIntro har (andIntro hfn (andIntro harg happ))) hr
    (pairRight (ys 8) (ys 3) (ys 6) hfn)
    (pairRight (ys 9) (ys 4) (ys 7) harg)
    (andLeft hb) (andRight hb) (andRight ho)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
