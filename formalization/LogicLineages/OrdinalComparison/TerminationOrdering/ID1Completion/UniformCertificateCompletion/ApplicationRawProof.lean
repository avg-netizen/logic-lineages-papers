module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationTypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationRawProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open UniformCertificateCompletion.SupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Query the source tag internally and identify it with the SUPPLIED
canonical source type using the actual canonical fold's invariant. -/
theorem sourceRawTag (data : Data) (oldStep : Program 4)
    (x y s t k typ parameter : OTerm α)
    (ht : Nonempty (Derivation body Delta (typedAccepted data x typ parameter)))
    (he : Nonempty (Derivation body Delta (requirements data oldStep x y s t k parameter))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)) := by
  apply programCases InternalUnpair.left (Fin.cons s Fin.elim0)
    (graph1 InternalUnpair.left typ s)
  intro β j Theta tag hj hl
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hl
  have ht' := renameInto ht j Theta hj
  rw [typedRename] at ht'
  have he' := renameInto he j Theta hj
  rw [requirementsRename] at he'
  obtain ⟨hs,_,_⟩ := TypingProof.stepParts data oldStep (s.relabel j) (t.relabel j)
    (k.relabel j) (parameter.relabel j) (andLeft he')
  have hn := TypingProof.sourceFold data (x.relabel j) (s.relabel j) (parameter.relabel j)
    hs (andLeft (andRight he'))
  obtain ⟨consumer⟩ := InternalParameterizedCanonicalResultFoldProof.actualParameterizedCanonicalFoldOutputInvariant
    body data β Theta (x.relabel j) (s.relabel j) tag (parameter.relabel j)
  obtain ⟨hp⟩ := andIntro hs hl
  obtain ⟨hn'⟩ := hn
  have ho := (⟨Derivation.implicationElimination
    (Derivation.implicationElimination consumer hp) hn'⟩ :
    Nonempty (Derivation body Theta (InternalParameterizedCanonicalResultFold.successfulOutput data
      (x.relabel j) (s.relabel j) tag (parameter.relabel j))))
  have hf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover data.oldRepresentative
    (validity data) data.member (x.relabel j) (typ.relabel j) (parameter.relabel j) ht'
  have heq := valueUnique InternalUnpair.left tag (typ.relabel j) (Fin.cons (x.relabel j) Fin.elim0)
    (andLeft (andRight (andRight ho))) (andLeft (andRight (andRight hf)))
  exact outputTransport InternalUnpair.left tag (typ.relabel j)
    (Fin.cons (s.relabel j) Fin.elim0) heq hl

/-- Source validity already contains the original packed-target validator
as its FIRST literal conjunct, independently of any semantic calibration. -/
theorem targetFromSource (data : Data) (x parameter : OTerm α)
    (h : Nonempty (Derivation body Delta (graph2 (validity data) (suc z) x parameter))) :
    Nonempty (Derivation body Delta (graph2 (targetValidity data) (suc z) x parameter)) :=
  andLeft (InternalAcceptanceConjunctionProof.conjunctionRecover
    (InternalParameterizedApplicationValidityFold.targetP data.oldTarget)
    (InternalParameterizedApplicationValidityFold.universeP data.oldSource data.member)
    (Fin.cons x (Fin.cons parameter Fin.elim0)) h)

/-- The original seven-test endpoint follows from the SAME raw edge,
typed canonical source/argument and symbolic context pair. In particular,
codomain membership and both raw function tags are conclusions. -/
theorem endpointFromCore (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (oldStep : Program 4) (sigma tau : Ty)
    (x y a certificate out other s t k parameter gammaCode : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (Application.parameterPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (normalizeData base) oldStep sigma tau x y a certificate out other parameter gammaCode)))
    (he : Nonempty (Derivation body Delta
      (requirements (normalizeData base) oldStep x y s t k parameter))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedStructuralEndpointGuard.accepted
        (validity (normalizeData base)) (targetValidity (normalizeData base)) (normalizeData base).member
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) s t a parameter)) := by
  let data := normalizeData base
  let arrow : OTerm α := numeral (typeNumber (.arrow sigma tau))
  let d : OTerm α := numeral (typeNumber sigma)
  let e : OTerm α := numeral (typeNumber tau)
  have hpair := andLeft hp
  have hcore := andRight hp
  have hx := andLeft hcore
  have ha := andLeft (andRight hcore)
  obtain ⟨hvs,hvt,htags⟩ := TypingProof.stepParts data oldStep s t k parameter (andLeft he)
  have hs := sourceRawTag data oldStep x y s t k arrow parameter hx he
  have ht := TypingProof.targetTag s t k arrow parameter htags hs
  have hf := InternalOriginalUniformDescentSelectionInternalProof.typedRecover data.oldRepresentative
    (validity data) data.member x arrow parameter hx
  have harg := InternalOriginalUniformDescentSelectionInternalProof.typedRecover data.oldRepresentative
    (validity data) data.member a d parameter ha
  have hm := InternalOriginalUniformApplicationTypingMembershipProof.codomainMembership
    n arity base hc symbols S table hS sigma tau parameter gammaCode hpair (andLeft hf)
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral (body := body) (Gamma := Delta) (α := α) sigma tau
  exact InternalParameterizedStructuralEndpointGuardSupportProof.endpointAccept
    (validity data) (targetValidity data) data.member arrow d e s t a parameter har
    (andIntro hvs (andIntro (targetFromSource data t parameter hvt)
      (andIntro (andLeft (andRight harg))
        (andIntro (andIntro hs (andIntro ht (andLeft (andRight (andRight harg))))) hm))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationRawProof
