module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceBranchProof InternalStructuralEndpointGuardSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaTraversal (rawTag)
open OriginalLambdaTraversalInternal (otherTag)
open OriginalLambdaTraversalInternalOtherTagProof (constantZeroOneFalse)
open OriginalTransparentLambdaValidityInternal (TagIs)
open OriginalTransparentLambdaValidityInternalBooleanProof (sameReject)
open OriginalTransparentLambdaValidityInternalBranchSupportProof (oneNotTwo)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalHereditaryValidityInternalNodeSupportProof (exactAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Acceptance of the literal existing OTHER AST excludes tag two internally. -/
theorem otherNotTwo (raw : OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (graph1 otherTag (numeral 1) raw))) :
    Nonempty (Derivation body Gamma (TagIs 2 raw).not) := by
  let T := TagIs 2 raw
  have ht : Nonempty (Derivation body (T :: Gamma) T) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hc := sameAccept rawTag (two 1) (numeral 2) (Fin.cons raw Fin.elim0)
    ht (twoValue (Fin.cons raw Fin.elim0))
  obtain ⟨hf⟩ := constantZeroOneFalse (Fin.cons raw Fin.elim0)
    (successorBranchElim _ _ _ (numeral 1) z (Fin.cons raw Fin.elim0)
      hc (addAssumption ho T))
  exact ⟨Derivation.implicationIntroduction hf⟩

/-- The second excluded structural tag comes from the SAME original AST. -/
theorem otherNotOne (raw : OTerm alpha)
    (ho : Nonempty (Derivation body Gamma (graph1 otherTag (numeral 1) raw))) :
    Nonempty (Derivation body Gamma (TagIs 1 raw).not) := by
  let T := TagIs 1 raw
  have ht : Nonempty (Derivation body (T :: Gamma) T) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  let C := graph1 (InternalApplicationStepPeel.same rawTag (two 1)) (numeral 1) raw
  have hn : Nonempty (Derivation body (T :: Gamma) C.not) := by
    obtain ⟨h2⟩ := sameRightRecover rawTag (two 1) (numeral 2) (Fin.cons raw Fin.elim0)
      (show Nonempty (Derivation body (C :: T :: Gamma) C) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩) (twoValue (Fin.cons raw Fin.elim0))
    obtain ⟨hn2⟩ := addAssumption (oneNotTwo raw ht) C
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn2 h2)⟩
  have hc2 := sameReject rawTag (two 1) (Fin.cons raw Fin.elim0) hn
  have hc1 := exactAccept rawTag (Fin.cons raw Fin.elim0) ht
  have hi := zeroBranchElim _ _ _ (numeral 1) (Fin.cons raw Fin.elim0)
    hc2 (addAssumption ho T)
  obtain ⟨hf⟩ := constantZeroOneFalse (Fin.cons raw Fin.elim0)
    (successorBranchElim _ _ _ (numeral 1) z (Fin.cons raw Fin.elim0) hc1 hi)
  exact ⟨Derivation.implicationIntroduction hf⟩

/-- A witnessed original tag inherits either proved exclusion. -/
theorem tagValueNot (k : Nat) (raw tag : OTerm alpha)
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag tag raw)))
    (hn : Nonempty (Derivation body Gamma (TagIs k raw).not)) :
    Nonempty (Derivation body Gamma (equal tag (numeral k)).not) := by
  let E := equal tag (numeral k)
  have he : Nonempty (Derivation body (E :: Gamma) (eqn tag (numeral k))) := by
    simpa only [E,equalEqn] using
      (show Nonempty (Derivation body (E :: Gamma) E) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hgraph⟩ := outputTransport OriginalLambdaConstructor.tag tag (numeral k)
    (Fin.cons raw Fin.elim0) he (addAssumption ht E)
  obtain ⟨hn⟩ := addAssumption hn E
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn hgraph)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalOtherValidityTagProof
