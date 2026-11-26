module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.NumericDependencyCross.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open OriginalContextInsertionSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sourceAt (node param left right : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right))) :
    Nonempty (Derivation body Delta (programGraph source left (Fin.cons node (Fin.cons param Fin.elim0)))) :=
  unaryValue InternalUnpair.left (.projection 0) left node (Fin.cons node (Fin.cons param Fin.elim0))
    (pairLeft node left right hp) (projectionValue 0 (Fin.cons node (Fin.cons param Fin.elim0)))

theorem targetAt (node param left right : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right))) :
    Nonempty (Derivation body Delta (programGraph target right (Fin.cons node (Fin.cons param Fin.elim0)))) :=
  unaryValue InternalUnpair.right (.projection 0) right node (Fin.cons node (Fin.cons param Fin.elim0))
    (pairRight node left right hp) (projectionValue 0 (Fin.cons node (Fin.cons param Fin.elim0)))

theorem sourceAcceptedAt (n : Nat) (node param left right value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) value left))) :
    Nonempty (Derivation body Delta (graph2 (sourceAccepted n) value node param)) :=
  unaryValue (OriginalCodeValidityGuard.check n) source value left (Fin.cons node (Fin.cons param Fin.elim0))
    hv (sourceAt node param left right hp)

theorem targetAcceptedAt (n : Nat) (node param left right value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) value right))) :
    Nonempty (Derivation body Delta (graph2 (targetAccepted n) value node param)) :=
  unaryValue (OriginalCodeValidityGuard.check n) target value right (Fin.cons node (Fin.cons param Fin.elim0))
    hv (targetAt node param left right hp)

theorem zeroNotOne {k : Nat} (p : Program k) (xs : Fin k → OTerm alpha)
    (hz : Nonempty (Derivation body Delta (programGraph p z xs))) :
    Nonempty (Derivation body Delta (programGraph p (suc z) xs).not) := by
  obtain ⟨he⟩ := valueUnique p (suc z) z xs
    (show Nonempty (Derivation body (programGraph p (suc z) xs :: Delta) (programGraph p (suc z) xs)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hz _)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem rejectLeft (n : Nat) (node param : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (graph2 (sourceAccepted n) z node param))) :
    Nonempty (Derivation body Delta (graph2 (accepted n) z node param)) := by
  apply OriginalTransparentLambdaValidityInternalBranchSupportProof.conjunctionReject
    (sourceAccepted n) (targetAccepted n) (Fin.cons node (Fin.cons param Fin.elim0))
  let A := graph2 (accepted n) (suc z) node param
  have h := conjunctionRecover (sourceAccepted n) (targetAccepted n) (Fin.cons node (Fin.cons param Fin.elim0))
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hn⟩ := zeroNotOne (sourceAccepted n) (Fin.cons node (Fin.cons param Fin.elim0)) hz
  obtain ⟨ha⟩ := andLeft h
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
    (InternalBetaTotalityProof.addHyp hn A) ha)⟩

theorem rejectRight (n : Nat) (node param : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (graph2 (targetAccepted n) z node param))) :
    Nonempty (Derivation body Delta (graph2 (accepted n) z node param)) := by
  apply OriginalTransparentLambdaValidityInternalBranchSupportProof.conjunctionReject
    (sourceAccepted n) (targetAccepted n) (Fin.cons node (Fin.cons param Fin.elim0))
  let A := graph2 (accepted n) (suc z) node param
  have h := conjunctionRecover (sourceAccepted n) (targetAccepted n) (Fin.cons node (Fin.cons param Fin.elim0))
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hn⟩ := zeroNotOne (targetAccepted n) (Fin.cons node (Fin.cons param Fin.elim0)) hz
  obtain ⟨ha⟩ := andRight h
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
    (InternalBetaTotalityProof.addHyp hn A) ha)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
