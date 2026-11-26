module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineRunStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open InternalApplicationStepPeel (graph5)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawVisitSubstitution {m n : Nat} {gs : Fin n → Program m}
    {d k raw : Program n} {d' k' raw' : Program m}
    (hd : Substitutes gs d d') (hk : Substitutes gs k k') (hr : Substitutes gs raw raw') :
    Substitutes gs (visitOf d k raw) (visitOf d' k' raw') :=
  pairSubstitution (constantZeroSubstitution gs) (pairSubstitution hd (pairSubstitution hk hr))

def initialInputs : Fin 5 → Program 3 :=
  ![.projection 0,.projection 1,.projection 2,constant 3 0,constant 3 0]

theorem initialSubstitution : Substitutes initialInputs visitState initial :=
  liveSubstitution (consSubstitution
    (rawVisitSubstitution (.projection 0) (.projection 1) (.projection 2)) (.projection 3)) (.projection 4)

theorem initialAsVisit (state d k raw : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (graph3 initial state d k raw))) :
    Nonempty (Derivation positive Delta (graph5 visitState state d k raw z z)) := by
  apply (substitutionGraph initialSubstitution ![d,k,raw,z,z] ![d,k,raw] state _).mpr h
  intro i
  exact Fin.cases (projectionValue 0 ![d,k,raw]) (Fin.cases (projectionValue 1 ![d,k,raw])
    (Fin.cases (projectionValue 2 ![d,k,raw])
      (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![d,k,raw])
        (Fin.cases (InternalLessThanSupportProof.zeroConstantValue ![d,k,raw]) (fun j => Fin.elim0 j))))) i

theorem actualFuel (d k raw : OTerm alpha) :
    Nonempty (Derivation positive Delta
      (graph3 fuel (InternalApplicationCertifiedResultFoldClosure.payloadFuel raw) d k raw)) := by
  let xs : Fin 3 → OTerm alpha := ![d,k,raw]
  exact unaryValue .succ (addOf (.projection 2) (.projection 2))
    (suc (add raw raw)) (add raw raw) xs
    (successorValue (Fin.cons (add raw raw) Fin.elim0))
    (binaryValue InternalArithmeticPrograms.addition (.projection 2) (.projection 2)
      (add raw raw) raw raw xs (InternalArithmeticProgramsSupportProof.additionValue raw raw)
      (projectionValue 2 xs) (projectionValue 2 xs))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineRunStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineRunStateProof
