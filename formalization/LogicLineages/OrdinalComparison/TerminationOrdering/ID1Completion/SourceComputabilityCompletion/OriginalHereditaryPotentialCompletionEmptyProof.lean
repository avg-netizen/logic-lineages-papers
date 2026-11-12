module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionEmptyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open InternalNumericIteration InternalNumericIterationFixedPointProof
open OriginalHereditaryPotentialCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fixedEmpty (R : Program 2) (input : OTerm alpha)
 (h : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty input))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) input input)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryCombinedStep.work z input)) :=
  unaryValue InternalUnpair.left (.projection 0) z input xs h (projectionValue 0 xs)
 exact InternalAcceptanceBranchProof.zeroBranchIntro OriginalHereditaryCombinedStep.work (.projection 0)
  _ input xs hw (projectionValue 0 xs)
theorem emptyRun (R : Program 2) (fuel input output : OTerm alpha)
 (h : Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty input)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel input))) :
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)) := by
 have hf := fixedValue (OriginalHereditaryCombinedStep.step R) fuel input (fixedEmpty R input h)
 have he := valueUnique (InternalNumericIteration.repeatProgram (OriginalHereditaryCombinedStep.step R)) output input
  (Fin.cons fuel (Fin.cons input Fin.elim0)) hr hf
 obtain ⟨he⟩ := he
 exact headTransport InternalUnpair.left z input output Fin.elim0 (Nonempty.intro (symm he)) h
theorem fromWorkZero (input work results : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (he : Nonempty (Derivation body Delta (eqn work z))) :
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty input)) :=
 outputTransport InternalUnpair.left work z (Fin.cons input Fin.elim0) he (pairLeft input work results hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionEmptyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionEmptyProof
