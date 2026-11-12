module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalHereditaryInternalWeightDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalArithmeticProgramsSupportProof InternalArithmeticProgramsMultiplicationProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add)
open OriginalHereditaryInternalWeightArithmeticProof

theorem weightValue (job raw gamma len count : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields job raw gamma)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len gamma)))
 (hn : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count raw))) :
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight (mass len count) job)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 have hnodes : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.nodes count job)) :=
   unaryValue OriginalStructuralNodeSize.raw rawSelector count raw xs hn (andLeft hf)
 have hlen : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.contextLength len job)) :=
   unaryValue OriginalContextInsertion.length contextSelector len gamma xs hl (andRight hf)
 have hmul : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.multiplication (add count count) (suc (suc z)) count)) :=
   outputTransport InternalArithmeticPrograms.multiplication _ _ (Fin.cons (suc (suc z)) (Fin.cons count Fin.elim0))
     ⟨twoMul count⟩ (multiplicationValue (suc (suc z)) count)
 have htwo : Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.constant 1 2) (suc (suc z)) xs)) :=
   OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 2 xs
 have hd := binaryValue InternalArithmeticPrograms.multiplication (OriginalRawSyntaxTransport.constant 1 2)
   OriginalHereditaryFuelProgram.nodes (add count count) (suc (suc z)) count xs hmul htwo hnodes
 exact binaryValue InternalArithmeticPrograms.addition OriginalHereditaryFuelProgram.contextLength
   (.composition InternalArithmeticPrograms.multiplication ![OriginalRawSyntaxTransport.constant 1 2,OriginalHereditaryFuelProgram.nodes])
   (mass len count) len (add count count) xs (additionValue len (add count count)) hlen hd

theorem weightEqual (job raw gamma len count actual : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields job raw gamma)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len gamma)))
 (hn : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count raw)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight actual job))) :
 Nonempty (Derivation body Delta (eqn actual (mass len count))) := by
 simpa only [equalEqn] using valueUnique OriginalHereditaryFuelProgram.weight actual (mass len count)
   (Fin.cons job Fin.elim0) hw (weightValue job raw gamma len count hf hl hn)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightValueProof
