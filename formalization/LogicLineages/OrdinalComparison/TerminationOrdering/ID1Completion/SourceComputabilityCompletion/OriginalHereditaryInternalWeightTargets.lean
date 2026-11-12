module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalHereditaryInternalWeightDefinitions
/-- Allraw guarded ranking only; actual expansion inversion is separate. -/
def UnarySame : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child input childRaw gamma len count W V : OTerm alpha),
 Nonempty (Derivation body Delta (fields parent input gamma)) →
 Nonempty (Derivation body Delta (fields child childRaw gamma)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (suc z) input)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) childRaw input)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count childRaw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF V W))
def UnaryExtended : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child input childRaw gamma childGamma domain len count W V : OTerm alpha),
 Nonempty (Derivation body Delta (fields parent input gamma)) →
 Nonempty (Derivation body Delta (fields child childRaw childGamma)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (suc z) input)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) childRaw input)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count childRaw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma domain gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF V W))
def BinaryFirst : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child input first second gamma len firstCount secondCount W V : OTerm alpha),
 Nonempty (Derivation body Delta (fields parent input gamma)) →
 Nonempty (Derivation body Delta (fields child first gamma)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (suc (suc z)) input)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first input)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second input)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw firstCount first)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw secondCount second)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF V W))
def BinarySecond : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child input first second gamma len firstCount secondCount W V : OTerm alpha),
 Nonempty (Derivation body Delta (fields parent input gamma)) →
 Nonempty (Derivation body Delta (fields child second gamma)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (suc (suc z)) input)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first input)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second input)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw firstCount first)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw secondCount second)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF V W))
def Deletion : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child input erased gamma deleted typ cutoff count before after W V : OTerm alpha),
 Nonempty (Derivation body Delta (fields parent input gamma)) →
 Nonempty (Derivation body Delta (fields child erased deleted)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased typ cutoff input)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw before input)) →
 Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw after erased)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc count) gamma)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff (suc count))) →
 Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF V W))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightTargets
