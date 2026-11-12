module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalHereditaryInternalWeightDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalHereditaryInternalWeightValueProof
open InternalAdditionLawsProof (add)

theorem unarySame : OriginalHereditaryInternalWeightTargets.UnarySame := by
 intro body alpha Delta parent child input childRaw gamma len count W V hp hc ha hf hn hl hw hv
 have hparent := OriginalStructuralNodeSizeInternalRecurrenceProof.unary input childRaw count ha hf hn
 exact InternalOriginalPairingOrderArithmeticProof.strictTransport V W (mass len count) (mass len (suc count))
   (weightEqual child childRaw gamma len count V hc hl hn hv)
   (weightEqual parent input gamma len (suc count) W hp hl hparent hw)
   (OriginalHereditaryInternalWeightArithmeticProof.unarySame len count)

theorem unaryExtended : OriginalHereditaryInternalWeightTargets.UnaryExtended := by
 intro body alpha Delta parent child input childRaw gamma childGamma domain len count W V hp hc ha hf hn hl hcons hw hv
 have hparent := OriginalStructuralNodeSizeInternalRecurrenceProof.unary input childRaw count ha hf hn
 have hchildLen := OriginalContextInsertionLengthProof.lengthCons childGamma domain gamma len hcons hl
 exact InternalOriginalPairingOrderArithmeticProof.strictTransport V W (mass (suc len) count) (mass len (suc count))
   (weightEqual child childRaw childGamma (suc len) count V hc hchildLen hn hv)
   (weightEqual parent input gamma len (suc count) W hp hl hparent hw)
   (OriginalHereditaryInternalWeightArithmeticProof.unaryExtended len count)

theorem binaryFirst : OriginalHereditaryInternalWeightTargets.BinaryFirst := by
 intro body alpha Delta parent child input first second gamma len firstCount secondCount W V hp hc ha hf hs hfn hsn hl hw hv
 have hparent := OriginalStructuralNodeSizeInternalRecurrenceProof.binary input first second firstCount secondCount ha hf hs hfn hsn
 exact InternalOriginalPairingOrderArithmeticProof.strictTransport V W (mass len firstCount) (mass len (suc (add firstCount secondCount)))
   (weightEqual child first gamma len firstCount V hc hl hfn hv)
   (weightEqual parent input gamma len (suc (add firstCount secondCount)) W hp hl hparent hw)
   (OriginalHereditaryInternalWeightArithmeticProof.binaryFirst len firstCount secondCount)

theorem binarySecond : OriginalHereditaryInternalWeightTargets.BinarySecond := by
 intro body alpha Delta parent child input first second gamma len firstCount secondCount W V hp hc ha hf hs hfn hsn hl hw hv
 have hparent := OriginalStructuralNodeSizeInternalRecurrenceProof.binary input first second firstCount secondCount ha hf hs hfn hsn
 exact InternalOriginalPairingOrderArithmeticProof.strictTransport V W (mass len secondCount) (mass len (suc (add firstCount secondCount)))
   (weightEqual child second gamma len secondCount V hc hl hsn hv)
   (weightEqual parent input gamma len (suc (add firstCount secondCount)) W hp hl hparent hw)
   (OriginalHereditaryInternalWeightArithmeticProof.binarySecond len firstCount secondCount)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightChildProof
