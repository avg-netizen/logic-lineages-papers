module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceCellProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalListCodecSupportProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalContextInsertion OriginalContextInsertionSupportProof
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsObserverCongruence
open OriginalHereditaryDeletionRowsObserverCongruenceSyntaxProof
open OriginalHereditaryDeletionRowsObserverCongruenceCellProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem scanZero (Q : Program 2) (input parameter : OTerm alpha) :
 Nonempty (Derivation body Delta (graph3 (scan Q) z z input parameter)) :=
 recursionZeroValue (InternalAcceptance.constantZero 2) (step Q) z ![input,parameter]
   (InternalRawListRecursionSupportProof.constantZero _)

theorem zeroCore (Q T : Program 2) (input parameter other otherParameter left right : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields Q T z input parameter other otherParameter left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 obtain ⟨hl⟩ := valueUnique (scan Q) left z ![z,input,parameter] (andLeft (andRight hf)) (scanZero Q input parameter)
 obtain ⟨hr⟩ := valueUnique (scan T) right z ![z,other,otherParameter] (andRight (andRight hf)) (scanZero T other otherParameter)
 simpa only [equalEqn] using (Nonempty.intro (trans hl (symm hr)))

theorem successorAtValues (Q T : Program 2) (count input parameter other otherParameter left right
 previous value singleton previous2 value2 singleton2 : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row Q T count)))
 (hf : Nonempty (Derivation body Delta (fields Q T (suc count) input parameter other otherParameter left right)))
 (hp : Nonempty (Derivation body Delta (graph3 (scan Q) previous count input parameter)))
 (hv : Nonempty (Derivation body Delta (graph3 (observation Q) value count input parameter)))
 (hc : Nonempty (Derivation body Delta (consGraph singleton value z)))
 (hp2 : Nonempty (Derivation body Delta (graph3 (scan T) previous2 count other otherParameter)))
 (hv2 : Nonempty (Derivation body Delta (graph3 (observation T) value2 count other otherParameter)))
 (hc2 : Nonempty (Derivation body Delta (consGraph singleton2 value2 z))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have hePrev := rowApply Q T count input parameter other otherParameter previous previous2 hi
   (andIntro (restrict Q T count input parameter other otherParameter (andLeft hf)) (andIntro hp hp2))
 have heValue := cellApply Q T (suc count) input parameter other otherParameter count value value2
   (andLeft hf) (andIntro (ownBound count) (andIntro hv hv2))
 rw [equalEqn] at hePrev heValue
 have hc' := binaryInputs InternalListCodec.consCode singleton value z value2 z heValue ⟨refl z⟩ hc
 have heSingle := valueUnique InternalListCodec.consCode singleton singleton2 ![value2,z] hc' hc2
 have ha := OriginalHereditaryDeletionRowsStepProof.scanAppendRecover Q count previous input parameter value singleton left
   hp (andLeft (andRight hf)) hv hc
 have ha2 := OriginalHereditaryDeletionRowsStepProof.scanAppendRecover T count previous2 other otherParameter value2 singleton2 right
   hp2 (andRight (andRight hf)) hv2 hc2
 have ha' := binaryInputs InternalApplicationValidityStackAppend.append left previous singleton previous2 singleton2 hePrev heSingle ha
 simpa only [equalEqn] using valueUnique InternalApplicationValidityStackAppend.append left right ![previous2,singleton2] ha' ha2

theorem successorSecond (Q T : Program 2) (count input parameter other otherParameter left right previous value singleton : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row Q T count)))
 (hf : Nonempty (Derivation body Delta (fields Q T (suc count) input parameter other otherParameter left right)))
 (hp : Nonempty (Derivation body Delta (graph3 (scan Q) previous count input parameter)))
 (hv : Nonempty (Derivation body Delta (graph3 (observation Q) value count input parameter)))
 (hc : Nonempty (Derivation body Delta (consGraph singleton value z))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply OriginalHereditaryDeletionRowsCasesProof.scanCases T count other otherParameter _
 intro beta rho Theta previous2 value2 singleton2 hrho hp2 hv2 hc2
 simp only [equalRename]
 have hi' := renameInto hi rho Theta hrho
 rw [rowRename] at hi'
 have hf' := renameInto hf rho Theta hrho
 simp only [fieldsRename,sucRelabel] at hf'
 have hp' := renameInto hp rho Theta hrho
 rw [graph3Rename] at hp'
 have hv' := renameInto hv rho Theta hrho
 rw [graph3Rename] at hv'
 have hc' := renameInto hc rho Theta hrho
 simp only [consGraphRename,zRelabel] at hc'
 exact successorAtValues Q T (count.relabel rho) (input.relabel rho) (parameter.relabel rho)
   (other.relabel rho) (otherParameter.relabel rho) (left.relabel rho) (right.relabel rho)
   (previous.relabel rho) (value.relabel rho) (singleton.relabel rho) previous2 value2 singleton2
   hi' hf' hp' hv' hc' hp2 hv2 hc2

theorem succCore (Q T : Program 2) (count input parameter other otherParameter left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row Q T count)))
 (hf : Nonempty (Derivation body Delta (fields Q T (suc count) input parameter other otherParameter left right))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply OriginalHereditaryDeletionRowsCasesProof.scanCases Q count input parameter _
 intro beta rho Theta previous value singleton hrho hp hv hc
 simp only [equalRename]
 have hi' := renameInto hi rho Theta hrho
 rw [rowRename] at hi'
 have hf' := renameInto hf rho Theta hrho
 simp only [fieldsRename,sucRelabel] at hf'
 exact successorSecond Q T (count.relabel rho) (input.relabel rho) (parameter.relabel rho)
   (other.relabel rho) (otherParameter.relabel rho) (left.relabel rho) (right.relabel rho)
   previous value singleton hi' hf' hp hv hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceCoreProof
