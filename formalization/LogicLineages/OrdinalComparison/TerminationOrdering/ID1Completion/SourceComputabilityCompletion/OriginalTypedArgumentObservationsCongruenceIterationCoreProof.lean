module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalUniverseDecoderInternalFuelNumericSyntaxProof OriginalUniverseDecoderInternalFuelNumericSupportProof
open OriginalTypedArgumentObservationsWalkQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (R S : Program 2) (initial parameter left right : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (repeatGraph R left z initial parameter)))
 (hr : Nonempty (Derivation body Delta (repeatGraph S right z initial parameter))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 obtain ⟨hl⟩ := repeatZeroRecover R left initial parameter hl
 obtain ⟨hr⟩ := repeatZeroRecover S right initial parameter hr
 simpa only [equalEqn] using (Nonempty.intro
   (InternalTagArithmeticSupportProof.trans hl (InternalTagArithmeticSupportProof.symm hr)))

theorem successorCore (R S : Program 2) (count initial parameter left right : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (iterationRow R S count)))
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (hl : Nonempty (Derivation body Delta (repeatGraph R left (suc count) initial parameter)))
 (hr : Nonempty (Derivation body Delta (repeatGraph S right (suc count) initial parameter))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 apply ternaryCases (repeatProgram R) count initial parameter _
 intro beta j Theta previousR hj hpreviousR
 simp only [equalRename]
 have hpR : Nonempty (Derivation body Theta
   (repeatGraph R previousR (count.relabel j) (initial.relabel j) (parameter.relabel j))) := hpreviousR
 have hi' := renameInto hi j Theta hj
 have ha' := renameInto ha j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [iterationRename] at hi'
 rw [agreementRename] at ha'
 simp only [repeatRename,sucRelabel] at hl' hr'
 apply ternaryCases (repeatProgram S) (count.relabel j) (initial.relabel j) (parameter.relabel j) _
 intro gamma k Xi previousS hk hpreviousS
 simp only [equalRename]
 have hpS : Nonempty (Derivation body Xi
   (repeatGraph S previousS ((count.relabel j).relabel k) ((initial.relabel j).relabel k) ((parameter.relabel j).relabel k))) := hpreviousS
 have hpR' := renameInto hpR k Xi hk
 have hi'' := renameInto hi' k Xi hk
 have ha'' := renameInto ha' k Xi hk
 have hl'' := renameInto hl' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 rw [repeatRename] at hpR'
 rw [iterationRename] at hi''
 rw [agreementRename] at ha''
 simp only [repeatRename,sucRelabel] at hl'' hr''
 have he := iterationApply R S ((count.relabel j).relabel k) ((initial.relabel j).relabel k)
   ((parameter.relabel j).relabel k) (previousR.relabel k) previousS hi'' ha'' hpR' hpS
 have hstepR := repeatSuccRecover R ((count.relabel j).relabel k) (previousR.relabel k)
   ((left.relabel j).relabel k) ((initial.relabel j).relabel k) ((parameter.relabel j).relabel k) hpR' hl''
 have hstepS := repeatSuccRecover S ((count.relabel j).relabel k) previousS
   ((right.relabel j).relabel k) ((initial.relabel j).relabel k) ((parameter.relabel j).relabel k) hpS hr''
 have he' : Nonempty (Derivation body Xi (eqn previousS (previousR.relabel k))) := by
   obtain ⟨he⟩ := he
   exact ⟨InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using he)⟩
 have hstepS' := headTransport S ((right.relabel j).relabel k) previousS (previousR.relabel k)
   (Fin.cons ((parameter.relabel j).relabel k) Fin.elim0) he' hstepS
 exact agreementApply R S ((parameter.relabel j).relabel k) (previousR.relabel k)
   ((left.relabel j).relabel k) ((right.relabel j).relabel k) ha'' hstepR hstepS'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationCoreProof
