module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportContextProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open OriginalInternalJobChildPacket OriginalInternalJobChildCasesTargets
open OriginalRawSyntaxTransportInternalParserSupportProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof (stepArrowFieldsRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (argumentsAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (andRight)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
theorem consumerRename (H : Program 1) (M W : Program 2)
 (index role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (next : Consumer body Delta H M W index role typ raw cell parameter c gamma psi)
 {beta : Type} (j : alpha → beta) (Theta : List (Formula beta)) (hj : ∀ f ∈ Delta, f.relabel j ∈ Theta) :
 Consumer body Theta H M W (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (psi.relabel j) := by
 intro gammaType k Xi outRole outType outRaw outGamma outParam annotation hk hpacket
 have incl : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
  intro f hf
  simpa only [← formulaRelabelComposition] using hk _ (hj f hf)
 have h := next gammaType (k ∘ j) Xi outRole outType outRaw outGamma outParam annotation incl
  (by simpa only [Term.relabel_relabel] using hpacket)
 simpa only [formulaRelabelComposition] using h
theorem consFirstCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma domain head tail : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) psi
 intro beta j Theta payload hinc hpayload
 simp only [consTermRename,emptyRename] at hpayload
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [graph3Rename,graph2Rename,admissibleRename] at hc' ha' hp' hj'
 have next' := consumerRename H M W (numeral 0) role typ raw cell parameter c gamma psi next j Theta hinc
 simp only [GuardedSourceSyntaxProof.numeralRename] at next'
 let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.consTag (.projection 0) (raw.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) xs (projectionValue 0 xs) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 7) payload
   (unaryRecover InternalUnpair.left (.projection 0) (numeral 7) (raw.relabel j) xs htag (projectionValue 0 xs)) hpayload
 have hw := andRight (andRight (OriginalInternalJobAdmissibleModeProof.consMode H M W
   (role.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) payload ha' hraw))
 apply OriginalInternalJobChildConsQueriesProof.argumentsCases H M W (raw.relabel j) (gamma.relabel j) (c.relabel j) _ hw
 intro gammaType k Xi types hk haccept
 have hc'' := renameInto hc' k Xi hk
 have hp'' := renameInto hp' k Xi hk
 have hj'' := renameInto hj' k Xi hk
 simp only [graph3Rename,graph2Rename] at hc'' hp'' hj''
 have next'' := consumerRename H M W (numeral 0) (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (psi.relabel j) next' k Xi hk
 simp only [GuardedSourceSyntaxProof.numeralRename] at next''
 apply OriginalTypedDecoderTransportContextProof.arrowCases types _
 intro omega l Omega requested tailTypes hl hfields
 have hc''' := renameInto hc'' l Omega hl
 have hp''' := renameInto hp'' l Omega hl
 have hj''' := renameInto hj'' l Omega hl
 have haccept' := renameInto haccept l Omega hl
 simp only [graph3Rename,graph2Rename,argumentsAcceptedRename] at hc''' hp''' hj''' haccept'
 have next''' := consumerRename H M W (numeral 0) ((role.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k) ((cell.relabel j).relabel k) ((parameter.relabel j).relabel k) ((c.relabel j).relabel k) ((gamma.relabel j).relabel k) ((psi.relabel j).relabel k) next'' l Omega hl
 simp only [GuardedSourceSyntaxProof.numeralRename] at next'''
 exact OriginalInternalJobChildConsQueriesProof.consFirstAtFields H M W
  (((role.relabel j).relabel k).relabel l) (((typ.relabel j).relabel k).relabel l) (((raw.relabel j).relabel k).relabel l) (((cell.relabel j).relabel k).relabel l) (((parameter.relabel j).relabel k).relabel l) (((c.relabel j).relabel k).relabel l) (((gamma.relabel j).relabel k).relabel l) (((domain.relabel j).relabel k).relabel l) (((head.relabel j).relabel k).relabel l) (((tail.relabel j).relabel k).relabel l) (types.relabel l) requested tailTypes _ hc''' haccept' hfields hp''' hj''' next'''
theorem consSecondCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma domain head tail : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 1) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) psi
 intro beta j Theta payload hinc hpayload
 simp only [consTermRename,emptyRename] at hpayload
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [graph3Rename,graph2Rename,admissibleRename] at hc' ha' hp' hj'
 have next' := consumerRename H M W (numeral 1) role typ raw cell parameter c gamma psi next j Theta hinc
 simp only [GuardedSourceSyntaxProof.numeralRename] at next'
 let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.consTag (.projection 0) (raw.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) xs (projectionValue 0 xs) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 7) payload
   (unaryRecover InternalUnpair.left (.projection 0) (numeral 7) (raw.relabel j) xs htag (projectionValue 0 xs)) hpayload
 have hw := andRight (andRight (OriginalInternalJobAdmissibleModeProof.consMode H M W
   (role.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) payload ha' hraw))
 apply OriginalInternalJobChildConsQueriesProof.argumentsCases H M W (raw.relabel j) (gamma.relabel j) (c.relabel j) _ hw
 intro gammaType k Xi types hk haccept
 have hc'' := renameInto hc' k Xi hk
 have hp'' := renameInto hp' k Xi hk
 have hj'' := renameInto hj' k Xi hk
 simp only [graph3Rename,graph2Rename] at hc'' hp'' hj''
 have next'' := consumerRename H M W (numeral 1) (role.relabel j) (typ.relabel j) (raw.relabel j) (cell.relabel j)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (psi.relabel j) next' k Xi hk
 simp only [GuardedSourceSyntaxProof.numeralRename] at next''
 apply OriginalTypedDecoderTransportContextProof.arrowCases types _
 intro omega l Omega requested tailTypes hl hfields
 have hc''' := renameInto hc'' l Omega hl
 have hp''' := renameInto hp'' l Omega hl
 have hj''' := renameInto hj'' l Omega hl
 have haccept' := renameInto haccept l Omega hl
 simp only [graph3Rename,graph2Rename,argumentsAcceptedRename] at hc''' hp''' hj''' haccept'
 have next''' := consumerRename H M W (numeral 1) ((role.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k) ((cell.relabel j).relabel k) ((parameter.relabel j).relabel k) ((c.relabel j).relabel k) ((gamma.relabel j).relabel k) ((psi.relabel j).relabel k) next'' l Omega hl
 simp only [GuardedSourceSyntaxProof.numeralRename] at next'''
 exact OriginalInternalJobChildConsQueriesProof.consSecondAtFields H M W
  (((role.relabel j).relabel k).relabel l) (((typ.relabel j).relabel k).relabel l) (((raw.relabel j).relabel k).relabel l) (((cell.relabel j).relabel k).relabel l) (((parameter.relabel j).relabel k).relabel l) (((c.relabel j).relabel k).relabel l) (((gamma.relabel j).relabel k).relabel l) (((domain.relabel j).relabel k).relabel l) (((head.relabel j).relabel k).relabel l) (((tail.relabel j).relabel k).relabel l) (types.relabel l) requested tailTypes _ hc''' haccept' hfields hp''' hj''' next'''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsCasesProof
