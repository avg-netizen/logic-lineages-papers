module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixFirstOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixReportsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport programRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody unaryRename)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell packedReports)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaWitnessTerm)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof (LambdaParts lambdaWitnessRename rawLambdaRename)
open NumberedWindowInternalLiteralLambdaLexicalGateProof (exact_OpenLambdaLexicalRowsAt)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof
open NumberedWindowInternalLiteralLambdaPrefixFirstOpenProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem lambdaFields (x d a : OTerm α) (h : D B Γ (eqn x (rawLambdaTerm d a))) :
    D B Γ (unary (field 0) d x) ∧ D B Γ (unary (field 1) a x) := by
  let named := rawLambdaTerm d a
  obtain ⟨literal⟩ := canonicalCell (body := B) (Γ := Γ) (numeral 2) (packedBody [d,a])
  have tail : D B Γ (unary cellTail (packedBody [d,a]) named) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight literal)⟩
  have row := packedReports named cellTail [d,a] tail
  have l : D B Γ (unary (field 0) d named) := row.1
  have r : D B Γ (unary (field 1) a named) := row.2.1
  exact ⟨headTransport (field 0) d named x Fin.elim0 (h.map symm) l,
    headTransport (field 1) a named x Fin.elim0 (h.map symm) r⟩

private theorem witnessField (w inner : OTerm α) (h : D B Γ (eqn w (lambdaWitnessTerm inner))) :
    D B Γ (unary (field 0) inner w) := by
  let named := lambdaWitnessTerm inner
  obtain ⟨literal⟩ := canonicalCell (body := B) (Γ := Γ) (numeral 1) (packedBody [inner])
  have tail : D B Γ (unary cellTail (packedBody [inner]) named) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight literal)⟩
  have row : D B Γ (unary (field 0) inner named) :=
    (packedReports named cellTail [inner] tail).1
  exact headTransport (field 0) inner named w Fin.elim0 (h.map symm) row

/-- Inversion using actual prefix acceptance, not calibration as a
logical equality. The lexical reports come from the very same window
program at both literal body endpoints. -/
theorem exact_OpenPrefixLexicalReportsAt (W : Program 3)
    (c t q w r d a inner e b dom k : OTerm α)
    (head : D B Γ (unary cellHead (numeral 2) q))
    (row : LambdaParts B Γ q w r d a inner e b)
    (gate : D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]))
    (domain : D B Γ (unary cellHead dom t)) (codomain : D B Γ (unary cellTail k t)) :
    D B Γ (eqn t (rawCons d k)) ∧
      D B Γ (windowAt W (rawCons d c) k a) ∧ D B Γ (windowAt W (rawCons d c) k b) ∧
      D B Γ (programGraph (prefixTick W) (prefixStartTerm (rawCons d c) k a inner b) ![prefixStartTerm c t q w r]) := by
  let n := NumberedWindowInternalSparsePair.pairTerm (numeral 1) (packedBody [inner])
  have positive : D B Γ (eqn w (suc n)) := row.witness
  have selected := exact_OpenPrefixTest c t q w r d a inner e b head row
  have accepted := exact_OpenPrefixOwnFirstValidation W c t q w r n positive selected gate
  have a₀ := lambdaFields q d a row.source
  have b₀ := lambdaFields r e b row.target
  have typed := exact_OpenLambdaLexicalRowsAt W c t q w r d a b dom k
    (exact_OpenPrefixValidationRows W c t q w r accepted) a₀.1 a₀.2 b₀.2 domain codomain
  exact ⟨typed.1,typed.2.1,typed.2.2,
    exact_OpenPrefixLifts W c t q w r d k a inner b selected accepted a₀.1 codomain a₀.2
      (witnessField w inner row.witness) b₀.2⟩

#print axioms exact_OpenPrefixLexicalReportsAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixReportsProof
