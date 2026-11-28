module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixRawFitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixNonLambdaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixHopProjectionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof (acceptCalls)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalParameterizedAddressPositive (exact_OriginalAddressAt)
open NumberedWindowInternalOriginalFirstHopCoreProof
  (D oneHopProgram exact_OriginalAddressAtIntro exact_OriginalPositiveOneCell exact_OneHopProgramIntro)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget targetGate)
open NumberedWindowInternalLiteralLambdaPrefixRawFitProof (prefixRaw exact_OpenPrefixRaw)
open NumberedWindowInternalLiteralLambdaPrefixNonLambdaProof (exact_OpenPrefixRawNonLambda)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem replaceRawCall (i cv tv : Program 1) (raw raw' : Program 5) (L : Program 3)
    (ctx ty before hd after q w r : OTerm α)
    (held : D B Γ (hopCalls (rawWithTarget i cv tv raw L) L ctx ty before hd after q w r))
    (move : D B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r]) →
      D B Γ (programGraph raw' (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (hopCalls (rawWithTarget i cv tv raw' L) L ctx ty before hd after q w r) := by
  let gate := targetGate i cv tv L
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  obtain ⟨row⟩ := held
  let calls := Derivation.conjunctionRight row
  obtain ⟨selected⟩ := conjunctionRecover raw gate xs ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨moved⟩ := conjunctionAccept raw' gate xs (move ⟨Derivation.conjunctionLeft selected⟩)
    ⟨Derivation.conjunctionRight selected⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft row)
    (Derivation.conjunctionIntroduction moved (Derivation.conjunctionRight calls))⟩

/-- Project a prefix-certified hop report onto the unprefixed checker in
the same derivation context. The original hop, target gate and both
least calls are retained. -/
theorem exact_OpenLambdaPrefixHopReports (i cv tv : Program 1) (W : Program 3)
    (raw : Program 5) (L : Program 3) (ctx ty before hd after q w r : OTerm α)
    (held : D B Γ (hopCalls (rawWithTarget i cv tv (prefixRaw W raw) L) L ctx ty before hd after q w r)) :
    D B Γ (hopCalls (rawWithTarget i cv tv raw L) L ctx ty before hd after q w r) :=
  replaceRawCall i cv tv (prefixRaw W raw) raw L ctx ty before hd after q w r held
    (fun live => ((exact_OpenPrefixRaw W raw ![ctx,ty,q,w,r]).mp live).1)

/-- At a non-lambda source the original prefix program accepts the same
hop. The proof uses the selector's actual header and reuses every report
other than the raw call. -/
theorem exact_OpenLambdaPrefixHopReportsOfNonLambda (i cv tv : Program 1) (W : Program 3)
    (raw : Program 5) (L : Program 3) (ctx ty before hd after q w r tag : OTerm α)
    (header : D B Γ (unary cellHead tag q))
    (nonLambda : D B Γ (eqn tag (numeral 2 : OTerm α)).not)
    (held : D B Γ (hopCalls (rawWithTarget i cv tv raw L) L ctx ty before hd after q w r)) :
    D B Γ (hopCalls (rawWithTarget i cv tv (prefixRaw W raw) L) L ctx ty before hd after q w r) :=
  replaceRawCall i cv tv raw (prefixRaw W raw) L ctx ty before hd after q w r held
    (exact_OpenPrefixRawNonLambda W raw ctx ty q w r tag header nonLambda)

/-- The unprefixed one-hop program accepts the same literal hop and the
same addressed endpoints, in the arithmetic body of the supplied reports. -/
theorem exact_OpenLambdaPrefixOneHopProjection (i cv tv : Program 1) (W : Program 3)
    (raw : Program 5) (L : Program 3) (x y ctx ty before hd after q w r : OTerm α)
    (left : D B Γ (addressReport x ctx ty before)) (right : D B Γ (addressReport y ctx ty after))
    (context : D B Γ (unary cv (suc z) ctx)) (type : D B Γ (unary tv (suc z) ty))
    (held : D B Γ (hopCalls (rawWithTarget i cv tv (prefixRaw W raw) L) L ctx ty before hd after q w r)) :
    D B Γ (programGraph (oneHopProgram (addressPositive cv tv (rawWithTarget i cv tv raw L) L))
      (suc z) ![x,hd,y]) := by
  let R := rawWithTarget i cv tv raw L
  have reported := exact_OpenLambdaPrefixHopReports i cv tv W raw L ctx ty before hd after q w r held
  have advanced := acceptCalls R L ctx ty before hd after q w r reported
  have one := exact_OriginalPositiveOneCell R L ctx ty before hd after advanced
  have path : D B Γ (programGraph (addressPositive cv tv R L) (suc z) ![x,rawCons hd z,y]) := by
    rw [← exact_OriginalAddressAt]
    exact exact_OriginalAddressAtIntro cv tv (positive R L) x (rawCons hd z) y ctx ty before after
      left right context type one
  exact exact_OneHopProgramIntro (addressPositive cv tv R L) x hd y path

#print axioms exact_OpenLambdaPrefixHopReports
#print axioms exact_OpenLambdaPrefixHopReportsOfNonLambda
#print axioms exact_OpenLambdaPrefixOneHopProjection
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixHopProjectionProof
