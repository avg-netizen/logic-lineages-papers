module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandGuardsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMemoChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkRetapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding liftBind varBind)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.SourcePresentation (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralAtomicAddressReportProof (rebuildAddress)
open NumberedWindowInternalNeutralFactsTargets (direct directData)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenStrictRetapeContext (L : Program 3) (source destination ty raw out : OTerm α)
    (coord : D B Γ (eqn source destination))
    (held : D B Γ (programGraph L out ![source,ty,raw])) :
    D B Γ (programGraph L out ![destination,ty,raw]) := by
  unfold programGraph at held ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula L) out ![source,ty,raw] ![destination,ty,raw] _ held
  intro i
  rw [onEquality]
  exact Fin.cases coord (Fin.cases (⟨refl ty⟩ : D B Γ (eqn ty ty))
    (Fin.cases (⟨refl raw⟩ : D B Γ (eqn raw raw)) (fun a => Fin.elim0 a))) i

theorem exact_OpenStrictArrowRetape (a b c d : OTerm α)
    (left : D B Γ (eqn a c)) (right : D B Γ (eqn b d)) :
    D B Γ (eqn (rawCons a b) (rawCons c d)) := by
  have source : D B Γ (programGraph fieldCons (rawCons a b) ![a,b]) := consGraph a b
  have target : D B Γ (programGraph fieldCons (rawCons a b) ![c,d]) := by
    unfold programGraph at source ⊢
    apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula fieldCons)
      (rawCons a b) ![a,b] ![c,d] _ source
    intro i
    rw [onEquality]
    exact Fin.cases left (Fin.cases right (fun j => Fin.elim0 j)) i
  exact valueUnique fieldCons (rawCons a b) (rawCons c d) ![c,d] target (consGraph c d)

theorem exact_OpenStrictMemberRetape (finite : List Nat) (source destination : OTerm α)
    (types : D B Γ (eqn source destination))
    (held : D B Γ (literalMembership finite source)) : D B Γ (literalMembership finite destination) := by
  let code : OTerm α := SourceComputabilityFormulaSupportProof.numeral (Encodable.encode finite)
  unfold literalMembership memberGraph at held ⊢
  unfold programGraph at held ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula scratchMember)
    (suc z) ![code,source] ![code,destination] _ held
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl code⟩ : D B Γ (eqn code code)) (Fin.cases types (fun j => Fin.elim0 j)) i

theorem exact_OpenStrictChildFunctionAddress (x u ctx result dom cod fn arg sc d e : OTerm α)
    (parsed : D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg))
    (scope : D B Γ (eqn ctx sc)) (type : D B Γ (eqn (rawCons dom cod) (rawCons d e))) :
    D B Γ (eqn x (literalAddress sc (rawCons d e) fn)) := by
  obtain ⟨all⟩ := parsed
  let uRows := Derivation.conjunctionRight all
  let arrowRows := Derivation.conjunctionRight uRows
  let fRows := Derivation.conjunctionRight arrowRows
  let aRows := Derivation.conjunctionRight fRows
  let cords := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight aRows))
  have addr : D B Γ (addressReport x ctx result fn) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft all) (Derivation.conjunctionLeft fRows)⟩
  obtain ⟨t⟩ := type
  have atType : D B Γ (eqn result (rawCons d e)) :=
    ⟨ID1Completion.InternalTagArithmeticSupportProof.trans (Derivation.conjunctionLeft cords) t⟩
  exact rebuildAddress x ctx result fn sc (rawCons d e) fn addr scope atType ⟨refl fn⟩

theorem exact_OpenStrictRetapeDirectSource (S : Data) (hop : Program 3) (c : Nat) (source destination y : OTerm α)
    (same : D B Γ (eqn source destination)) (held : D B Γ (direct S hop c source y)) :
    D B Γ (direct S hop c destination y) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let φ : Formula (α ⊕ Fin 1) := direct S hop c (.var (.inr 0)) (y.relabel j)
  have inst (x : OTerm α) : instantiate φ (emb x) = direct S hop c x y := by
    simp only [φ,direct,instantiate,bindEmbedding,edgeSubst,varBind,j,liftBind]
  obtain ⟨h⟩ := held
  obtain ⟨e⟩ := same
  have converted := Derivation.equalityElimination φ (emb source) (emb destination) e (by rw [inst]; exact h)
  rw [inst] at converted
  exact ⟨converted⟩

#print axioms exact_OpenStrictRetapeContext
#print axioms exact_OpenStrictArrowRetape
#print axioms exact_OpenStrictMemberRetape
#print axioms exact_OpenStrictChildFunctionAddress
#print axioms exact_OpenStrictRetapeDirectSource
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkRetapeProof
