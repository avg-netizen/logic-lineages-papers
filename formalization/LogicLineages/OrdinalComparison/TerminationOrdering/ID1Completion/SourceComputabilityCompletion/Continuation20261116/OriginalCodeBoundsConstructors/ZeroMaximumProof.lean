module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.FoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MaximumProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ZeroMaximumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel)
open InternalTagArithmeticSupportProof (refl symm)
open InternalSourceInversionSupportProof (onEquality)
open Continuation20261115 OriginalBoundsRecombination
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem secondTransport (p : Program 2) (out a b c : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn b c)))
    (hp : Nonempty (Derivation body Delta (graph2 p out a b))) :
    Nonempty (Derivation body Delta (graph2 p out a c)) := by
  unfold graph2 programGraph at hp ⊢
  apply graphInputTransport body alpha 2 Delta _ out ![a,b] ![a,c] _ hp
  intro i
  fin_cases i
  · rw [onEquality]
    exact ⟨refl _⟩
  · rw [onEquality]
    exact he

theorem leftZero (a : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 maximum a z a)) := by
  apply zeroSuccessorCases Delta a _
  · have he : Nonempty (Derivation body (eqn a z :: Delta) (eqn a z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he'⟩ := he
    have h := secondTransport maximum z z z a ⟨symm he'⟩
      (OriginalEnumerationDepth.CollectProof.maximumZero z)
    exact outputTransport maximum z a ![z,a] ⟨symm he'⟩ h
  · intro beta j Theta v hj he
    simp only [graph2Rename,zRelabel]
    have h := OriginalEnumerationMembership.MaximumProof.rightValue (body := body) (Delta := Theta) z (suc v)
      ⟨InternalQuotientComparisonProof.zeroLessSuccessor v⟩
    obtain ⟨he'⟩ := he
    have ht := secondTransport maximum (suc v) z (suc v) (a.relabel j) ⟨symm he'⟩ h
    exact outputTransport maximum (suc v) (a.relabel j) ![z,a.relabel j] ⟨symm he'⟩ ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ZeroMaximumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ZeroMaximumProof
