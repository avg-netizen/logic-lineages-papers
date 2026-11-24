module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJUnionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionInnerProgressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalLiteralCarrierProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectTypedListOpenProof (exact_OpenJRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalFunctionalRawUnion (functionalUnion)
open NumberedWindowInternalFunctionalRawUnionReportProof (exact_FunctionalRawUnionReport)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJSpecializedProof (exact_LiteralUnionCarrierSupply)
open NumberedWindowInternalCertifiedUnionStepProof (Pr unionGraph)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (unionGraphRename)

private theorem unionGraphIdentity {α : Type} (a b u : OTerm α) :
    ConditionalJUnionTargets.union functionalUnion a b u =
      programGraph functionalUnion u ![a,b] := rfl

attribute [local irreducible] programGraph

private theorem moveUnion {B : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}
    {Δ : List (Formula β)} (a b u : OTerm α) (j : α → β)
    (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (h : Nonempty (Derivation B Γ (programGraph functionalUnion u ![a,b]))) :
    Nonempty (Derivation B Δ (programGraph functionalUnion (u.relabel j) ![a.relabel j,b.relabel j])) := by
  have moved := renameInto h j Δ keep
  rw [programRename] at moved
  have e : (fun k : Fin 2 => (![a,b] k).relabel j) = ![a.relabel j,b.relabel j] := by
    funext k
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) k
  rw [e] at moved
  exact moved

/-- The two literal carrier reports, not accessibility assumptions,
suffice to validate the actual fixed functional union's carrier. -/
theorem exact_FunctionalLiteralCarrierUnion (i : Program 1) (r : Program 3) (c : Nat) :
    ConditionalJUnionTargets.CarrierUnion (literalData i r) c functionalUnion := by
  intro α Γ a b u ca cb held
  let S := literalData i r
  let B := sourceBody S c
  have heldGraph : Nonempty (Derivation B Γ (programGraph functionalUnion u ![a,b])) := by
    rw [← unionGraphIdentity]
    exact held
  have rawA : Nonempty (Derivation B Γ (unary (jRaw i) (suc z) a)) :=
    (exact_DomainRules i (jRaw i) r (dCore i r permutation) true c B α Γ a).1 ca
  have rawB : Nonempty (Derivation B Γ (unary (jRaw i) (suc z) b)) :=
    (exact_DomainRules i (jRaw i) r (dCore i r permutation) true c B α Γ b).1 cb
  apply exact_LiteralUnionCarrierSupply i r c α Γ a b u ca cb
  apply exact_OpenJRaw i B α Γ a _ rawA
  intro β j Δ sa keep la
  rw [unionGraphRename]
  have rb : Nonempty (Derivation B Δ (unary (jRaw i) (suc z) (b.relabel j))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto rawB j Δ keep
  have go := moveUnion a b u j keep heldGraph
  apply exact_OpenJRaw i B β Δ (b.relabel j) _ rb
  intro γ k Ω sb keep' rr
  rw [unionGraphRename]
  have la' := renameParser (a.relabel j) sa la.parsed k Ω keep'
  have joined := moveUnion (a.relabel j) (b.relabel j) (u.relabel j) k keep' go
  exact exact_FunctionalRawUnionReport ((a.relabel j).relabel k) ((b.relabel j).relabel k)
    ((u.relabel j).relabel k) (sa.relabel k) sb la' rr.parsed joined

#print axioms exact_FunctionalLiteralCarrierUnion
end LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalLiteralCarrierProof
