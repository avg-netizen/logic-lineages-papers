module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverArgumentCellsTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem unaryTapeRename {β : Type} (a : OTerm α) (j : α → β) :
    (fun q : Fin 1 => ((![a] : Fin 1 → OTerm α) q).relabel j) = ![a.relabel j] := by
  funext q
  obtain rfl := Fin.eq_zero q
  rfl

private theorem swapTape (x y : OTerm α) :
    (fun i => (![x,y] : Fin 2 → OTerm α) ((![1,0] : Fin 2 → Fin 2) i)) = ![y,x] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

theorem outerGraph (out ts ars : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph cellsTail out ![ts,ars]))) :
    Nonempty (Derivation body Γ (flatGraph cellBlock out ts ![ars])) := by
  have tape : (![ts,ars] : Fin 2 → OTerm α) = Fin.cons ts ![ars] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [tape] at actual
  exact actual

theorem innerGraph (out q ars : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph cellBlock out ![q,ars]))) :
    Nonempty (Derivation body Γ (flatGraph cellSingle out ars ![q])) := by
  have recovered := recoverReordered (flatMap cellSingle) (![1,0] : Fin 2 → Fin 2) out ![q,ars] actual
  have tape : (fun i => (![q,ars] : Fin 2 → OTerm α) ((![1,0] : Fin 2 → Fin 2) i)) = Fin.cons ars ![q] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [tape] at recovered
  exact recovered

theorem singletonCell (one q a : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph cellSingle one ![a,q]))) :
    Nonempty (Derivation body Γ (consGraph one (rawCons q a) z)) := by
  let xs : Fin 2 → OTerm α := ![a,q]
  have picked : Nonempty (Derivation body Γ (programGraph (reorder fieldCons ![1,0]) (rawCons q a) xs)) := by
    apply compositionValue fieldCons (fun i => .projection ((![1,0] : Fin 2 → Fin 2) i))
      (rawCons q a) xs ![q,a] (NumberedWindowInternalSparsePairGraphProof.consGraph q a)
    intro i
    rw [← swapTape a q]
    exact projectionValue ((![1,0] : Fin 2 → Fin 2) i) xs
  apply compositionRecover consCode
    (Fin.cons (reorder fieldCons ![1,0]) (Fin.cons (constantZero 2) Fin.elim0))
    one xs ![rawCons q a,z] actual
  intro i
  exact Fin.cases picked (Fin.cases (zeroConstantValue xs) (fun j => Fin.elim0 j)) i

theorem sentinelCell (out tail ts ars : OTerm α)
    (whole : Nonempty (Derivation body Γ (cellsReport out ts ars)))
    (folded : Nonempty (Derivation body Γ (programGraph cellsTail tail ![ts,ars]))) :
    Nonempty (Derivation body Γ (consGraph out z tail)) := by
  let xs : Fin 2 → OTerm α := ![ts,ars]
  apply compositionRecover consCode (Fin.cons (constantZero 2) (Fin.cons cellsTail Fin.elim0))
    out xs ![z,tail] whole
  intro i
  exact Fin.cases (zeroConstantValue xs) (Fin.cases folded (fun j => Fin.elim0 j)) i

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsOpenDataProof
