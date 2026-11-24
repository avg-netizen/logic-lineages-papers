module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (Data)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb zRelabel sucRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode scalarLower singletonSubst)

theorem singletonCodeRename {α β : Type} (q : OTerm α) (ρ : α → β) :
    (singletonCode q).relabel ρ = singletonCode (q.relabel ρ) := by
  simp only [singletonCode,rawConsRename,zRelabel]

theorem scalarLowerRename {α β : Type} (S : Data) (c : Nat) (q : OTerm α) (ρ : α → β) :
    (scalarLower S c q).relabel ρ = scalarLower S c (q.relabel ρ) := by
  have subst {γ : Type} (ts : α → OTerm γ) :
      (scalarLower S c q).subst (fun a => emb (ts a)) = scalarLower S c (q.subst ts) := by
    simp only [scalarLower,allEmbeddedSubst,impSubst,edgeSubst,singletonSubst,liftTermSubst] <;> rfl
  rw [formulaRelabelAsSubst]
  change (scalarLower S c q).subst (fun a => emb (.var (ρ a))) = _
  rw [subst,← termRelabelAsSubst]

theorem oddCertificateRename {α β : Type} (S : Data) (c : Nat) (q p w : OTerm α) (ρ : α → β) :
    (certificate S true c q p w).relabel ρ =
      certificate S true c (q.relabel ρ) (p.relabel ρ) (w.relabel ρ) := by
  unfold certificate
  rw [programRename,sucRelabel,zRelabel]
  congr 1
  funext j
  exact Fin.cases (ID1Completion.GuardedSourceSyntaxProof.numeralRename c ρ)
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSyntaxProof
