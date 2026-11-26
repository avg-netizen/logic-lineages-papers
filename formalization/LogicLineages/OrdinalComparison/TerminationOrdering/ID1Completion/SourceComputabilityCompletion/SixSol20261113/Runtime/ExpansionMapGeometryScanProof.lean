module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm addZero addSucc)
open InternalAdditionLawsProof (add)
open OriginalContextInsertion (lengthGraph)
open ExpansionMapGeometryScanDefinitions ExpansionMapGeometryScanSyntax ExpansionMapGeometryScanRowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalTagArithmeticSyntaxProof (emb zRelabel varBind liftBind nextLift nextTerm bindTerm bindEmbedding nextEmbedding)
open InternalTagArithmeticSupportProof (natInduction)
theorem zeroRow (start role typ raw jobs prefixRow : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefixRow start role typ raw jobs))) :
 Nonempty (Derivation body Delta (row z start role typ raw jobs prefixRow)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 1 Delta
 unfold rowBody
 simp only [zRelabel]
 let full : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
 let A := graph5 OriginalHereditaryAnnotatedExpansion.scan full (add (start.relabel Sum.inl) z)
   (role.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (jobs.relabel Sum.inl)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
 have hp' := renameInto hp Sum.inl Theta (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [graph5Rename] at hp'
 obtain ⟨h⟩ := ExpansionMapGeometryScanCore.zeroCore (start.relabel Sum.inl) (role.relabel Sum.inl)
   (typ.relabel Sum.inl) (raw.relabel Sum.inl) (jobs.relabel Sum.inl) (prefixRow.relabel Sum.inl) full
   hp' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
theorem successorRow (count start role typ raw jobs prefixRow : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count start role typ raw jobs prefixRow))) :
 Nonempty (Derivation body Delta (row (suc count) start role typ raw jobs prefixRow)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 1 Delta
 unfold rowBody
 simp only [sucRelabel]
 let full : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
 let A := graph5 OriginalHereditaryAnnotatedExpansion.scan full (add (start.relabel Sum.inl) (suc (count.relabel Sum.inl)))
   (role.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (jobs.relabel Sum.inl)
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
 have hi' := renameInto hi Sum.inl Theta (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [rowRename] at hi'
 obtain ⟨h⟩ := ExpansionMapGeometryScanQueries.successorCore (count.relabel Sum.inl) (start.relabel Sum.inl)
   (role.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (jobs.relabel Sum.inl) (prefixRow.relabel Sum.inl) full
   hi' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
theorem allRows (count start role typ raw jobs prefixRow : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefixRow start role typ raw jobs))) :
 Nonempty (Derivation body Delta (row count start role typ raw jobs prefixRow)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0)) (start.relabel Sum.inl)
   (role.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (jobs.relabel Sum.inl) (prefixRow.relabel Sum.inl)
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,instantiate,bindEmbedding,rowSubst,varBind,liftBind] using zeroRow start role typ raw jobs prefixRow hp
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow (.var (.inr (0 : Fin 1))) (start.relabel Sum.inl)
     (role.relabel Sum.inl) (typ.relabel Sum.inl) (raw.relabel Sum.inl) (jobs.relabel Sum.inl) (prefixRow.relabel Sum.inl)
     (body := body) (Delta := theta :: Delta.map weaken) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,successorInstance,nextEmbedding,rowSubst,nextLift,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,instantiate,bindEmbedding,rowSubst,varBind,liftBind] using Nonempty.intro h

theorem actualExtension : ExpansionMapGeometryScanTargets.ActualExtension := by
 intro body alpha Delta start count role typ raw jobs prefixRow full hp hf
 exact rowApply count start role typ raw jobs prefixRow full (allRows count start role typ raw jobs prefixRow hp) hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanProof
