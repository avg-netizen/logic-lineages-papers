module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel varBind nextTerm)
open InternalTagArithmeticSupportProof (natInduction)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open CountedPrefixSyntax CountedPrefixCore
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let remaining : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let code : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let front : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let suffix : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let A := fields z remaining code front suffix
 obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
   remaining code front suffix ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)
theorem succRow (count : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (row count))) :
 Nonempty (Derivation body Delta (row (suc count))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let remaining : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let code : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let front : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let suffix : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let A := fields (suc c) remaining code front suffix
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have hrow' := renameInto hrow Sum.inl Theta
   (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hrow'
 obtain ⟨h⟩ := succCore c remaining code front suffix hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)
theorem allRows (count : OTerm alpha) : Nonempty (Derivation body Delta (row count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
     (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,rowInstantiate,varBind] using Nonempty.intro h
theorem actualCountedSplit : CountedPrefixTargets.ActualCountedSplit := by
 intro body alpha Delta count remaining code front suffix hl hf hd
 exact rowApply count remaining code front suffix (allRows count) (andIntro hl (andIntro hf hd))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixProof
