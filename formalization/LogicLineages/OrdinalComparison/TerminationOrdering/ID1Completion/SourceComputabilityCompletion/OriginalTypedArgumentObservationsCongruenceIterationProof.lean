module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalAbsorbProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalLessThanSupportProof (oneConstantValue)
open InternalRawListRecursionSupportProof (recursionNext)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTypedArgumentObservationsCongruenceSyntaxProof

open OriginalTypedArgumentObservationsCongruenceIterationCoreProof

attribute [local irreducible] walk walkStep

open OriginalTypedArgumentObservationsCongruence OriginalUniverseDecoderInternalFuelNumericSyntaxProof
theorem zeroRow (R S : Program 2) : Nonempty (Derivation body Delta (iterationRow R S z)) := by
 unfold iterationRow
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let initial : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let left : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let right : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let c : OTerm (alpha ⊕ Fin 4) := z
 let H0 := Agreement R S parameter
 let H1 := repeatGraph R left c initial parameter
 let H2 := repeatGraph S right c initial parameter
 let Theta := H2 :: H1 :: H0 :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have h0 : Nonempty (Derivation body Theta H0) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
 have h1 : Nonempty (Derivation body Theta H1) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have h2 : Nonempty (Derivation body Theta H2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := zeroCore R S initial parameter left right h1 h2
 simpa only [iterationBody,zRelabel] using (Nonempty.intro
   (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))))

theorem successorRow (R S : Program 2) (count : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (iterationRow R S count))) :
 Nonempty (Derivation body Delta (iterationRow R S (suc count))) := by
 unfold iterationRow
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let initial : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let left : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let right : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let H0 := Agreement R S parameter
 let H1 := repeatGraph R left (suc c) initial parameter
 let H2 := repeatGraph S right (suc c) initial parameter
 let Theta := H2 :: H1 :: H0 :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have ih := renameInto hrow Sum.inl Theta (fun p hp => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))))
 rw [iterationRename] at ih
 have h0 : Nonempty (Derivation body Theta H0) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
 have h1 : Nonempty (Derivation body Theta H1) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have h2 : Nonempty (Derivation body Theta H2) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := successorCore R S c initial parameter left right ih h0 h1 h2
 simpa only [iterationBody,sucRelabel] using (Nonempty.intro
   (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))))

theorem allRows (R S : Program 2) (count : OTerm alpha) :
 Nonempty (Derivation body Delta (iterationRow R S count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := iterationRow R S (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,iterationInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) R S)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow (body := body) (Delta := theta :: Delta.map weaken)
     R S (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,iterationSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,iterationInstantiate,varBind] using (Nonempty.intro h)

theorem iterationValues (R S : Program 2) (count initial parameter left right : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (hl : Nonempty (Derivation body Delta (repeatGraph R left count initial parameter)))
 (hr : Nonempty (Derivation body Delta (repeatGraph S right count initial parameter))) :
 Nonempty (Derivation body Delta (equal left right)) :=
 iterationApply R S count initial parameter left right (allRows R S count) ha hl hr

theorem actualIterationCongruence : OriginalTypedArgumentObservationsCongruenceTargets.IterationCongruence := by
 intro R S body alpha Delta count initial parameter left right
 let A := Agreement R S parameter ⊓
   (repeatGraph R left count initial parameter ⊓ repeatGraph S right count initial parameter)
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hv⟩ := iterationValues R S count initial parameter left right
   (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
 exact ⟨Derivation.implicationIntroduction hv⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceIterationProof
