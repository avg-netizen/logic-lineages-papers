module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalAbsorbProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationProof
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
open OriginalTypedArgumentObservationsTerminationSyntaxProof

open OriginalTypedArgumentObservationsTerminationSuccessorProof

attribute [local irreducible] walk walkStep

theorem zeroRow (R : Program 2) : Nonempty (Derivation body Delta (terminalRow R z)) := by
 unfold terminalRow
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let raw : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let acc : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let initial : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let B := InternalLessThan.strictLess raw z
 let P := graph2 InternalPairing.pairing initial raw acc
 let G := graph3 (walk R) out z initial parameter
 let Theta := G :: P :: B :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
 obtain ⟨hn⟩ := OriginalHereditaryValidityInternalAbsorbProof.notLessZero (body := body) (Gamma := Theta) raw
 have hb : Derivation body Theta B := Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have h : Derivation body Theta (graph2 (walkStep R) out out parameter) :=
   Derivation.explosion (Derivation.implicationElimination hn hb)
 simpa only [terminalBody,zRelabel] using (Nonempty.intro
   (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))))

theorem successorRow (R : Program 2) (count : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (terminalRow R count))) :
 Nonempty (Derivation body Delta (terminalRow R (suc count))) := by
 unfold terminalRow
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let raw : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let acc : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let initial : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
 let B := InternalLessThan.strictLess raw (suc c)
 let P := graph2 InternalPairing.pairing initial raw acc
 let G := graph3 (walk R) out (suc c) initial parameter
 let Theta := G :: P :: B :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
 have ih := renameInto hrow Sum.inl Theta (fun p hp =>
   List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))))
 rw [terminalRename] at ih
 have hb : Nonempty (Derivation body Theta B) := ⟨Derivation.hypothesis
   (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
 have hp : Nonempty (Derivation body Theta P) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have hg : Nonempty (Derivation body Theta G) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := successorCore R c raw acc initial parameter out ih hb hp hg
 simpa only [terminalBody,sucRelabel] using (Nonempty.intro
   (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))))

theorem allRows (R : Program 2) (count : OTerm alpha) :
 Nonempty (Derivation body Delta (terminalRow R count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := terminalRow R (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,terminalInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) R)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow (body := body) (Delta := theta :: Delta.map weaken)
     R (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,terminalSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,terminalInstantiate,varBind] using (Nonempty.intro h)

theorem rawTermination : OriginalTypedArgumentObservationsTerminationTargets.RawTermination := by
 intro R body alpha Delta count raw acc initial parameter out hb hp hr
 exact terminalApply R count raw acc initial parameter out (allRows R count) hb hp hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationProof
