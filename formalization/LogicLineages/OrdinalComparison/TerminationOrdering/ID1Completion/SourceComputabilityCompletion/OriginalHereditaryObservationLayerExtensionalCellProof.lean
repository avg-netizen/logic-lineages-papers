module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationExtensionalCallProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsObserverCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalCellProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (emb)
open OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceAgreementProof
open OriginalRootObservationExtensional OriginalRootObservationExtensionalCallProof
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsObserverCongruence
open OriginalHereditaryDeletionRowsObserverCongruenceSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem observationForward (Q T : Program 2) (cutoff input parameter out : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement Q T)))
 (ho : Nonempty (Derivation body Delta (graph3 (observation Q) out cutoff input parameter))) :
 Nonempty (Derivation body Delta (graph3 (observation T) out cutoff input parameter)) := by
 let qs : Fin 2 → Program 3 := ![OriginalClassContextAllPositionObserver.erasedPacked,OriginalClassContextAllPositionObserver.erasedParameter]
 let xs : Fin 3 → OTerm alpha := ![cutoff,input,parameter]
 apply queryCases qs xs _
 intro beta rho ys Theta hrho hq
 rw [graph3Rename]
 have hg' := renameInto hg rho Theta hrho
 rw [globalRename] at hg'
 have ho' := renameInto ho rho Theta hrho
 rw [graph3Rename] at ho'
 let xx : Fin 3 → OTerm beta := ![cutoff.relabel rho,input.relabel rho,parameter.relabel rho]
 have he : (fun i => (xs i).relabel rho) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [he] at hq
 have hv := binaryRecover Q (qs 0) (qs 1) (out.relabel rho) (ys 0) (ys 1) xx ho' (hq 0) (hq 1)
 have ht := agreementForward Q T (ys 1) (ys 0) (out.relabel rho) (globalAt Q T (ys 1) hg') hv
 exact binaryValue T (qs 0) (qs 1) (out.relabel rho) (ys 0) (ys 1) xx ht (hq 0) (hq 1)

theorem cells (Q T : Program 2) (count input parameter : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (GlobalAgreement Q T))) :
 Nonempty (Derivation body Delta (CellAgreement Q T count input parameter input parameter)) := by
 unfold CellAgreement
 apply actualFiniteUniversalIntroduction body alpha 3 Delta
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let x := input.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let p := parameter.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
 let i : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let a : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let b : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := cellFields Q T c x p x p i a b
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hg' := renameInto hg Sum.inl Theta (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
 rw [globalRename] at hg'
 have ha := observationForward Q T i x p a hg' (andLeft (andRight hh))
 have he := InternalControlGraphSupportProof.valueUnique (observation T) a b ![i,x,p] ha (andRight (andRight hh))
 rw [← InternalControlGraphSupportProof.equalEqn] at he
 obtain ⟨he⟩ := he
 simpa only [cellBody] using (Nonempty.intro (Derivation.implicationIntroduction he))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalCellProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerExtensionalCellProof
