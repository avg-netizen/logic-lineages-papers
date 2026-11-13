module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseForwardRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseActualRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseStackSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsBranchesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem countTransport (childCount expected deletionCount results first second : OTerm alpha)
    (he : Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn childCount expected)))
    (hv : Nonempty (Derivation body Delta
      (graph3 OriginalHereditaryResultStackProgram.firstSlot first expected deletionCount results ⊓
       graph3 OriginalHereditaryResultStackProgram.secondSlot second expected deletionCount results))) :
    Nonempty (Derivation body Delta
      (graph3 OriginalHereditaryResultStackProgram.firstSlot first childCount deletionCount results ⊓
       graph3 OriginalHereditaryResultStackProgram.secondSlot second childCount deletionCount results)) := by
  obtain ⟨he⟩ := he
  exact InternalApplicationStepPeelSupportProof.andIntro
    (headTransport OriginalHereditaryResultStackProgram.firstSlot first expected childCount
      (Fin.cons deletionCount (Fin.cons results Fin.elim0)) ⟨symm he⟩ (InternalApplicationStepPeelSupportProof.andLeft hv))
    (headTransport OriginalHereditaryResultStackProgram.secondSlot second expected childCount
      (Fin.cons deletionCount (Fin.cons results Fin.elim0)) ⟨symm he⟩ (InternalApplicationStepPeelSupportProof.andRight hv))

 theorem actual : ReverseChildSlotsTargets.ActualSlots := by
  intro body alpha Delta raw childCount deletionCount forwardRow backwardRow deletionPrefix produced old results first second ha hl hrev hd hp hr hf hs
  have hv := OriginalRawSyntaxTransportInternalConstructorArityCasesProof.arityRange raw childCount ha
  apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases hv
  · intro Theta inc he
    have heq : Nonempty (Derivation body Theta (InternalTagArithmeticSyntaxProof.eqn childCount z)) := by
      simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using he
    have hlen := outputTransport length childCount z (Fin.cons forwardRow Fin.elim0) heq
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hl inc)
    have hslots := ReverseChildSlotsBranchesProof.zero deletionCount forwardRow backwardRow deletionPrefix produced old results first second hlen
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hrev inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hd inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hr inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hs inc)
    exact countTransport childCount z deletionCount results first second heq hslots
  · intro Theta inc hrest
    apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases hrest
    · intro Xi inc2 he
      have incl : ∀ f ∈ Delta, f ∈ Xi := fun f hf => inc2 _ (inc f hf)
      have heq : Nonempty (Derivation body Xi (InternalTagArithmeticSyntaxProof.eqn childCount (suc z))) := by
        simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using he
      have hlen := outputTransport length childCount (suc z) (Fin.cons forwardRow Fin.elim0) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hl incl)
      have hslots := ReverseChildSlotsBranchesProof.one deletionCount forwardRow backwardRow deletionPrefix produced old results first second hlen
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hrev incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hd incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hr incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hs incl)
      exact countTransport childCount (suc z) deletionCount results first second heq hslots
    · intro Xi inc2 he
      have incl : ∀ f ∈ Delta, f ∈ Xi := fun f hf => inc2 _ (inc f hf)
      have heq : Nonempty (Derivation body Xi (InternalTagArithmeticSyntaxProof.eqn childCount (suc (suc z)))) := by
        simpa only [equalEqn,SourceComputabilityFormulaSupportProof.numeral] using he
      have hlen := outputTransport length childCount (suc (suc z)) (Fin.cons forwardRow Fin.elim0) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hl incl)
      have hslots := ReverseChildSlotsBranchesProof.two deletionCount forwardRow backwardRow deletionPrefix produced old results first second hlen
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hrev incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hd incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hr incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hs incl)
      exact countTransport childCount (suc (suc z)) deletionCount results first second heq hslots
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsProof.actual
