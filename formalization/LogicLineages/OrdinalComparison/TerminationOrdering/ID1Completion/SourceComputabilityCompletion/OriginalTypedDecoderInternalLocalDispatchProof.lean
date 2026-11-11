module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalTagBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalDispatchSpecificationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLocalDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTypedDecoder OriginalTypedDecoderInternalTagBranchProof
open OriginalTypedDecoderInternalDispatchSpecificationProof OriginalTypedDecoderInternalBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem termLocalForward (H : Program 1) (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state))) :
    ∀ i : Fin 8, Nonempty (Derivation body Delta (graph1 (termCase H i) out state)) →
      Nonempty (Derivation body Delta (termBranchSpec H out g t p suffix i)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ho
    exact OriginalTypedDecoderInternalVariableProof.variableForward state out g t p suffix hg ht hp hr ho
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ho
      exact OriginalTypedDecoderInternalLambdaProof.lambdaForward state out g t p suffix hg ht hp hr ho
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ho
        exact OriginalTypedDecoderInternalApplicationProof.applicationForward state out g t p suffix hg ht hp hr ho
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ho
          exact OriginalTypedDecoderInternalBottomProof.bottomForward state out t p suffix ht hp hr ho
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ho
            exact OriginalTypedDecoderInternalOrdinaryProof.ordinaryForward H state out g t p suffix hg ht hp hr ho
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ho
              exact OriginalTypedDecoderInternalNumberedProof.numberedForward H state out g t p suffix hg ht hp hr ho
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ho
                exact constantForward 0 out (Fin.cons state Fin.elim0) ho
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ho
                  exact constantForward 0 out (Fin.cons state Fin.elim0) ho
                · exact Fin.elim0 i

theorem termLocalBackward (H : Program 1) (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state))) :
    ∀ i : Fin 8, Nonempty (Derivation body Delta (termBranchSpec H out g t p suffix i)) →
      Nonempty (Derivation body Delta (graph1 (termCase H i) out state)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ho
    exact OriginalTypedDecoderInternalVariableProof.variableBackward state out g t p suffix hg ht hp hr ho
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ho
      exact OriginalTypedDecoderInternalLambdaProof.lambdaBackward state out g t p suffix hg ht hp hr ho
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ho
        exact OriginalTypedDecoderInternalApplicationProof.applicationBackward state out g t p suffix hg ht hp hr ho
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ho
          exact OriginalTypedDecoderInternalBottomProof.bottomBackward state out t p suffix ht hp hr ho
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ho
            exact OriginalTypedDecoderInternalOrdinaryProof.ordinaryBackward H state out g t p suffix hg ht hp hr ho
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ho
              exact OriginalTypedDecoderInternalNumberedProof.numberedBackward H state out g t p suffix hg ht hp hr ho
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ho
                exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ho
                  exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
                · exact Fin.elim0 i

theorem argumentsLocalForward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state))) :
    ∀ i : Fin 8, Nonempty (Derivation body Delta (graph1 (argumentsCase i) out state)) →
      Nonempty (Derivation body Delta (argumentsBranchSpec out g t p suffix i)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ho
    exact constantForward 0 out (Fin.cons state Fin.elim0) ho
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ho
      exact constantForward 0 out (Fin.cons state Fin.elim0) ho
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ho
        exact constantForward 0 out (Fin.cons state Fin.elim0) ho
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ho
          exact constantForward 0 out (Fin.cons state Fin.elim0) ho
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ho
            exact constantForward 0 out (Fin.cons state Fin.elim0) ho
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ho
              exact constantForward 0 out (Fin.cons state Fin.elim0) ho
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ho
                exact OriginalTypedDecoderInternalNilProof.nilForward state out t p suffix ht hp hr ho
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ho
                  exact OriginalTypedDecoderInternalConsProof.consForward state out g t p suffix hg ht hp hr ho
                · exact Fin.elim0 i

theorem argumentsLocalBackward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state))) :
    ∀ i : Fin 8, Nonempty (Derivation body Delta (argumentsBranchSpec out g t p suffix i)) →
      Nonempty (Derivation body Delta (graph1 (argumentsCase i) out state)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro ho
    exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
  · 
    refine Fin.cases ?_ (fun i => ?_) i
    · intro ho
      exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
    · 
      refine Fin.cases ?_ (fun i => ?_) i
      · intro ho
        exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
      · 
        refine Fin.cases ?_ (fun i => ?_) i
        · intro ho
          exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
        · 
          refine Fin.cases ?_ (fun i => ?_) i
          · intro ho
            exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
          · 
            refine Fin.cases ?_ (fun i => ?_) i
            · intro ho
              exact constantBackward 0 out (Fin.cons state Fin.elim0) ho
            · 
              refine Fin.cases ?_ (fun i => ?_) i
              · intro ho
                exact OriginalTypedDecoderInternalNilProof.nilBackward state out t p suffix ht hp hr ho
              · 
                refine Fin.cases ?_ (fun i => ?_) i
                · intro ho
                  exact OriginalTypedDecoderInternalConsProof.consBackward state out g t p suffix hg ht hp hr ho
                · exact Fin.elim0 i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLocalDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLocalDispatchProof
