module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksLogicalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem commonValue (P : Program 1) (left right value mark : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (graph1 P value left)))
 (hr : Nonempty (Derivation body Delta (graph1 P value right))) :
 Nonempty (Derivation body Delta ((graph1 P mark left).iff (graph1 P mark right))) := by
 have hf : Nonempty (Derivation body (graph1 P mark left :: Delta) (graph1 P mark right)) := by
   have hm : Nonempty (Derivation body (graph1 P mark left :: Delta) (graph1 P mark left)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he := valueUnique P value mark (Fin.cons left Fin.elim0) (withHyp hl _) hm
   exact outputTransport P value mark (Fin.cons right Fin.elim0) he (withHyp hr _)
 have hb : Nonempty (Derivation body (graph1 P mark right :: Delta) (graph1 P mark left)) := by
   have hm : Nonempty (Derivation body (graph1 P mark right :: Delta) (graph1 P mark right)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have he := valueUnique P value mark (Fin.cons right Fin.elim0) (withHyp hr _) hm
   exact outputTransport P value mark (Fin.cons left Fin.elim0) he (withHyp hl _)
 obtain ⟨hf⟩ := hf
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩
theorem equalInputs (P : Program 1) (left right mark : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal left right))) :
 Nonempty (Derivation body Delta ((graph1 P mark left).iff (graph1 P mark right))) := by
 rw [equalEqn] at he
 have hf : Nonempty (Derivation body (graph1 P mark left :: Delta) (graph1 P mark right)) :=
   headTransport P mark left right Fin.elim0 (withHyp he _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨he⟩ := he
 have hb : Nonempty (Derivation body (graph1 P mark right :: Delta) (graph1 P mark left)) :=
   headTransport P mark right left Fin.elim0 (withHyp ⟨InternalTagArithmeticSupportProof.symm he⟩ _) ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hf⟩ := hf
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩
theorem equalObservations (left right mark : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal left right))) :
 Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations left right mark)) :=
 andIntro (equalInputs _ left right mark he)
 (andIntro (equalInputs _ left right mark he)
 (andIntro (equalInputs _ left right mark he)
 (andIntro (equalInputs _ left right mark he) (equalInputs _ left right mark he))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksLogicalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksLogicalProof
