module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAgreementProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open OriginalTypedArgumentObservationsCongruence OriginalTypedArgumentObservationsCongruenceSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem agreementIntro (R S : Program 2) (parameter : OTerm alpha)
 (supply : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (input left right : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (graph2 R left input (parameter.relabel j))) →
  Nonempty (Derivation body Theta (graph2 S right input (parameter.relabel j))) →
  Nonempty (Derivation body Theta (equal left right))) :
 Nonempty (Derivation body Delta (Agreement R S parameter)) := by
 unfold Agreement
 apply actualFiniteUniversalIntroduction body alpha 3 Delta
 let input : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let left : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let right : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let H := graph2 R left input (parameter.relabel Sum.inl) ⊓ graph2 S right input (parameter.relabel Sum.inl)
 let Theta := H :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 obtain ⟨h⟩ := supply (alpha ⊕ Fin 3) Sum.inl Theta input left right
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
   ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
 exact ⟨Derivation.implicationIntroduction h⟩

theorem agreementRefl (R : Program 2) (parameter : OTerm alpha) :
 Nonempty (Derivation body Delta (Agreement R R parameter)) := by
 apply agreementIntro R R parameter
 intro beta j Theta input left right hj hl hr
 simpa only [equalEqn] using valueUnique R left right
   (Fin.cons input (Fin.cons (parameter.relabel j) Fin.elim0)) hl hr

theorem agreementForward (R S : Program 2) (parameter input value : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 R value input parameter))) :
 Nonempty (Derivation body Delta (graph2 S value input parameter)) := by
 apply binaryCases S input parameter _
 intro beta j Theta other hj ho
 rw [graph2Rename]
 have ha' := renameInto ha j Theta hj
 have hv' := renameInto hv j Theta hj
 rw [agreementRename] at ha'
 rw [graph2Rename] at hv'
 obtain ⟨he⟩ := agreementApply R S (parameter.relabel j) (input.relabel j) (value.relabel j) other ha' hv' ho
 have he' : Nonempty (Derivation body Theta (eqn other (value.relabel j))) :=
   ⟨InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using he)⟩
 exact outputTransport S other (value.relabel j)
   (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he' ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceAgreementProof
