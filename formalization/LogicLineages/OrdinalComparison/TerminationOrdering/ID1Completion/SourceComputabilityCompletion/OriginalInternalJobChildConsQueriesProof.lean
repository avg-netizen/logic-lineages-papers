module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportContextProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open OriginalInternalJobChildPacket OriginalInternalJobChildCasesTargets
open OriginalRawSyntaxTransportInternalParserSupportProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof (stepArrowFieldsRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (argumentsAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem argumentsCases (H : Program 1) (M W : Program 2) (raw gamma c : OTerm alpha) (psi : Formula alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsWitness H M W raw gamma c)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (types : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types (raw.relabel j) (gamma.relabel j) (c.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 obtain ⟨ha⟩ := ha
 apply Nonempty.intro
 apply Derivation.existentialElimination ha
 let Theta : List (Formula (alpha ⊕ Fin 1)) := ArgumentsMatrix H M W raw gamma c :: Delta.map weaken
 have hm : Nonempty (Derivation body Theta (ArgumentsMatrix H M W raw gamma c)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 dsimp only [ArgumentsMatrix] at hm
 exact Classical.choice (next (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)) hm)
theorem consFirstAtFields (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma domain head tail types requested tailTypes : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
 (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma c)))
 (ht : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) : Nonempty (Derivation body Delta psi) := by
 let an : Program 2 := pairOf (constant 2 0) (.projection 1)
 let qs : Fin 3 → Program 2 := ![rightOf (.projection 0),rightOf (rightOf (.projection 0)),an]
 let xs : Fin 2 → OTerm alpha := ![raw,domain]
 apply programsCases qs xs psi
 intro beta j Theta ys hinc hq
 let xx : Fin 2 → OTerm beta := ![raw.relabel j,domain.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [graph3Rename,graph2Rename,argumentsAcceptedRename,stepArrowFieldsRename] at hc' ha' ht' hp' hj'
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.consTag (.projection 0) (raw.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) xx (projectionValue 0 xx) hc'
 have hdomain := OriginalRawSyntaxTransportInternalConstructorFieldsProof.consType (.projection 0) (raw.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) xx (projectionValue 0 xx) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 7) (ys 0)
  (unaryRecover InternalUnpair.left (.projection 0) (numeral 7) (raw.relabel j) xx htag (projectionValue 0 xx))
  (unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xx (hq 0) (projectionValue 0 xx))
 have hdom := selectorPair (rightOf (.projection 0)) (ys 0) (domain.relabel j) (ys 1) xx (hq 0) hdomain (hq 1)
 have hann := binaryRecover InternalPairing.pairing (constant 2 0) (.projection 1) (ys 2) (numeral 0) (domain.relabel j) xx (hq 2) (constantValue 0 xx) (projectionValue 1 xx)
 have packet := OriginalInternalJobChildConsFieldsProof.consFirst H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (ys 0) (ys 1) (domain.relabel j) (head.relabel j) (tail.relabel j)
  (types.relabel j) (requested.relabel j) (tailTypes.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) (ys 2)
  hc' hraw hdom ht' hp' hj' hann ha'
 exact next beta j Theta (numeral 0) (domain.relabel j) (head.relabel j) (gamma.relabel j) (parameter.relabel j) (ys 2) hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
theorem consSecondAtFields (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma domain head tail types requested tailTypes : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
 (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma c)))
 (ht : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 1) role typ raw cell parameter c gamma psi) : Nonempty (Derivation body Delta psi) := by
 let an : Program 2 := pairOf (constant 2 1) (constant 2 0)
 let qs : Fin 3 → Program 2 := ![rightOf (.projection 0),rightOf (rightOf (.projection 0)),an]
 let xs : Fin 2 → OTerm alpha := ![raw,domain]
 apply programsCases qs xs psi
 intro beta j Theta ys hinc hq
 let xx : Fin 2 → OTerm beta := ![raw.relabel j,domain.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [graph3Rename,graph2Rename,argumentsAcceptedRename,stepArrowFieldsRename] at hc' ha' ht' hp' hj'
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.consTag (.projection 0) (raw.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) xx (projectionValue 0 xx) hc'
 have hdomain := OriginalRawSyntaxTransportInternalConstructorFieldsProof.consType (.projection 0) (raw.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) xx (projectionValue 0 xx) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 7) (ys 0)
  (unaryRecover InternalUnpair.left (.projection 0) (numeral 7) (raw.relabel j) xx htag (projectionValue 0 xx))
  (unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xx (hq 0) (projectionValue 0 xx))
 have hdom := selectorPair (rightOf (.projection 0)) (ys 0) (domain.relabel j) (ys 1) xx (hq 0) hdomain (hq 1)
 have hann := binaryRecover InternalPairing.pairing (constant 2 1) (constant 2 0) (ys 2) (numeral 1) (numeral 0) xx (hq 2) (constantValue 1 xx) (constantValue 0 xx)
 have packet := OriginalInternalJobChildConsFieldsProof.consSecond H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (ys 0) (ys 1) (domain.relabel j) (head.relabel j) (tail.relabel j)
  (types.relabel j) (requested.relabel j) (tailTypes.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) (ys 2)
  hc' hraw hdom ht' hp' hj' hann ha'
 exact next beta j Theta (numeral 1) (numeral 0) (tail.relabel j) (gamma.relabel j) (parameter.relabel j) (ys 2) hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsQueriesProof
