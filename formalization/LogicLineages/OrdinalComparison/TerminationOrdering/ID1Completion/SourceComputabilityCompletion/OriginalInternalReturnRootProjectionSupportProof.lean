module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationCoordinatesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesElim)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consRecover {n : Nat} (p q : Program n) (out x y : OTerm alpha) (xs : Fin n → OTerm alpha)
 (ho : Nonempty (Derivation body Delta (programGraph (consOf p q) out xs)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out x y))) :
 Nonempty (Derivation body Delta ((programGraph p x xs) ⊓ (programGraph q y xs))) := by
 apply programCompositionCases InternalListCodec.consCode ![p,q] out xs _ ho
 intro beta rho ys Theta hrho hcons hs
 simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,programRename]
 have hc' := renameInto hc rho Theta hrho
 rw [graph2Rename] at hc'
 have hcons' : Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (out.relabel rho) (ys 0) (ys 1))) := by
   have htuple : Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
     funext i
     exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
   simpa only [graph2,htuple] using hcons
 have hx := valueUnique InternalListCodec.headCode (ys 0) (x.relabel rho) (Fin.cons (out.relabel rho) Fin.elim0)
   (InternalRawListRecursionSupportProof.consHead _ _ _ hcons') (InternalRawListRecursionSupportProof.consHead _ _ _ hc')
 have hy := valueUnique InternalListCodec.tailCode (ys 1) (y.relabel rho) (Fin.cons (out.relabel rho) Fin.elim0)
   (InternalRawListRecursionSupportProof.consTail _ _ _ hcons') (InternalRawListRecursionSupportProof.consTail _ _ _ hc')
 exact andIntro (outputTransport p _ _ _ hx (hs 0)) (outputTransport q _ _ _ hy (hs 1))

theorem popRecover (R : Program 2) (input work results frame rest payload out : OTerm alpha)
 (hstate : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)))
 (hwork : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work frame rest)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hrole : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.role (numeral 0) input)))
 (hstep : Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.step R) out input))) :
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryReturnStep.pop (OriginalHereditaryReturnStep.termValue R)) out input)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.work work input)) :=
   unaryValue InternalUnpair.left (.projection 0) work input xs (pairLeft input work results hstate) (projectionValue 0 xs)
 have hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryReturnStep.frame frame input)) :=
   unaryValue InternalListCodec.headCode OriginalHereditaryReturnStep.work frame work xs (InternalRawListRecursionSupportProof.consHead work frame rest hwork) hw
 have ht : Nonempty (Derivation body Delta (graph1 (leftOf OriginalHereditaryReturnStep.frame) (numeral 1) input)) :=
   unaryValue InternalUnpair.left OriginalHereditaryReturnStep.frame (numeral 1) frame xs (pairLeft frame (numeral 1) payload hframe) hf
 have hnonzero := OriginalTypedDecoderInternalBranchProof.nonzeroAtElim OriginalHereditaryReturnStep.work (.projection 0) _ out work xs hw
   (OriginalTypedDecoderInternalListProof.consNonzero work frame rest hwork) hstep
 have htag := sameYesElim (leftOf OriginalHereditaryReturnStep.frame) (OriginalRawSyntaxTransport.constant 1 1) _ (.projection 0)
   out (numeral 1) (numeral 1) xs ht (constantValue 1 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (refl (body:=body) (Gamma:=Delta) (numeral 1)))) hnonzero
 exact sameYesElim OriginalHereditaryReturnStep.role (OriginalRawSyntaxTransport.constant 1 0) _ _
   out (numeral 0) (numeral 0) xs hrole (constantValue 0 xs)
   (by simpa only [equalEqn] using (Nonempty.intro (refl (body:=body) (Gamma:=Delta) (numeral 0)))) htag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionSupportProof
