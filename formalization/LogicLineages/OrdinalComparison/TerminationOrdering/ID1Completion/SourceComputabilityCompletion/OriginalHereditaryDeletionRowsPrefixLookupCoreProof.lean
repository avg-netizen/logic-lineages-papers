module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalSquareRootArithmeticSupportProof
open InternalListCodecSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryDeletionRowsPrefixSyntaxProof
open OriginalHereditaryDeletionRowsAppendProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tailCases (tail suffix : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (count joined : OTerm beta), (∀ p ∈ Delta, p.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (lengthGraph count (tail.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append joined (tail.relabel rho) (suffix.relabel rho))) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let l : Program 2 := .composition length (fun _ : Fin 1 => .projection 0)
 let qs : Fin 2 → Program 2 := ![l,InternalApplicationValidityStackAppend.append]
 let xs : Fin 2 → OTerm alpha := ![tail,suffix]
 apply InternalApplicationStepPeelSupportProof.queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 2 → OTerm beta := ![tail.relabel rho,suffix.relabel rho]
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hl := unaryRecover length (.projection 0) (ys 0) (tail.relabel rho) xx (hq 0) (projectionValue 0 xx)
 exact next beta rho Theta (ys 0) (ys 1) hrho hl (hq 1)

theorem zeroAtCons (count front head tail suffix out value : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
 (hf : Nonempty (Derivation body Delta (fields count front z suffix out value))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value z out)) := by
 apply tailCases tail suffix _
 intro beta rho Theta tailCount joined hrho hlen happ
 simp only [graph2Rename,zRelabel]
 have hc' := renameInto hc rho Theta hrho
 rw [consGraphRename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fieldsRename,zRelabel] at hf'
 have hv := andRight (andRight (andRight hf'))
 have hhead := OriginalAllPositionContextDeleteBaseProof.lookupZero (front.relabel rho) (head.relabel rho) (tail.relabel rho) hc'
 have he := valueUnique InternalRawListRecursion.lookup (value.relabel rho) (head.relabel rho)
   ![z,front.relabel rho] hv hhead
 obtain ⟨he⟩ := he
 have ho := appendHead (front.relabel rho) (head.relabel rho) (tail.relabel rho) (suffix.relabel rho)
   joined (out.relabel rho) hc' happ (andLeft (andRight (andRight hf')))
 exact outputTransport InternalRawListRecursion.lookup (head.relabel rho) (value.relabel rho)
   ![z,out.relabel rho] ⟨symm he⟩ ho

theorem successorAtCons (count front cutoff head tail suffix out value : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (row cutoff)))
 (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
 (hf : Nonempty (Derivation body Delta (fields count front (suc cutoff) suffix out value))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (suc cutoff) out)) := by
 apply tailCases tail suffix _
 intro beta rho Theta tailCount joined hrho hlen happ
 simp only [graph2Rename,sucRelabel]
 have hc' := renameInto hc rho Theta hrho
 rw [consGraphRename] at hc'
 have hf' := renameInto hf rho Theta hrho
 simp only [fieldsRename,sucRelabel] at hf'
 have hi := renameInto hrow rho Theta hrho
 rw [rowRename] at hi
 obtain ⟨he⟩ := lengthConsRecover (front.relabel rho) (head.relabel rho) (tail.relabel rho)
   (count.relabel rho) tailCount hc' (andLeft hf') hlen
 obtain ⟨hlt⟩ := andLeft (andRight hf')
 have hb := OriginalContextInsertionBelowCoreProof.successorStrict (cutoff.relabel rho) tailCount
   ⟨orderRight (suc (cutoff.relabel rho)) he hlt⟩
 obtain ⟨hlk⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff
   (front.relabel rho) (head.relabel rho) (tail.relabel rho) (cutoff.relabel rho) (value.relabel rho) hc'
 obtain ⟨hv⟩ := andRight (andRight (andRight hf'))
 have htail := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft hlk) hv)
 have hout := rowApply tailCount (tail.relabel rho) (cutoff.relabel rho) (suffix.relabel rho) joined (value.relabel rho)
   hi (andIntro hlen (andIntro hb (andIntro happ htail)))
 obtain ⟨hout⟩ := hout
 obtain ⟨hlift⟩ := appendLookupSuccessor (front.relabel rho) (head.relabel rho) (tail.relabel rho)
   (suffix.relabel rho) joined (out.relabel rho) (cutoff.relabel rho) (value.relabel rho)
   hc' happ (andLeft (andRight (andRight hf')))
 exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hlift) hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupCoreProof
