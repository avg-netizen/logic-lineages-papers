module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof ChildInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem childInputsRename (xs : Fin 6 → OTerm alpha) (child bound : OTerm alpha)
    {beta : Type} (j : alpha → beta) :
    (fun i => (childInputs xs child bound i).relabel j) =
      childInputs (fun i => (xs i).relabel j) (child.relabel j) (bound.relabel j) := by
  funext i
  fin_cases i <;> rfl

theorem allowedRename (n : Nat) (heads rawHead : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (Targets.headAllowed n heads rawHead).relabel j = Targets.headAllowed n (heads.relabel j) (rawHead.relabel j) :=
  OriginalEncodedNumberedEnumerationBranch.MapImageProof.imageRename (OriginalEncodedHeadConversion.convert n) heads rawHead j

theorem atMapped (n : Nat) (xs : Fin 6 → OTerm alpha) (head child mapped : OTerm alpha)
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓
       (Targets.headAllowed n (xs 3) head ⊓ programGraph (fields n) (suc z) (childInputs xs child (xs 1)))))) := by
  constructor
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hmapj := renameInto hmap j Theta hj
    rw [graph1Rename] at hmapj
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph2Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,allowedRename,consTermRename,emptyRename] at hfj ⊢
    apply UnaryWitnessProof.cases n (child.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi childKey value deps values hxi hck hv hd hl
    have hmapk := renameInto hmapj k Xi hxi
    rw [graph1Rename] at hmapk
    have hck' := hck
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph2Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,allowedRename,consTermRename,emptyRename] at hff ⊢
    have hchildren := OrdinaryWitnessProof.forward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((head.relabel j).relabel k) ((child.relabel j).relabel k)
      childKey value deps values ((mapped.relabel j).relabel k) hkk hpk hcc hck' hv hd hl hmapk hff
    exact andIntro (AcceptanceProof.validFromFields n (fun i => ((xs i).relabel j).relabel k) hff) hchildren
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hmapj := renameInto hmap j Theta hj
    rw [graph1Rename] at hmapj
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph2Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,allowedRename,consTermRename,emptyRename] at hfj ⊢
    apply UnaryWitnessProof.cases n (child.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi childKey value deps values hxi hck hv hd hl
    have hmapk := renameInto hmapj k Xi hxi
    rw [graph1Rename] at hmapk
    have hck' := hck
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph2Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,allowedRename,consTermRename,emptyRename] at hff ⊢
    exact OrdinaryWitnessProof.backward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((head.relabel j).relabel k) ((child.relabel j).relabel k)
      childKey value deps values ((mapped.relabel j).relabel k) hkk hpk hcc hck' hv hd hl hmapk (andLeft hff) (andLeft (andRight hff)) (andRight (andRight hff))

theorem atInput (n : Nat) (xs : Fin 6 → OTerm alpha) (head child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor (xs 0) head child))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓
       (Targets.headAllowed n (xs 3) head ⊓ programGraph (fields n) (suc z) (childInputs xs child (xs 1)))))) := by
  constructor
  · intro hf
    apply InternalAcceptanceSupportProof.programCases (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (Fin.cons (xs 3) Fin.elim0) _
    intro beta j Theta mapped hj hmap
    simp only [consTermRename,emptyRename] at hmap
    have hcj := renameInto hc j Theta hj
    rw [graph2Rename] at hcj
    have hfj := renameInto hf j Theta hj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,allowedRename,consTermRename,emptyRename] at hfj ⊢
    exact (atMapped n (fun i => (xs i).relabel j) (head.relabel j) (child.relabel j) mapped hmap hcj).mp hfj
  · intro hf
    apply InternalAcceptanceSupportProof.programCases (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (Fin.cons (xs 3) Fin.elim0) _
    intro beta j Theta mapped hj hmap
    simp only [consTermRename,emptyRename] at hmap
    have hcj := renameInto hc j Theta hj
    rw [graph2Rename] at hcj
    have hfj := renameInto hf j Theta hj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,allowedRename,consTermRename,emptyRename] at hfj ⊢
    exact (atMapped n (fun i => (xs i).relabel j) (head.relabel j) (child.relabel j) mapped hmap hcj).mpr hfj

theorem internalOrdinary : Targets.InternalOrdinary := by
  intro n body alpha Delta raw b S H labels tupleBound head child hc
  exact atInput n ![raw,b,S,H,labels,tupleBound] head child hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.OrdinaryProof
