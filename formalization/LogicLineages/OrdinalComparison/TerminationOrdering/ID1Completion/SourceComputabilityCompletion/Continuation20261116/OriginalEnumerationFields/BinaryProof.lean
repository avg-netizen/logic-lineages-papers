module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryAcceptanceWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryProof
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

theorem applicationAtInput (n : Nat) (xs : Fin 6 → OTerm alpha) (typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor (xs 0) typ left right))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓
       ((graph2 contains (suc z) (xs 2) typ ⊓ programGraph (fields n) (suc z) (childInputs xs left (xs 1))) ⊓
        programGraph (fields n) (suc z) (childInputs xs right (xs 1)))))) := by
  constructor
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph3Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hfj ⊢
    apply BinaryWitnessProof.cases n (left.relabel j) (right.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi leftKey rightKey leftOut rightOut depRest deps valueRest values hxi hlk hrk hlv hrv hdr hds hvr hvs
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph3Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hff ⊢
    have hchildren := BinaryAcceptanceWitnessProof.applicationForward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((typ.relabel j).relabel k) ((left.relabel j).relabel k) ((right.relabel j).relabel k)
      leftKey rightKey leftOut rightOut depRest deps valueRest values hkk hpk hcc hlk hrk hlv hrv hdr hds hvr hvs hff
    exact andIntro (AcceptanceProof.validFromFields n (fun i => ((xs i).relabel j).relabel k) hff) hchildren
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph3Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hfj ⊢
    apply BinaryWitnessProof.cases n (left.relabel j) (right.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi leftKey rightKey leftOut rightOut depRest deps valueRest values hxi hlk hrk hlv hrv hdr hds hvr hvs
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph3Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hff ⊢
    exact BinaryAcceptanceWitnessProof.applicationBackward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((typ.relabel j).relabel k) ((left.relabel j).relabel k) ((right.relabel j).relabel k)
      leftKey rightKey leftOut rightOut depRest deps valueRest values hkk hpk hcc hlk hrk hlv hrv hdr hds hvr hvs
      (andLeft hff) (andLeft (andLeft (andRight hff))) (andRight (andLeft (andRight hff))) (andRight (andRight hff))

theorem consAtInput (n : Nat) (xs : Fin 6 → OTerm alpha) (typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor (xs 0) typ left right))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓
       ((graph2 contains (suc z) (xs 2) typ ⊓ programGraph (fields n) (suc z) (childInputs xs left (xs 1))) ⊓
        programGraph (fields n) (suc z) (childInputs xs right (xs 1)))))) := by
  constructor
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph3Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hfj ⊢
    apply BinaryWitnessProof.cases n (left.relabel j) (right.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi leftKey rightKey leftOut rightOut depRest deps valueRest values hxi hlk hrk hlv hrv hdr hds hvr hvs
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph3Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hff ⊢
    have hchildren := BinaryAcceptanceWitnessProof.consForward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((typ.relabel j).relabel k) ((left.relabel j).relabel k) ((right.relabel j).relabel k)
      leftKey rightKey leftOut rightOut depRest deps valueRest values hkk hpk hcc hlk hrk hlv hrv hdr hds hvr hvs hff
    exact andIntro (AcceptanceProof.validFromFields n (fun i => ((xs i).relabel j).relabel k) hff) hchildren
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    have hfj := renameInto hf j Theta hj
    rw [graph3Rename] at hcj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hfj ⊢
    apply BinaryWitnessProof.cases n (left.relabel j) (right.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi leftKey rightKey leftOut rightOut depRest deps valueRest values hxi hlk hrk hlv hrv hdr hds hvr hvs
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    simp only [programRename] at hkk hpk
    rw [graph3Rename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename] at hff ⊢
    exact BinaryAcceptanceWitnessProof.consBackward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((typ.relabel j).relabel k) ((left.relabel j).relabel k) ((right.relabel j).relabel k)
      leftKey rightKey leftOut rightOut depRest deps valueRest values hkk hpk hcc hlk hrk hlv hrv hdr hds hvr hvs
      (andLeft hff) (andLeft (andLeft (andRight hff))) (andRight (andLeft (andRight hff))) (andRight (andRight hff))

theorem internalApplication : Targets.InternalApplication := by
  intro n body alpha Delta raw b S H labels tupleBound typ left right hc
  exact applicationAtInput n ![raw,b,S,H,labels,tupleBound] typ left right hc

theorem internalCons : Targets.InternalCons := by
  intro n body alpha Delta raw b S H labels tupleBound typ left right hc
  exact consAtInput n ![raw,b,S,H,labels,tupleBound] typ left right hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryProof
