module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof (strictRename)
open OriginalContextInsertionSyntaxProof (lengthRename)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof ChildInputProof
open Types.AllowedSyntaxProof (allowedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem childInputsRename (xs : Fin 6 → OTerm alpha) (child bound : OTerm alpha)
    {beta : Type} (j : alpha → beta) :
    (fun i => (childInputs xs child bound i).relabel j) =
      childInputs (fun i => (xs i).relabel j) (child.relabel j) (bound.relabel j) := by
  funext i
  fin_cases i <;> rfl

theorem headAllowedRename (n : Nat) (heads rawHead : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (Targets.headAllowed n heads rawHead).relabel j = Targets.headAllowed n (heads.relabel j) (rawHead.relabel j) :=
  OriginalEncodedNumberedEnumerationBranch.MapImageProof.imageRename (OriginalEncodedHeadConversion.convert n) heads rawHead j

theorem sixRename (a b c d e f : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (fun i => (![a,b,c,d,e,f] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
  funext i
  fin_cases i <;> rfl

theorem atKnown (n : Nat) (xs : Fin 6 → OTerm alpha) (label head typ base list extra mapped len : OTerm alpha)
    (hmap : Nonempty (Derivation body Delta (graph1 (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) mapped (xs 3))))
    (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph len list)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,list,extra]))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓
       (((((InternalLessThan.strictLess label (suc (xs 4)) ⊓ Targets.headAllowed n (xs 3) head) ⊓
         graph2 contains (suc z) (xs 2) typ) ⊓ programGraph (fields n) (suc z) (childInputs xs base (xs 1))) ⊓
         Targets.typesAllowed list (xs 2) (xs 5)) ⊓ programGraph (fields n) (suc z) (childInputs xs extra (xs 1)))))) := by
  constructor
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    simp only [programRename,sixRename] at hcj
    have hmj := renameInto hmap j Theta hj
    rw [graph1Rename] at hmj
    have hlj := renameInto hlen j Theta hj
    rw [lengthRename] at hlj
    have hfj := renameInto hf j Theta hj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename,strictRename,headAllowedRename,allowedRename] at hfj ⊢
    apply BinaryWitnessProof.cases n (base.relabel j) (extra.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi leftKey rightKey leftOut rightOut depRest deps valueRest values hxi hlk hrk hlv hrv hdr hds hvr hvs
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hmm := renameInto hmj k Xi hxi
    have hll := renameInto hlj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    rw [graph1Rename] at hmm
    rw [lengthRename] at hll
    simp only [programRename] at hkk hpk
    simp only [programRename,sixRename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename,strictRename,headAllowedRename,allowedRename] at hff ⊢
    have hchildren := NumberedWitnessProof.forward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((label.relabel j).relabel k) ((head.relabel j).relabel k)
      ((typ.relabel j).relabel k) ((base.relabel j).relabel k) ((list.relabel j).relabel k) ((extra.relabel j).relabel k)
      leftKey rightKey leftOut rightOut depRest deps valueRest values ((mapped.relabel j).relabel k) ((len.relabel j).relabel k)
      hkk hpk hcc hlk hrk hlv hrv hdr hds hvr hvs hmm hll hff
    exact andIntro (AcceptanceProof.validFromFields n (fun i => ((xs i).relabel j).relabel k) hff) hchildren
  · intro hf
    apply AcceptanceProof.cases n xs _
    intro beta j Theta key param answers hj hk hp ha
    have hcj := renameInto hc j Theta hj
    simp only [programRename,sixRename] at hcj
    have hmj := renameInto hmap j Theta hj
    rw [graph1Rename] at hmj
    have hlj := renameInto hlen j Theta hj
    rw [lengthRename] at hlj
    have hfj := renameInto hf j Theta hj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename,strictRename,headAllowedRename,allowedRename] at hfj ⊢
    apply BinaryWitnessProof.cases n (base.relabel j) (extra.relabel j) ((xs 1).relabel j) param _
    intro gamma k Xi leftKey rightKey leftOut rightOut depRest deps valueRest values hxi hlk hrk hlv hrv hdr hds hvr hvs
    have hkk := renameInto hk k Xi hxi
    have hpk := renameInto hp k Xi hxi
    have hcc := renameInto hcj k Xi hxi
    have hmm := renameInto hmj k Xi hxi
    have hll := renameInto hlj k Xi hxi
    have hff := renameInto hfj k Xi hxi
    rw [graph1Rename] at hmm
    rw [lengthRename] at hll
    simp only [programRename] at hkk hpk
    simp only [programRename,sixRename] at hcc
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename,strictRename,headAllowedRename,allowedRename] at hff ⊢
    have parts := andRight hff
    have h5 := andRight parts
    have t4 := andLeft parts
    have h4 := andRight t4
    have t3 := andLeft t4
    have h3 := andRight t3
    have t2 := andLeft t3
    have h2 := andRight t2
    have t1 := andLeft t2
    have h1 := andRight t1
    have h0 := andLeft t1
    exact NumberedWitnessProof.backward n (fun i => ((xs i).relabel j).relabel k)
      (key.relabel k) (param.relabel k) ((label.relabel j).relabel k) ((head.relabel j).relabel k)
      ((typ.relabel j).relabel k) ((base.relabel j).relabel k) ((list.relabel j).relabel k) ((extra.relabel j).relabel k)
      leftKey rightKey leftOut rightOut depRest deps valueRest values ((mapped.relabel j).relabel k) ((len.relabel j).relabel k)
      hkk hpk hcc hlk hrk hlv hrv hdr hds hvr hvs hmm hll (andLeft hff) h0 h1 h2 h3 h4 h5

def extras (n : Nat) : Fin 2 → Program 2 :=
  ![.composition (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (fun _ : Fin 1 => .projection 0),
    .composition OriginalContextInsertion.length (fun _ : Fin 1 => .projection 1)]

theorem atInput (n : Nat) (xs : Fin 6 → OTerm alpha) (label head typ base list extra : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,list,extra]))) :
    (Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0) ⊓
       (((((InternalLessThan.strictLess label (suc (xs 4)) ⊓ Targets.headAllowed n (xs 3) head) ⊓
         graph2 contains (suc z) (xs 2) typ) ⊓ programGraph (fields n) (suc z) (childInputs xs base (xs 1))) ⊓
         Targets.typesAllowed list (xs 2) (xs 5)) ⊓ programGraph (fields n) (suc z) (childInputs xs extra (xs 1)))))) := by
  constructor
  · intro hf
    apply queryCases (extras n) ![xs 3,list] _
    intro beta j ys Theta hj hq
    have hx : (fun i => (![xs 3,list] i).relabel j) = ![(xs 3).relabel j,list.relabel j] := by
      funext i
      fin_cases i <;> rfl
    rw [hx] at hq
    have hm := unaryRecover (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (.projection 0)
      (ys 0) ((xs 3).relabel j) ![(xs 3).relabel j,list.relabel j] (hq 0) (projectionValue 0 ![(xs 3).relabel j,list.relabel j])
    have hl := unaryRecover OriginalContextInsertion.length (.projection 1)
      (ys 1) (list.relabel j) ![(xs 3).relabel j,list.relabel j] (hq 1) (projectionValue 1 ![(xs 3).relabel j,list.relabel j])
    have hcj := renameInto hc j Theta hj
    simp only [programRename,sixRename] at hcj
    have hfj := renameInto hf j Theta hj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename,strictRename,headAllowedRename,allowedRename] at hfj ⊢
    exact (atKnown n (fun i => (xs i).relabel j) (label.relabel j) (head.relabel j) (typ.relabel j)
      (base.relabel j) (list.relabel j) (extra.relabel j) (ys 0) (ys 1) hm hl hcj).mp hfj
  · intro hf
    apply queryCases (extras n) ![xs 3,list] _
    intro beta j ys Theta hj hq
    have hx : (fun i => (![xs 3,list] i).relabel j) = ![(xs 3).relabel j,list.relabel j] := by
      funext i
      fin_cases i <;> rfl
    rw [hx] at hq
    have hm := unaryRecover (OriginalEncodedNumberedEnumerationBranch.convertedHeads n) (.projection 0)
      (ys 0) ((xs 3).relabel j) ![(xs 3).relabel j,list.relabel j] (hq 0) (projectionValue 0 ![(xs 3).relabel j,list.relabel j])
    have hl := unaryRecover OriginalContextInsertion.length (.projection 1)
      (ys 1) (list.relabel j) ![(xs 3).relabel j,list.relabel j] (hq 1) (projectionValue 1 ![(xs 3).relabel j,list.relabel j])
    have hcj := renameInto hc j Theta hj
    simp only [programRename,sixRename] at hcj
    have hfj := renameInto hf j Theta hj
    simp only [conjunctionRename,graph1Rename,graph2Rename,programRename,sucRelabel,zRelabel,childInputsRename,consTermRename,emptyRename,strictRename,headAllowedRename,allowedRename] at hfj ⊢
    exact (atKnown n (fun i => (xs i).relabel j) (label.relabel j) (head.relabel j) (typ.relabel j)
      (base.relabel j) (list.relabel j) (extra.relabel j) (ys 0) (ys 1) hm hl hcj).mpr hfj

theorem internalNumbered : Targets.InternalNumbered := by
  intro n body alpha Delta raw b S H labels tupleBound label head typ base list extra hc
  exact atInput n ![raw,b,S,H,labels,tupleBound] label head typ base list extra hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedProof
