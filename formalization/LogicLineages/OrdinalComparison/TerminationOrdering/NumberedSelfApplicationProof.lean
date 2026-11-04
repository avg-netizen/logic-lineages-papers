module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCodePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedSelectCertificate NumberedSelfApplication
open NumberedSelectCodePrimrecProof NumberedSelfApplicationSupportProof

attribute [local irreducible] Primrec selectTarget

theorem selectTypePreservation (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty) (index : Nat)
    (q r : Packed (Fin n) arity Gamma) (h : selectTarget arity Gamma types index q=some r) : r.1=q.1 := by
  have hi := (NumberedSelectCertificateProof.selectCertificates n arity Gamma q r).mp ⟨types,index,h⟩
  cases hi
  rfl

theorem packedSelectPrimitive : NumberedSelfApplicationTargets.ActualPackedSelectPrimitive := by
  intro n arity Gamma
  have hp : Primrec (fun p : List Ty × Nat × Packed (Fin n) arity Gamma =>
      (p.1,p.2.1,packedCode p.2.2)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      ((NumberedPackedStructurePrimrecProof.packedCodePrimitive n arity Gamma).comp (Primrec.snd.comp Primrec.snd)))
  have hr : Primrec (fun p : List Ty × Nat × Packed (Fin n) arity Gamma =>
      selectCode p.1 p.2.1 p.2.2.1 (termCode p.2.2.2)) := (allSelectCodePrimitive n).comp hp
  exact NumberedDirectOperationsProof.reconstructSameType
    (A := List Ty × Nat × Packed (Fin n) arity Gamma) (fun p => p.2.2)
    (fun p => selectTarget arity Gamma p.1 p.2.1 p.2.2)
    (fun p => selectCode p.1 p.2.1 p.2.2.1 (termCode p.2.2.2))
    (Primrec.snd.comp Primrec.snd) hr
    (fun p => selectCodeCalibration n arity Gamma p.1 p.2.1 p.2.2)
    (fun p r h => selectTypePreservation n arity Gamma p.1 p.2.1 p.2.2 r h)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationProof
