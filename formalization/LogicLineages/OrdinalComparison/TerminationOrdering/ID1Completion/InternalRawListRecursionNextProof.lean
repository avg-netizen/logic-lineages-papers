module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionNextProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalRawListRecursionSyntaxProof InternalListCodec
open InternalControlGraphSupportProof InternalListCodecSupportProof
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nextCodeAt {k : Nat} (index previous : OTerm α) (params : Fin k → OTerm α) :
    Nonempty (Derivation body Gamma (programGraph (nextCode : Program (k + 2)) (suc index)
      (Fin.cons index (Fin.cons previous params)))) := by
  let xs : Fin (k + 2) → OTerm α := Fin.cons index (Fin.cons previous params)
  apply compositionValue .succ (fun _ : Fin 1 => .projection 0) (suc index)
    xs (Fin.cons index Fin.elim0) (successorValue (Fin.cons index Fin.elim0))
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 xs

theorem nextUnaryAt {k : Nat} (p : Program 1) (out index previous : OTerm α)
    (params : Fin k → OTerm α)
    (h : Nonempty (Derivation body Gamma (unaryGraph p out (suc index)))) :
    Nonempty (Derivation body Gamma (programGraph
      (.composition p (fun _ : Fin 1 => (nextCode : Program (k + 2)))) out
      (Fin.cons index (Fin.cons previous params)))) := by
  apply compositionValue p (fun _ : Fin 1 => nextCode) out
    (Fin.cons index (Fin.cons previous params)) (Fin.cons (suc index) Fin.elim0) h
  intro i
  obtain rfl := Fin.eq_zero i
  exact nextCodeAt index previous params

theorem nextHeadAt {k : Nat} (head index previous : OTerm α) (params : Fin k → OTerm α)
    (h : Nonempty (Derivation body Gamma (unaryGraph headCode head (suc index)))) :
    Nonempty (Derivation body Gamma (programGraph (nextHead : Program (k + 2)) head
      (Fin.cons index (Fin.cons previous params)))) :=
  nextUnaryAt headCode head index previous params h

theorem nextTailAt {k : Nat} (tail index previous : OTerm α) (params : Fin k → OTerm α)
    (h : Nonempty (Derivation body Gamma (unaryGraph tailCode tail (suc index)))) :
    Nonempty (Derivation body Gamma (programGraph (nextTail : Program (k + 2)) tail
      (Fin.cons index (Fin.cons previous params)))) :=
  nextUnaryAt tailCode tail index previous params h

theorem previousIndexAt {k : Nat} (gap tail index previous : OTerm α)
    (params : Fin k → OTerm α)
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode tail (suc index))))
    (hg : Nonempty (Derivation body Gamma (programGraph InternalEqualityTest.subtract gap
      (Fin.cons tail (Fin.cons index Fin.elim0))))) :
    Nonempty (Derivation body Gamma (programGraph (previousIndex : Program (k + 2)) gap
      (Fin.cons index (Fin.cons previous params)))) := by
  let xs : Fin (k + 2) → OTerm α := Fin.cons index (Fin.cons previous params)
  apply compositionValue InternalEqualityTest.subtract
    (Fin.cons nextTail (Fin.cons (.projection 0) Fin.elim0)) gap xs
    (Fin.cons tail (Fin.cons index Fin.elim0)) hg
  intro i
  exact Fin.cases (nextTailAt tail index previous params ht)
    (Fin.cases (projectionValue 0 xs) (fun q => Fin.elim0 q)) i

theorem previousValueAt {k : Nat} (result gap tail index previous : OTerm α)
    (params : Fin k → OTerm α)
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode tail (suc index))))
    (hg : Nonempty (Derivation body Gamma (programGraph InternalEqualityTest.subtract gap
      (Fin.cons tail (Fin.cons index Fin.elim0)))))
    (hl : Nonempty (Derivation body Gamma (lookupGraph result gap previous))) :
    Nonempty (Derivation body Gamma (programGraph (previousValue : Program (k + 2)) result
      (Fin.cons index (Fin.cons previous params)))) := by
  let xs : Fin (k + 2) → OTerm α := Fin.cons index (Fin.cons previous params)
  apply compositionValue lookup (Fin.cons previousIndex (Fin.cons (.projection 1) Fin.elim0))
    result xs (Fin.cons gap (Fin.cons previous Fin.elim0)) hl
  intro i
  exact Fin.cases (previousIndexAt gap tail index previous params ht hg)
    (Fin.cases (projectionValue 1 xs) (fun q => Fin.elim0 q)) i

/-- The literal table-step value is assembled from the same head, tail-index
lookup and user-step witnesses. All original parameters and the complete
object-language hypothesis context are retained. -/
theorem nextValueAt {k : Nat} (step : Program (k + 2))
    (index previous head tail gap result out : OTerm α) (params : Fin k → OTerm α)
    (hh : Nonempty (Derivation body Gamma (unaryGraph headCode head (suc index))))
    (ht : Nonempty (Derivation body Gamma (unaryGraph tailCode tail (suc index))))
    (hg : Nonempty (Derivation body Gamma (programGraph InternalEqualityTest.subtract gap
      (Fin.cons tail (Fin.cons index Fin.elim0)))))
    (hl : Nonempty (Derivation body Gamma (lookupGraph result gap previous)))
    (hs : Nonempty (Derivation body Gamma (programGraph step out
      (Fin.cons head (Fin.cons result params))))) :
    Nonempty (Derivation body Gamma (programGraph (nextValue step) out
      (Fin.cons index (Fin.cons previous params)))) := by
  let xs : Fin (k + 2) → OTerm α := Fin.cons index (Fin.cons previous params)
  apply compositionValue step
    (Fin.cons nextHead (Fin.cons previousValue (fun i => .projection i.succ.succ)))
    out xs (Fin.cons head (Fin.cons result params)) hs
  intro i
  exact Fin.cases (nextHeadAt head index previous params hh)
    (Fin.cases (previousValueAt result gap tail index previous params ht hg hl)
      (fun j => projectionValue j.succ.succ xs)) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionNextProof
