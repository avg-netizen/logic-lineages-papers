module
public import LogicLineages.PermittedControl.StableSortedHighFieldTargets
import LogicLineages.PermittedControl.HighFieldPreparedPacketShapeProof
import LogicLineages.PermittedControl.HighFieldComparisonCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl.StableSortedHighField
open FieldComparison PreparedProjection HighFieldPreparedPacket
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

theorem basePacketExact : BasePacketExact := by
  intro F G lowRank highRank wanted ordered
  have source := (highFieldComparisonCalibration.2.2.2 F G lowRank highRank).1 ordered
  by_cases admitted : wanted ≤ 2
  · cases form : distinctForm (normalizeShortField F) (normalizeShortField G) with
    | const answer =>
      simpa only [compile,source,basePacket,if_pos admitted,form,encodeComparisonForm] using
        And.intro (packetExact.2.1 0 answer lowRank highRank wanted admitted) (packetShape.2.1 0 answer wanted)
    | linear sign H =>
      simpa only [compile,source,basePacket,if_pos admitted,form,encodeComparisonForm] using
        And.intro (packetExact.2.2 0 sign lowRank highRank wanted H admitted)
          (packetShape.2.2 0 sign lowRank highRank wanted H)
  · have failed := lt_of_not_ge admitted
    simpa only [compile,basePacket,if_neg admitted] using
      And.intro (packetExact.1 _ lowRank highRank wanted failed) packetShape.1

theorem orderGuardEval (name : Nat) (ν : Nat → Nat) :
    (orderGuard name).eval ν ↔ ν name < ν 0 := by
  simp [orderGuard,NormalForm.Formula.eval,NormalForm.Atom.eval,NormalForm.rowValue,
    NormalForm.Summand.term,Term.value]
  omega

theorem appendOrderShape (table : List LowerOperand) (p : NormalForm.Formula) (lowRank : Nat)
    (base : PreparedInput table p) :
    PreparedInput (table ++ [.coordinate lowRank])
      (.conjunction (orderGuard (table.length+1)) p) := by
  constructor
  · intro a member term used
    rcases List.mem_append.mp member with guardMember | baseMember
    · have atom : a = .nonnegative (-1,[(1,.variable 0),(-1,.variable (table.length+1))]) :=
        List.mem_singleton.mp guardMember
      subst a
      change term ∈ [(1,.variable 0),(-1,.variable (table.length+1))] at used
      rcases List.mem_cons.mp used with first | second
      · subst term
        exact ⟨0,rfl⟩
      · have exactTerm := List.mem_singleton.mp second
        subst term
        exact ⟨table.length+1,rfl⟩
    · exact base.1 a baseMember term used
  · intro name used
    rcases List.mem_append.mp used with guardUsed | baseUsed
    · change name ∈ [0,table.length+1] at guardUsed
      rcases List.mem_cons.mp guardUsed with first | second
      · subst name
        exact Nat.zero_le _
      · have last := List.mem_singleton.mp second
        subst name
        simp
    · exact (base.2 name baseUsed).trans (by simp)

end LogicLineages.PermittedControl.StableSortedHighField
