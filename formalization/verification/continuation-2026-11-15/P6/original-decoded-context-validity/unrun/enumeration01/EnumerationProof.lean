module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.EnumerationProof

theorem vectorsComplete {alpha : Type} (values : List alpha) (n : Nat)
    (f : Fin n → alpha) (h : ∀ i, f i ∈ values) : f ∈ vectors values n := by
  induction n with
  | zero =>
    have hf : f = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [hf]
    exact List.mem_cons_self
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, h 0, List.mem_map.mpr ?_⟩
    exact ⟨Fin.tail f, ih (Fin.tail f) (fun i => h i.succ), Fin.cons_self_tail f⟩

theorem tablesComplete (n : Nat) (f : Fin n → Fin n → Bool) : f ∈ tables n := by
  apply vectorsComplete
  intro i
  apply vectorsComplete
  intro j
  cases h : f i j <;> simp [h]

theorem encodedMember (n : Nat) (f : Fin n → Fin n → Bool) :
    Encodable.encode f ∈ tableCodes n :=
  List.mem_map.mpr ⟨f,tablesComplete n f,rfl⟩

/-- Canonicality supplies the converse on arbitrary raw codes, not just images. -/
theorem tableDecode (n raw : Nat) :
    (Encodable.decode (α := Fin n → Fin n → Bool) raw).isSome = decide (raw ∈ tableCodes n) := by
  by_cases hm : raw ∈ tableCodes n
  · obtain ⟨f,hf,he⟩ := List.mem_map.mp hm
    rw [← he,Encodable.encodek]
    simp only [Option.isSome_some,hm,decide_true]
  · cases hd : Encodable.decode (α := Fin n → Fin n → Bool) raw with
    | none => simp only [Option.isSome_none,hm,decide_false]
    | some f =>
      have he := OrdinaryArithmeticQuotientDecoderProof.tableCanonical n raw f hd
      have hf := encodedMember n f
      rw [he] at hf
      exact False.elim (hm hf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.EnumerationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.EnumerationProof
