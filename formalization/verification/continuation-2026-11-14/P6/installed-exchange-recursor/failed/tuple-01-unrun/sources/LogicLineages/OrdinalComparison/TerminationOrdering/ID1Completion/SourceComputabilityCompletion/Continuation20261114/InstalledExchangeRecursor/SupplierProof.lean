module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.SupplierProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] Primrec

theorem validPrimitive (n : Nat) : Primrec (validValue n) := by
  let V := List.Vector Nat 3
  let Ctx := OrdinaryArithmeticQuotient.Context n
  let Raw := NumberedUniformPackedDecoding.RawPacked n
  have getP (i : Fin 3) : Primrec (fun v : V => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hc := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp (Primrec.unpair.comp (getP 2)))
  have ha : Primrec (fun v : V => Encodable.decode (α := Raw) (v.get 0)) :=
    Primrec.decode.comp (getP 0)
  have hb : Primrec (fun v : V => Encodable.decode (α := Raw) (v.get 1)) :=
    Primrec.decode.comp (getP 1)
  have he : Primrec (fun _ : ((V × Ctx) × Raw) × Raw => (1 : Nat)) := Primrec.const 1
  have hm := Primrec.option_map (hb.comp (Primrec.fst.comp Primrec.fst)) he.to₂
  have hi := Primrec.option_bind (ha.comp Primrec.fst) hm.to₂
  have ho := Primrec.option_getD.comp (Primrec.option_bind hc hi.to₂) (Primrec.const 0)
  apply ho.of_eq
  intro v
  cases hc : Encodable.decode (α := Ctx) (Nat.unpair (v.get 2)).1 <;>
    cases ha : Encodable.decode (α := Raw) (v.get 0) <;>
    cases hb : Encodable.decode (α := Raw) (v.get 1) <;>
    simp only [validValue,hc,ha,hb,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

theorem windowPrimitive (n : Nat) : Primrec (windowValue n) := by
  let V := List.Vector Nat 1
  let Ctx := OrdinaryArithmeticQuotient.Context n
  have h0 : Primrec (fun v : V => v.get 0) := Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  have hc := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp (Primrec.unpair.comp h0))
  have he : Primrec (fun p : V × Ctx => Encodable.encode p.2.1) :=
    Primrec.encode.comp (Primrec.fst.comp Primrec.snd)
  exact (Primrec.option_getD.comp (Primrec.option_map hc he.to₂) (Primrec.const 0)).of_eq
    (by intro v; rfl)

theorem supplierSelection : Targets.SupplierSelection := by
  intro n
  obtain ⟨V,hV⟩ := Proof.allPrimitiveFunctions 3 _ (validPrimitive n)
  obtain ⟨K,hK⟩ := Proof.allPrimitiveFunctions 1 _ (windowPrimitive n)
  exact ⟨V,K,hV,hK⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.SupplierProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.SupplierProof
