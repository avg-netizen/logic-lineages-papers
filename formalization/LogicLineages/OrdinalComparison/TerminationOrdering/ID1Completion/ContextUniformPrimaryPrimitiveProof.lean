module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryPrimitiveProof
open Source NumberedAuxiliaryCoding NumberedUniformPackedDecoding ContextUniformPrimary

abbrev Seed (n : Nat) := Window n × List Ty × RawPacked n
abbrev Stage (n : Nat) := Window n × List (RawPacked n) × List (RawPacked n)
abbrev Run (n : Nat) := Seed n × Nat
abbrev Test (n : Nat) := Window n × List Ty × RawPacked n × RawPacked n

attribute [local irreducible] Primrec

private theorem anyPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) := by
  have hfold : Primrec (fun a => (f a).foldr (fun b rest => g a b || rest) false) :=
    Primrec.list_foldr hf (Primrec.const false)
      (Primrec.or.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  apply hfold.of_eq
  intro a
  induction f a <;> simp_all

private theorem filterPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → List B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).filter (g a)) := by
  have hchoice : Primrec (fun p : A × B => bif g p.1 p.2 then some p.2 else none) :=
    Primrec.cond hg (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  have hfilter : Primrec (fun a => (f a).filterMap (fun b => bif g a b then some b else none)) :=
    Primrec.listFilterMap hf hchoice.to₂
  apply hfilter.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b rest ih => cases hb : g a b <;> simp [hb,ih]

theorem classCodesPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Seed n => classCodes arity p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hb : Primrec (fun p : Seed n => NumberedSyntaxBoundsPrimrec.codeBounds p.2.2.2) :=
    (NumberedSyntaxBoundsPrimrecProof.codeBoundsPrimitive n).comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs := Primrec.fst.comp hb
  have hl := Primrec.snd.comp hb
  have hh : Primrec (fun p : Seed n => NumberedAuxiliaryEnumeration.sourceHeads arity p.1.1 p.1.2) :=
    (NumberedEnumerationOperationsPrimrecProof.sourceHeadsPrimitive n arity).comp Primrec.fst
  have hd : Primrec (fun p : Seed n =>
      (p.1.2,NumberedAuxiliaryEnumeration.sourceHeads arity p.1.1 p.1.2,
        (NumberedSyntaxBoundsPrimrec.codeBounds p.2.2.2).2,
        (NumberedSyntaxBoundsPrimrec.codeBounds p.2.2.2).1)) :=
    (Primrec.snd.comp Primrec.fst).pair (hh.pair (hl.pair hs))
  have hlimits : Primrec (fun p : Seed n =>
      (p.2.1.length,2*(NumberedSyntaxBoundsPrimrec.codeBounds p.2.2.2).1)) :=
    (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.nat_mul.comp (Primrec.const 2) hs)
  have hen := (NumberedCodeEnumerationPrimrecProof.enumerationPrimitive n).comp hd hlimits
  have htype : Primrec (fun p : Seed n => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hpair : Primrec (fun p : Seed n × Code (Fin n) => (p.1.2.2.1,p.2)) :=
    (htype.comp Primrec.fst).pair Primrec.snd
  exact (Primrec.list_map hen hpair.to₂).of_eq (by intro p; rfl)

theorem candidatesPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Seed n => candidates arity p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Seed n × RawPacked n => rawStructuralDecode arity p.1.2.1 p.2) :=
    (NumberedUniformPackedDecodingProof.rawStructuralDecoderPrimitive n arity).comp
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  exact (Primrec.listFilterMap (classCodesPrimitive n arity) hd.to₂).of_eq (by intro p; rfl)

theorem verticesPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Seed n => vertices arity p.1.1 p.1.2 p.2.1 p.2.2) :=
  Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (candidatesPrimitive n arity)

theorem packedExchangePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Window n × RawPacked n × RawPacked n =>
      NumberedExchangeCode.packedCodeExchange arity p.1.1 p.1.2 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Window n × RawPacked n × RawPacked n => decide (p.2.1.1 = p.2.2.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).decide
  have hc : Primrec (fun p : Window n × RawPacked n × RawPacked n =>
      NumberedExchangeCode.codeExchange arity p.1.1 p.1.2 p.2.1.2 p.2.2.2) :=
    (NumberedExchangeCodePrimrecProof.codeExchangePrimitive n arity).comp
      (Primrec.fst.pair ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (Primrec.and.comp ht hc).of_eq (by intro p; rfl)

theorem stepPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Stage n => step arity p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hedge : Primrec (fun p : (Stage n × RawPacked n) × RawPacked n =>
      NumberedExchangeCode.packedCodeExchange arity p.1.1.1.1 p.1.1.1.2 p.2 p.1.2) :=
    (packedExchangePrimitive n arity).comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))
  have ha : Primrec (fun p : Stage n × RawPacked n =>
      p.1.2.2.any (fun a => NumberedExchangeCode.packedCodeExchange arity p.1.1.1 p.1.1.2 a p.2)) :=
    anyPrimitive (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hedge.to₂
  have hf : Primrec (fun p : Stage n =>
      p.2.1.filter (fun r => p.2.2.any (fun a =>
        NumberedExchangeCode.packedCodeExchange arity p.1.1 p.1.2 a r))) :=
    filterPrimitive (Primrec.fst.comp Primrec.snd) ha.to₂
  exact (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd) hf).of_eq (by intro p; rfl)

theorem seedStepPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Seed n × List (RawPacked n) =>
      step arity p.1.1.1 p.1.1.2 (vertices arity p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2) p.2) :=
  (stepPrimitive n arity).comp
    ((Primrec.fst.comp Primrec.fst).pair (((verticesPrimitive n arity).comp Primrec.fst).pair Primrec.snd))

theorem reachablePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Run n => reachable arity p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2) := by
  unfold reachable
  exact Primrec.nat_iterate
    (f := fun p : Run n => p.2)
    (g := fun p : Run n => [p.1.2.2])
    (h := fun (p : Run n) (reached : List (RawPacked n)) =>
      step arity p.1.1.1 p.1.1.2 (vertices arity p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2) reached)
    Primrec.snd
    (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const []))
    ((seedStepPrimitive n arity).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem primaryListPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Seed n => primaryList arity p.1.1 p.1.2 p.2.1 p.2.2) :=
  ((reachablePrimitive n arity).comp
    (Primrec.id.pair (Primrec.list_length.comp (verticesPrimitive n arity)))).of_eq (by intro p; rfl)

theorem actualRawPrimaryPrimitive : ContextUniformPrimaryTargets.ActualRawPrimaryPrimitive := by
  intro n arity
  have hc : Primrec (fun p : Test n => primaryList arity p.1.1 p.1.2 p.2.1 p.2.2.1) :=
    (primaryListPrimitive n arity).comp
      (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  exact ((NumberedHeadWindowPrimrecProof.memberPrimitive (RawPacked n)).decide.comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hc).of_eq (by intro p; rfl)

theorem packedNumberPrimitive (n : Nat) : Primrec (@ContextUniformPrimary.packedNumber n) :=
  Primrec₂.natPair.comp (NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp Primrec.fst)
    ((NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd)

theorem classNumberTestPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Seed n × Nat => classNumberTest arity p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2) := by
  have hd : Primrec (fun p : Seed n × Nat => rawPackedDecode n arity p.1.2.1 p.2) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  have hseed : Primrec (fun p : (Seed n × Nat) × RawPacked n => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : (Seed n × Nat) × RawPacked n =>
      (p.1.1.1,p.1.1.2.1,p.1.1.2.2,p.2)) :=
    (Primrec.fst.comp hseed).pair ((Primrec.fst.comp (Primrec.snd.comp hseed)).pair
      ((Primrec.snd.comp (Primrec.snd.comp hseed)).pair Primrec.snd))
  have hb := (actualRawPrimaryPrimitive n arity).comp hi
  exact (NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive hd hb.to₂).of_eq (by intro p; rfl)

theorem actualRawRepresentativePrimitive : ContextUniformPrimaryTargets.ActualRawRepresentativePrimitive := by
  intro n arity
  have hb : Primrec (fun p : Seed n => ContextUniformPrimary.packedNumber p.2.2 + 1) :=
    Primrec.succ.comp ((packedNumberPrimitive n).comp (Primrec.snd.comp Primrec.snd))
  have hr := Primrec.list_range.comp hb
  exact (Primrec.list_findIdx hr (classNumberTestPrimitive n arity).to₂).of_eq (by intro p; rfl)

theorem actualUniformCanonicalPrimitive : ContextUniformPrimaryTargets.ActualUniformCanonicalPrimitive := by
  intro n arity
  let Input := Window n × List Ty × Nat
  have hd : Primrec (fun p : Input => rawUniverseDecode n arity p.1.1 p.1.2 p.2.1 p.2.2) :=
    NumberedUniformPackedDecodingProof.rawUniverseDecoderPrimitive n arity
  have hr : Primrec (fun p : Input × RawPacked n =>
      representative arity p.1.1.1 p.1.1.2 p.1.2.1 p.2) :=
    (actualRawRepresentativePrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have hb : Primrec (fun p : Input × RawPacked n =>
      decide (representative arity p.1.1.1 p.1.1.2 p.1.2.1 p.2 = p.1.2.2)) :=
    (Primrec.eq.comp hr (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).decide
  exact (NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive hd hb.to₂).of_eq (by intro p; rfl)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryPrimitiveProof
