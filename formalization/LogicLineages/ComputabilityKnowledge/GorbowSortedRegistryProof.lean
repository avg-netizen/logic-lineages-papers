module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedRegistry
public import LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof
open GorbowRegistryTuple GorbowRegistryDecoder GorbowSortedRegistry

private theorem headerAt (arity tag : Nat) (args : List Nat) : decodeHeader (header arity tag args)=some (arity,tag,args) :=
  (GorbowRegistryDecoderProof.headerExact _ _ _ _).mpr rfl

theorem relationDispatch : Comparators.GorbowSortedRegistry.RelationDispatch := by
  intro a b
  simp [relationProgram,headerAt]
theorem functionDispatch : Comparators.GorbowSortedRegistry.FunctionDispatch := by
  intro a b c
  simp [functionProgram,headerAt]

theorem malformedDefaults : Comparators.GorbowSortedRegistry.MalformedDefaults := by
  refine ⟨?_,?_,?_⟩
  · intro code h
    simp [relationProgram,functionProgram,h]
  · intro arity tag args h₁ h₂
    have h0 : ¬(arity=1 ∧ tag=0 ∧ args.length=1) := by omega
    have h1 : ¬(arity=1 ∧ tag=1 ∧ args.length=1) := by omega
    have h2 : ¬(arity=1 ∧ tag=2 ∧ args.length=1) := by omega
    have h3 : ¬(arity=1 ∧ tag=3 ∧ args.length=1) := by omega
    simp [relationProgram,headerAt,h0,h1,h2,h3,h₂]
  · intro arity tag args h₁ h₂ h₃
    have h0 : ¬(arity=2 ∧ tag<3 ∧ args.length=2) := by omega
    have h3 : ¬(arity=2 ∧ tag=3 ∧ args.length=2) := by omega
    have h4 : ¬(arity=2 ∧ tag=4 ∧ args.length=2) := by omega
    simp [functionProgram,headerAt,h₁,h0,h3,h4,h₃]

private abbrev Header := Nat × Nat × List Nat
private theorem pr_tag : Primrec (fun p : Header => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem pr_args : Primrec (fun p : Header => p.2.2) := Primrec.snd.comp Primrec.snd
private theorem pr_arg (i : Nat) : Primrec (fun p : Header => p.2.2.getD i 0) :=
  (Primrec.list_getD 0).comp pr_args (Primrec.const i)
private theorem pr_shape (arity tag count : Nat) : PrimrecPred (fun p : Header => p.1=arity ∧ p.2.1=tag ∧ p.2.2.length=count) :=
  (Primrec.eq.comp Primrec.fst (Primrec.const arity)).and
    ((Primrec.eq.comp pr_tag (Primrec.const tag)).and
      (Primrec.eq.comp (Primrec.list_length.comp pr_args) (Primrec.const count)))
private theorem pr_binaryShape : PrimrecPred (fun p : Header => p.1=2 ∧ p.2.1<3 ∧ p.2.2.length=2) :=
  (Primrec.eq.comp Primrec.fst (Primrec.const 2)).and
    ((Primrec.nat_lt.comp pr_tag (Primrec.const 3)).and
      (Primrec.eq.comp (Primrec.list_length.comp pr_args) (Primrec.const 2)))
private theorem pr_relationBody : Primrec (fun p : Header =>
    if p.1=1 ∧ p.2.1=0 ∧ p.2.2.length=1 then GorbowSortedBooleanCode.sentenceCode (p.2.2.getD 0 0)
    else if p.1=1 ∧ p.2.1=1 ∧ p.2.2.length=1 then GorbowSortedBooleanCode.fullTermCode (p.2.2.getD 0 0)
    else if p.1=1 ∧ p.2.1=2 ∧ p.2.2.length=1 then GorbowSortedBooleanCode.arithmeticTermCode (p.2.2.getD 0 0)
    else if p.1=1 ∧ p.2.1=3 ∧ p.2.2.length=1 then GorbowSortedSyntaxCode.isVariableCode (p.2.2.getD 0 0)
    else if p.1=2 ∧ p.2.1=0 ∧ p.2.2.length=2 then GorbowSortedNamedCode.namedFormula (p.2.2.getD 0 0) (p.2.2.getD 1 0)
    else false) :=
  Primrec.ite (pr_shape 1 0 1) (GorbowSortedBooleanCodeProof.uniformPrograms.2.2.1.comp (pr_arg 0))
    (Primrec.ite (pr_shape 1 1 1) (GorbowSortedBooleanCodeProof.uniformPrograms.2.2.2.1.comp (pr_arg 0))
      (Primrec.ite (pr_shape 1 2 1) (GorbowSortedBooleanCodeProof.uniformPrograms.2.2.2.2.comp (pr_arg 0))
        (Primrec.ite (pr_shape 1 3 1) (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.2.2.2.comp (pr_arg 0))
          (Primrec.ite (pr_shape 2 0 2) (GorbowSortedNamedCodeProof.uniformPrograms.2.1.comp ((pr_arg 0).pair (pr_arg 1))) (Primrec.const false)))))
private theorem pr_relation : Primrec relationProgram := by
  have h := Primrec.option_casesOn GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2 (Primrec.const false) (pr_relationBody.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by cases hd : decodeHeader code <;> simp [relationProgram,hd])

private theorem pr_all : Primrec (fun p : Header => (GorbowSortedNamedCode.allNumber (p.2.2.getD 0 0) (p.2.2.getD 1 0)).getD 0) :=
  Primrec.option_getD.comp (GorbowSortedNamedCodeProof.uniformPrograms.2.2.1.comp ((pr_arg 0).pair (pr_arg 1))) (Primrec.const 0)
private theorem pr_ex : Primrec (fun p : Header => (GorbowSortedNamedCode.exNumber (p.2.2.getD 0 0) (p.2.2.getD 1 0)).getD 0) :=
  Primrec.option_getD.comp (GorbowSortedNamedCodeProof.uniformPrograms.2.2.2.1.comp ((pr_arg 0).pair (pr_arg 1))) (Primrec.const 0)
private theorem pr_instance : Primrec (fun p : Header => (GorbowSortedNamedCode.instanceNumber (p.2.2.getD 0 0) (p.2.2.getD 1 0) (p.2.2.getD 2 0)).getD 0) :=
  Primrec.option_getD.comp (GorbowSortedNamedCodeProof.uniformPrograms.2.2.2.2.comp ((pr_arg 0).pair ((pr_arg 1).pair (pr_arg 2)))) (Primrec.const 0)
private theorem pr_functionBody : Primrec (fun p : Header =>
    if p.1=1 ∧ p.2.1=0 ∧ p.2.2.length=1 then GorbowSortedBooleanCode.unaryNumber 6 (p.2.2.getD 0 0)
    else if p.1=2 ∧ p.2.1<3 ∧ p.2.2.length=2 then GorbowSortedBooleanCode.binaryNumber (p.2.1+7) (p.2.2.getD 0 0) (p.2.2.getD 1 0)
    else if p.1=2 ∧ p.2.1=3 ∧ p.2.2.length=2 then (GorbowSortedNamedCode.allNumber (p.2.2.getD 0 0) (p.2.2.getD 1 0)).getD 0
    else if p.1=2 ∧ p.2.1=4 ∧ p.2.2.length=2 then (GorbowSortedNamedCode.exNumber (p.2.2.getD 0 0) (p.2.2.getD 1 0)).getD 0
    else if p.1=3 ∧ p.2.1=0 ∧ p.2.2.length=3 then (GorbowSortedNamedCode.instanceNumber (p.2.2.getD 0 0) (p.2.2.getD 1 0) (p.2.2.getD 2 0)).getD 0
    else 0) :=
  Primrec.ite (pr_shape 1 0 1) (GorbowSortedBooleanCodeProof.uniformPrograms.1.comp ((Primrec.const 6).pair (pr_arg 0)))
    (Primrec.ite pr_binaryShape (GorbowSortedBooleanCodeProof.uniformPrograms.2.1.comp
      ((Primrec.nat_add.comp pr_tag (Primrec.const 7)).pair ((pr_arg 0).pair (pr_arg 1))))
      (Primrec.ite (pr_shape 2 3 2) pr_all (Primrec.ite (pr_shape 2 4 2) pr_ex
        (Primrec.ite (pr_shape 3 0 3) pr_instance (Primrec.const 0)))))
private theorem pr_function : Primrec functionProgram := by
  have h := Primrec.option_casesOn GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2 (Primrec.const 0) (pr_functionBody.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by cases hd : decodeHeader code <;> simp [functionProgram,hd])

theorem uniformPrograms : Comparators.GorbowSortedRegistry.UniformPrograms := ⟨pr_relation,pr_function⟩
theorem gorbowSortedRegistry : Comparators.GorbowSortedRegistry.Target :=
  ⟨relationDispatch,functionDispatch,malformedDefaults,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof
