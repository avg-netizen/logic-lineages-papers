module

public import LogicLineages.PersistentMarking.NumberedWindowPositivePathWalkPrograms
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowPositivePathAlgorithm List.Vector
open NumberedWindowPositivePathProgramTargets NumberedWindowPositivePathParserPrograms
open NumberedWindowPositivePathWalkPrograms
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowSyntaxShapePrograms (anyOption)

theorem addressPrim {step : Step} {least : Least}
    (hs : Primrec (fun p : StepInput => step p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (hl : Primrec (fun p : LeastInput => least p.1 p.2.1 p.2.2)) :
    Primrec (fun p : AddressInput => addressRS step least p.1 p.2.1 p.2.2) := by
  let P := (AddressInput × Address) × Address
  have src : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have dst : Primrec (fun p : P => p.2) := Primrec.snd
  have ctx := Primrec.fst.comp src
  have ty := Primrec.fst.comp (Primrec.snd.comp src)
  have s := Primrec.snd.comp (Primrec.snd.comp src)
  have t := Primrec.snd.comp (Primrec.snd.comp dst)
  have cert : Primrec (fun p : P => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have ctxEq := equalPrim.comp ctx (Primrec.fst.comp dst)
  have tyEq := equalPrim.comp ty (Primrec.fst.comp (Primrec.snd.comp dst))
  have path := (positivePrim hs hl).comp (ctx.pair (ty.pair (s.pair (cert.pair t))))
  have go := Primrec.and.comp (Primrec.and.comp ctxEq tyEq) path
  have fromAddress := NumberedWindowAddressProgramProof.addressPrim
  have readSrc := fromAddress.comp (Primrec.fst : Primrec (Prod.fst : AddressInput → Nat))
  have readDst : Primrec (fun p : AddressInput × Address => addressView p.1.2.2) :=
    fromAddress.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  apply (anyOption readSrc (anyOption readDst go.to₂).to₂).of_eq
  rintro ⟨a,c,b⟩
  cases h₁ : addressView a <;> cases h₂ : addressView b <;> simp [h₁,h₂,addressRS,Option.any]

private theorem indicator {α} [Primcodable α] {f : α → Bool} (h : Primrec f) :
    Primrec (fun x => if f x then 1 else 0) :=
  Primrec.ite (Primrec.eq.comp h (Primrec.const true)) (Primrec.const 1) (Primrec.const 0)

theorem programs : PositivePathPrograms := by
  intro step least hs hl
  constructor
  · let read (n : Nat) := (Encodable.decode (α := PathInput) n).getD default
    have readPrim : Primrec read := Primrec.option_getD.comp Primrec.decode (Primrec.const default)
    obtain ⟨p,hp⟩ := (GorbowPRProgram.Proof.unaryCorrespondence _).mp
      ((indicator (positivePrim hs hl)).comp readPrim)
    refine ⟨p,?_⟩
    intro ctx ty source cert target
    let data : PathInput := (ctx,ty,source,cert,target)
    have readData : read (Encodable.encode data) = data := by
      change ((Encodable.decode (Encodable.encode data) : Option PathInput).getD default) = data
      simp only [Encodable.encodek,Option.getD_some]
    have eval := hp (Encodable.encode data)
    rw [readData] at eval
    exact eval
  · have first : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
    have second := Primrec.vector_head.comp
      (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
    have third := Primrec.vector_head.comp (Primrec.vector_tail.comp
      (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
    obtain ⟨p,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
      ((indicator (addressPrim hs hl)).comp (first.pair (second.pair third)))
    exact ⟨p,fun source cert target => hp (source ::ᵥ cert ::ᵥ target ::ᵥ List.Vector.nil)⟩

end LogicLineages.PersistentMarking.NumberedWindowPositivePathProgramProof
