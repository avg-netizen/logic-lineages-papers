module

public import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchPathPrograms
import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
import LogicLineages.PersistentMarking.NumberedWindowScalarProgramProof
import LogicLineages.PersistentMarking.NumberedWindowSyntaxShapePrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProgramChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowApplicationMatch NumberedWindowApplicationMatchProgramTargets
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowAddressApplication (application arrowView)
open NumberedWindowAddressApplicationProgramProof (applicationPrim)
open NumberedWindowAddressProgramProof (addressPrim)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowScalarProgramProof (leastPrim)
open NumberedWindowClassApplicationPath (liftPath)
open NumberedWindowApplicationMatchPathPrograms (liftPathScopedPrim)

private abbrev Inputs := Nat × Nat × Nat
private abbrev Parsed := List Nat × Nat × Nat × Nat
private abbrev Found := (Inputs × Parsed) × Nat

private theorem arrowPrim : Primrec arrowView := by
  apply (Primrec.nat_casesOn₁ none NumberedWindowSyntaxShapePrograms.pairs).of_eq
  intro n
  cases n <;> rfl

private def readInputs (p : Inputs) : Option Parsed :=
  (addressView p.1).bind fun q =>
    (arrowView q.2.1).bind fun ty =>
      (addressView p.2.1).map fun u => (q.1,ty.1,ty.2,u.2.2)

private theorem readInputsPrim : Primrec readInputs := by
  let Source := Inputs × Address
  let Arrow := Source × (Nat × Nat)
  let Result := Arrow × Address
  have arg : Primrec (fun p : Arrow => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have ctx : Primrec (fun p : Result => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have types : Primrec (fun p : Result => p.1.2) := Primrec.snd.comp Primrec.fst
  have input : Primrec (fun p : Result => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have output := ctx.pair ((Primrec.fst.comp types).pair ((Primrec.snd.comp types).pair input))
  have fromArrow := Primrec.option_map (addressPrim.comp arg) output.to₂
  have fromSource := Primrec.option_bind
    (arrowPrim.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : Source → Address)))))
    fromArrow.to₂
  exact Primrec.option_bind (addressPrim.comp Primrec.fst) fromSource.to₂

private def finish (s : Settings) (p : Found) : Option (Nat × Nat) :=
  (addressView p.2).bind fun canonical =>
    let fields := p.1.2
    (liftPath (least s fields.1 fields.2.2.1) fields.2.1 fields.2.2.1
      fields.2.2.2 canonical.2.2 p.1.1.2.2).map fun result => (p.2,result.2)

private theorem finishPrim (s : Settings) : Primrec (finish s) := by
  let Row := Found × Address
  have fields : Primrec (fun p : Row => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ctx := Primrec.fst.comp fields
  have domain := Primrec.fst.comp (Primrec.snd.comp fields)
  have result := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp fields))
  have input := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp fields))
  have start : Primrec (fun p : Row => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have cert : Primrec (fun p : Row => p.1.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have scope := ctx.pair result
  have config := scope.pair (domain.pair (result.pair input))
  have supplied := (liftPathScopedPrim (fun sc q => least s sc.1 sc.2 q)
    (leastPrim s).to₂).comp (config.pair (start.pair cert))
  have before : Primrec (fun p : Row => p.1.2) := Primrec.snd.comp Primrec.fst
  have returned := (before.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)
  have checked := Primrec.option_map supplied returned.to₂
  exact Primrec.option_bind (addressPrim.comp Primrec.snd) checked.to₂

private theorem matchingPrim (s : Settings) :
    Primrec (fun p : Inputs => matchingCertificate s p.1 p.2.1 p.2.2) := by
  let Known := Inputs × Parsed
  have source : Primrec (fun p : Known => p.1.1) := Primrec.fst.comp Primrec.fst
  have arg : Primrec (fun p : Known => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have fromKnown := Primrec.option_bind ((applicationPrim s).comp source arg) (finishPrim s).to₂
  apply (Primrec.option_bind readInputsPrim fromKnown.to₂).of_eq
  intro p
  change (readInputs p).bind (fun fields =>
    (application s p.1 p.2.1).bind (fun before => finish s ((p,fields),before))) = _
  unfold readInputs matchingCertificate
  cases src : addressView p.1 with
  | none => simp [src]
  | some q =>
    rcases q with ⟨ctx,ft,_⟩
    cases ty : arrowView ft with
    | none => simp [src,ty]
    | some types =>
      rcases types with ⟨domain,result⟩
      cases arg : addressView p.2.1 with
      | none => simp [src,ty,arg]
      | some u =>
        rcases u with ⟨_,_,input⟩
        cases has : application s p.1 p.2.1 with
        | none => simp [src,ty,arg,has]
        | some before =>
          cases view : addressView before with
          | none => simp [src,ty,arg,has,finish,view]
          | some a =>
            rcases a with ⟨_,_,start⟩
            cases cert : liftPath (least s ctx result) domain result input start p.2.2 with
            | none => simp [src,ty,arg,has,finish,view,cert]
            | some output =>
              rcases output with ⟨_,proof⟩
              simp [src,ty,arg,has,finish,view,cert]

theorem exact_ApplicationMatchProgram : ApplicationMatchProgram := by
  intro s
  let V := List.Vector Nat 3
  have f : Primrec (fun v : V => v.head) := Primrec.vector_head
  have tf : Primrec (fun v : V => v.tail) := Primrec.vector_tail
  have u := Primrec.vector_head.comp tf
  have tu := Primrec.vector_tail.comp tf
  have certificate := Primrec.vector_head.comp tu
  have inspect := (matchingPrim s).comp (f.pair (u.pair certificate))
  obtain ⟨p,h⟩ := Proof.allPrimitiveFunctions 3 _ (Primrec.encode.comp inspect)
  exact ⟨p,fun f u certificate => h (f ::ᵥ u ::ᵥ certificate ::ᵥ nil)⟩

#print axioms exact_ApplicationMatchProgram

end LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProgramChecks
