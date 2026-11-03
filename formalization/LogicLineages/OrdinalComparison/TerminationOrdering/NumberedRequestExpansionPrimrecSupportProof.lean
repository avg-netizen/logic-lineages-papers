module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecSupportProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedTypedRequests NumberedRequestPresentation NumberedCodeView
open NumberedTypeCodecPrimrec NumberedTypeCodecPrimrecSupportProof
open NumberedHeadSignaturePrimrecProof

/-- Sum elimination retains an unchanged common parameter. -/
def withSum {A B C D : Type} (f : A × B → D) (g : A × C → D)
    (p : A × (B ⊕ C)) : D :=
  p.2.elim (fun b => f (p.1, b)) (fun c => g (p.1, c))

theorem withSumPrimitive {A B C D : Type}
    [Primcodable A] [Primcodable B] [Primcodable C] [Primcodable D]
    {f : A × B → D} {g : A × C → D} (hf : Primrec f) (hg : Primrec g) :
    Primrec (withSum f g) :=
  Primrec.sumCasesOn Primrec.snd
    (hf.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
    (hg.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem termPrimitive {A : Type} [Primcodable A] (n : Nat)
    {Gamma : A → List Ty} {tau : A → Ty} {code : A → Code (Fin n)}
    (hGamma : Primrec Gamma) (htau : Primrec tau) (hcode : Primrec code) :
    Primrec (fun a => Request.term (Gamma a) (tau a) (code a)) :=
  (termRequestPrimitive n).comp (hGamma.pair (htau.pair hcode))

theorem argumentsPrimitive {A : Type} [Primcodable A] (n : Nat)
    {Gamma types : A → List Ty} {code : A → Code (Fin n)}
    (hGamma : Primrec Gamma) (htypes : Primrec types) (hcode : Primrec code) :
    Primrec (fun a => Request.arguments (Gamma a) (types a) (code a)) :=
  (argumentsRequestPrimitive n).comp (hGamma.pair (htypes.pair hcode))

theorem singletonSomePrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → B} (hf : Primrec f) : Primrec (fun a => some [f a]) :=
  Primrec.option_some.comp (Primrec.list_cons.comp hf (Primrec.const []))

theorem pairSomePrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f g : A → B} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => some [f a, g a]) :=
  Primrec.option_some.comp
    (Primrec.list_cons.comp hf (Primrec.list_cons.comp hg (Primrec.const [])))

/-- The genuine arrow fields of the expected type; ground has no fields. -/
def arrowParts : Ty → Option (Ty × Ty)
  | .ground => none
  | .arrow domain result => some (domain, result)

theorem arrowPartsPrimitive : Primrec arrowParts := by
  have h : Primrec (fun value : Nat => (Nat.casesOn value none
      (fun payload => some (typeEquiv.symm (Nat.unpair payload).1,
        typeEquiv.symm (Nat.unpair payload).2)) : Option (Ty × Ty))) :=
    Primrec.nat_casesOn Primrec.id (Primrec.const none)
      (Primrec.option_some.comp
        ((typeFrom.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).pair
          (typeFrom.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))).to₂
  apply (h.comp typeTo).of_eq
  intro tau
  cases tau with
  | ground => rfl
  | arrow domain result =>
    have he : typeEquiv (.arrow domain result) =
        Nat.succ (Nat.pair (typeEquiv domain) (typeEquiv result)) := by
      change 1 + Nat.pair (typeEquiv domain) (typeEquiv result) =
        Nat.pair (typeEquiv domain) (typeEquiv result) + 1
      exact Nat.add_comm 1 _
    rw [he]
    simp only [Nat.unpair_pair, Equiv.symm_apply_apply, arrowParts]

def variableExpansion (n : Nat) (p : (List Ty × Ty) × Nat) : Option (List (Request n)) :=
  if p.1.1[p.2]? = some p.1.2 then some [] else none

theorem variableExpansionPrimitive (n : Nat) : Primrec (variableExpansion n) :=
  Primrec.ite
    (Primrec.eq.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.const (some [])) (Primrec.const none)

def lambdaExpansion (n : Nat) (p : (List Ty × Ty) × (Ty × Code (Fin n))) :
    Option (List (Request n)) :=
  (arrowParts p.1.2).bind fun parts =>
    if p.2.1 = parts.1 then some [.term (parts.1 :: p.1.1) parts.2 p.2.2] else none

theorem lambdaExpansionPrimitive (n : Nat) : Primrec (lambdaExpansion n) := by
  have h : Primrec (fun p : ((List Ty × Ty) × (Ty × Code (Fin n))) × (Ty × Ty) =>
      if p.1.2.1 = p.2.1 then
        some [Request.term (p.2.1 :: p.1.1.1) p.2.2 p.1.2.2] else none) :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (singletonSomePrimitive (termPrimitive n
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.const none)
  exact Primrec.option_bind (arrowPartsPrimitive.comp (Primrec.snd.comp Primrec.fst)) h.to₂

def applicationExpansion (n : Nat) (p : (List Ty × Ty) × (Ty × Code (Fin n) × Code (Fin n))) :
    Option (List (Request n)) :=
  some [.term p.1.1 (.arrow p.2.1 p.1.2) p.2.2.1, .term p.1.1 p.2.1 p.2.2.2]

theorem applicationExpansionPrimitive (n : Nat) : Primrec (applicationExpansion n) :=
  pairSomePrimitive
    (termPrimitive n (Primrec.fst.comp Primrec.fst)
      (arrowPrimitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (termPrimitive n (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

def bottomExpansion (n : Nat) (p : (List Ty × Ty) × Ty) : Option (List (Request n)) :=
  if p.2 = p.1.2 then some [] else none

theorem bottomExpansionPrimitive (n : Nat) : Primrec (bottomExpansion n) :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
    (Primrec.const (some [])) (Primrec.const none)

def ordinaryExpansion (n : Nat) (arity : Fin n → Nat)
    (p : (List Ty × Ty) × (HeadCode (Fin n) × Code (Fin n))) : Option (List (Request n)) :=
  if headResult (decodeHead p.2.1) = p.1.2 then
    some [.arguments p.1.1 (headArguments arity (decodeHead p.2.1)) p.2.2] else none

theorem ordinaryExpansionPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (ordinaryExpansion n arity) :=
  Primrec.ite
    (Primrec.eq.comp ((headResultPrimitive n).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst))
    (singletonSomePrimitive (argumentsPrimitive n (Primrec.fst.comp Primrec.fst)
      ((headArgumentsPrimitive n arity).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)))
    (Primrec.const none)

abbrev NumberedFields (n : Nat) :=
  Nat × HeadCode (Fin n) × Ty × Code (Fin n) × List Ty × Code (Fin n)

def numberedExpansion (n : Nat) (arity : Fin n → Nat)
    (p : (List Ty × Ty) × NumberedFields n) : Option (List (Request n)) :=
  if p.2.2.2.1 = p.1.2 then
    some [.arguments p.1.1 (headArguments arity (decodeHead p.2.2.1)) p.2.2.2.2.1,
      .arguments p.1.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2] else none

theorem numberedExpansionPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (numberedExpansion n arity) := by
  have htail : Primrec (fun p : (List Ty × Ty) × NumberedFields n => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hresult : Primrec (fun p : (List Ty × Ty) × NumberedFields n => p.2.2.2) :=
    Primrec.snd.comp htail
  have hbase : Primrec (fun p : (List Ty × Ty) × NumberedFields n => p.2.2.2.2) :=
    Primrec.snd.comp hresult
  have hextras : Primrec (fun p : (List Ty × Ty) × NumberedFields n => p.2.2.2.2.2) :=
    Primrec.snd.comp hbase
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp hresult) (Primrec.snd.comp Primrec.fst))
    (pairSomePrimitive
      (argumentsPrimitive n (Primrec.fst.comp Primrec.fst)
        ((headArgumentsPrimitive n arity).comp (Primrec.fst.comp htail))
        (Primrec.fst.comp hbase))
      (argumentsPrimitive n (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp hextras) (Primrec.snd.comp hextras)))
    (Primrec.const none)

def termViewExpansion (n : Nat) (arity : Fin n → Nat) :
    (List Ty × Ty) × CodeView n → Option (List (Request n)) :=
  withSum (variableExpansion n)
    (withSum (lambdaExpansion n)
      (withSum (applicationExpansion n)
        (withSum (bottomExpansion n)
          (withSum (ordinaryExpansion n arity)
            (withSum (numberedExpansion n arity)
              (withSum (fun _ => none) (fun _ => none)))))))

theorem termViewPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (termViewExpansion n arity) :=
  withSumPrimitive (variableExpansionPrimitive n)
    (withSumPrimitive (lambdaExpansionPrimitive n)
      (withSumPrimitive (applicationExpansionPrimitive n)
        (withSumPrimitive (bottomExpansionPrimitive n)
          (withSumPrimitive (ordinaryExpansionPrimitive n arity)
            (withSumPrimitive (numberedExpansionPrimitive n arity)
              (withSumPrimitive (Primrec.const none) (Primrec.const none)))))))

def argumentsNilExpansion (n : Nat) (p : (List Ty × List Ty) × Unit) :
    Option (List (Request n)) :=
  if p.1.2 = [] then some [] else none

theorem argumentsNilExpansionPrimitive (n : Nat) : Primrec (argumentsNilExpansion n) :=
  Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const []))
    (Primrec.const (some [])) (Primrec.const none)

def argumentsConsExpansion (n : Nat)
    (p : (List Ty × List Ty) × (Ty × Code (Fin n) × Code (Fin n))) :
    Option (List (Request n)) :=
  match p.1.2 with
  | [] => none
  | domain :: tail =>
    if p.2.1 = domain then
      some [.term p.1.1 domain p.2.2.1, .arguments p.1.1 tail p.2.2.2] else none

theorem argumentsConsExpansionPrimitive (n : Nat) : Primrec (argumentsConsExpansion n) := by
  have h : Primrec (fun p : ((List Ty × List Ty) × (Ty × Code (Fin n) × Code (Fin n))) ×
      (Ty × List Ty) =>
      if p.1.2.1 = p.2.1 then
        some [Request.term p.1.1.1 p.2.1 p.1.2.2.1,
          Request.arguments p.1.1.1 p.2.2 p.1.2.2.2] else none) :=
    Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (pairSomePrimitive
        (termPrimitive n (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
        (argumentsPrimitive n (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
      (Primrec.const none)
  apply (Primrec.list_casesOn (Primrec.snd.comp Primrec.fst) (Primrec.const none) h.to₂).of_eq
  intro p
  rcases p with ⟨⟨Gamma, types⟩, payload⟩
  cases types <;> rfl

def argumentsViewExpansion (n : Nat) :
    (List Ty × List Ty) × CodeView n → Option (List (Request n)) :=
  withSum (fun _ => none) (withSum (fun _ => none) (withSum (fun _ => none)
    (withSum (fun _ => none) (withSum (fun _ => none) (withSum (fun _ => none)
      (withSum (argumentsNilExpansion n) (argumentsConsExpansion n)))))))

theorem argumentsViewPrimitive (n : Nat) : Primrec (argumentsViewExpansion n) :=
  withSumPrimitive (Primrec.const none) (withSumPrimitive (Primrec.const none)
    (withSumPrimitive (Primrec.const none) (withSumPrimitive (Primrec.const none)
      (withSumPrimitive (Primrec.const none) (withSumPrimitive (Primrec.const none)
        (withSumPrimitive (argumentsNilExpansionPrimitive n) (argumentsConsExpansionPrimitive n)))))))

theorem termViewExact (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty)
    (code : Code (Fin n)) :
    termViewExpansion n arity ((Gamma, tau), view code) = expand arity (.term Gamma tau code) := by
  cases code with
  | var index => rfl
  | lam sigma body => cases tau <;> rfl
  | app sigma q a => rfl
  | bottom result => rfl
  | ordinary head base => rfl
  | numbered k head result base types extras => rfl
  | argumentsNil => rfl
  | argumentsCons sigma q rest => rfl

theorem argumentsViewExact (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (code : Code (Fin n)) :
    argumentsViewExpansion n ((Gamma, types), view code) =
      expand arity (.arguments Gamma types code) := by
  cases code <;> cases types <;> rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecSupportProof
