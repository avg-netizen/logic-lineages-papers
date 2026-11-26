import LogicLineages.PersistentMarking.SpineSyntax

namespace LogicLineages.PersistentMarking.NumberedWindowSyntax

/-- Paper16's numerical auxiliary syntax. An ordinary head has implicit
label omega. A numbered head has an actual natural label, its original
head and base, its current output type, and ordered extras. Auxiliary
application is disjoint from the ordinary head `Head.app`. -/
mutual
inductive NTerm where
  | free (type : Ty) (name : Nat)
  | bound (type : Ty) (index : Nat)
  | lam (domain : Ty) (body : NTerm)
  | bottom (type : Ty)
  | ordinary (symbol : Head) (base : NArgs)
  | numbered (symbol : Head) (output : Ty) (label : Nat) (base extras : NArgs)
  | auxApp (domain codomain : Ty) (fn arg : NTerm)
inductive NArgs where
  | nil
  | cons (term : NTerm) (tail : NArgs)
end

def NTerm.type : NTerm → Ty
  | .free σ _ | .bound σ _ | .bottom σ => σ
  | .lam σ body => .arrow σ body.type
  | .ordinary f _ => f.result
  | .numbered _ τ _ _ _ | .auxApp _ τ _ _ => τ

def NArgs.length : NArgs → Nat
  | .nil => 0
  | .cons _ rest => 1 + rest.length

def NArgs.get : NArgs → Nat → Option NTerm
  | .nil, _ => none
  | .cons a _, 0 => some a
  | .cons _ rest, i+1 => rest.get i

def NArgs.append : NArgs → NArgs → NArgs
  | .nil, ys => ys
  | .cons a rest, ys => .cons a (rest.append ys)

def NArgs.toList : NArgs → List NTerm
  | .nil => []
  | .cons a rest => a :: rest.toList

mutual
def shift (amount cutoff : Nat) : NTerm → NTerm
  | .free σ x => .free σ x
  | .bound σ i => .bound σ (if i < cutoff then i else i + amount)
  | .lam σ body => .lam σ (shift amount (cutoff + 1) body)
  | .bottom σ => .bottom σ
  | .ordinary f bs => .ordinary f (shiftArgs amount cutoff bs)
  | .numbered f τ k bs es => .numbered f τ k (shiftArgs amount cutoff bs) (shiftArgs amount cutoff es)
  | .auxApp σ τ q a => .auxApp σ τ (shift amount cutoff q) (shift amount cutoff a)
def shiftArgs (amount cutoff : Nat) : NArgs → NArgs
  | .nil => .nil
  | .cons a rest => .cons (shift amount cutoff a) (shiftArgs amount cutoff rest)
end

/- Original de Bruijn removal of an outer block, in nearest-binder-first
order; substituted arguments are shifted beneath each residual lambda.
The auxiliary constructors neither change output types nor rearrange extras. -/
mutual
def substitute (values : NArgs) (depth : Nat) : NTerm → NTerm
  | .free σ x => .free σ x
  | .bound σ i =>
    if i < depth then .bound σ i else
      match values.get (i - depth) with
      | some a => shift depth 0 a
      | none => .bound σ (i - values.length)
  | .lam σ body => .lam σ (substitute values (depth + 1) body)
  | .bottom σ => .bottom σ
  | .ordinary f bs => .ordinary f (substituteArgs values depth bs)
  | .numbered f τ k bs es => .numbered f τ k (substituteArgs values depth bs) (substituteArgs values depth es)
  | .auxApp σ τ q a => .auxApp σ τ (substitute values depth q) (substitute values depth a)
def substituteArgs (values : NArgs) (depth : Nat) : NArgs → NArgs
  | .nil => .nil
  | .cons a rest => .cons (substitute values depth a) (substituteArgs values depth rest)
end

/-- Actual left-associated auxiliary applications. This does not define,
reassociate, or replace the literal partial symbolic `Spine.apply`. -/
def applications (q : NTerm) : NArgs → Option NTerm
  | .nil => some q
  | .cons a rest =>
    match q.type with
    | .ground => none
    | .arrow σ τ =>
      if a.type = σ then applications (.auxApp σ τ q a) rest else none

def ownerCopies (f : Head) (k : Nat) (bs es : NArgs) : List Ty → NArgs
  | [] => .nil
  | τ :: rest => .cons (.numbered f τ k bs es) (ownerCopies f k bs es rest)

/-- Opening at the newly bound position is the locally nameless form of
fresh abstraction creation. The original base and extras are shifted
together before appending this single new argument. -/
def openNumbered (f : Head) (σ τ : Ty) (k : Nat) (bs es : NArgs) : NTerm :=
  .numbered f τ k (shiftArgs 1 0 bs) ((shiftArgs 1 0 es).append (.cons (.bound σ 0) .nil))

end LogicLineages.PersistentMarking.NumberedWindowSyntax
