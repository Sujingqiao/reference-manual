```lean -show
section
variable (m : Type → Type)
open Lean.Elab.Command (CommandElabM)
```
```lean -show
end
```
```lean (name := funEval) +error
#eval fun x => x + 1
```
```leanOutput funEval
could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Nat → Nat
```
```leanOutput funEval
could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Nat → Nat
```
```lean (name := quadEval)
inductive Quadrant where
  | nw | sw | se | ne

#eval Quadrant.nw
```
```leanOutput quadEval
Quadrant.nw
```
```leanOutput quadEval
Quadrant.nw
```
```lean (name := quadEval2) +error
set_option eval.derive.repr false
#eval Quadrant.nw
```
```leanOutput quadEval2
could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Quadrant
```
```leanOutput quadEval2
could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Quadrant
```
```lean (name := plusOne)
#reduce (fun x => x + 1)
```
```leanOutput plusOne
fun x => x.succ
```
```leanOutput plusOne
fun x => x.succ
```
```lean (name := onePlus)
#reduce (fun x => 1 + x)
```
```leanOutput onePlus
fun x => (Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) x).1 1
```
```leanOutput onePlus
fun x => (Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) x).1 1
```
```lean (name := singletonList)
#check fun x => [x]
```
```leanOutput singletonList
fun x => [x] : ?m.9 → List ?m.9
```
```leanOutput singletonList
fun x => [x] : ?m.9 → List ?m.9
```
```lean (name := polyPlus)
#check fun x => x + x
```
```leanOutput polyPlus
fun x => x + x : (x : ?m.12) → ?m.19 x
```
```leanOutput polyPlus
fun x => x + x : (x : ?m.12) → ?m.19 x
```
```lean (name := oneOne)
#check_failure "one" + 1
```
```leanOutput oneOne
failed to synthesize
  HAdd String Nat ?m.32

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput oneOne
failed to synthesize
  HAdd String Nat ?m.32

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput oneOne
"one" + 1 : ?m.32
```
```leanOutput oneOne
"one" + 1 : ?m.32
```
```lean
def swap (x y : BitVec 32) : BitVec 32 × BitVec 32 :=
  (y, x)

def swap' (x y : BitVec 32) : BitVec 32 × BitVec 32 :=
  let x := x ^^^ y
  let y := x ^^^ y
  let x := x ^^^ y
  (x, y)
```
```lean
theorem swap_eq_swap' : swap = swap' := by
  funext x y
  simp only [swap, swap', Prod.mk.injEq]
  bv_decide
```
```lean (name := axioms)
#print axioms swap_eq_swap'
```
```leanOutput axioms
'swap_eq_swap'' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```
```leanOutput axioms
'swap_eq_swap'' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```
```lean (name := intersperse_eqns)
def intersperse (x : α) : List α → List α
  | y :: z :: zs => y :: x :: intersperse x (z :: zs)
  | xs => xs

#print equations intersperse
```
```leanOutput intersperse_eqns
equations:
@[defeq] theorem intersperse.eq_1.{u_1} : ∀ {α : Type u_1} (x y z : α) (zs : List α),
  intersperse x (y :: z :: zs) = y :: x :: intersperse x (z :: zs)
theorem intersperse.eq_2.{u_1} : ∀ {α : Type u_1} (x : α) (x_1 : List α),
  (∀ (y z : α) (zs : List α), x_1 = y :: z :: zs → False) → intersperse x x_1 = x_1
```
```leanOutput intersperse_eqns
equations:
@[defeq] theorem intersperse.eq_1.{u_1} : ∀ {α : Type u_1} (x y z : α) (zs : List α),
  intersperse x (y :: z :: zs) = y :: x :: intersperse x (z :: zs)
theorem intersperse.eq_2.{u_1} : ∀ {α : Type u_1} (x : α) (x_1 : List α),
  (∀ (y z : α) (zs : List α), x_1 = y :: z :: zs → False) → intersperse x x_1 = x_1
```
```lean (name := intersperse_eq_def)
#check intersperse.eq_def
```
```leanOutput intersperse_eq_def
intersperse.eq_def.{u_1} {α : Type u_1} (x : α) (x✝ : List α) :
  intersperse x x✝ =
    match x✝ with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```
```leanOutput intersperse_eq_def
intersperse.eq_def.{u_1} {α : Type u_1} (x : α) (x✝ : List α) :
  intersperse x x✝ =
    match x✝ with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```
```lean (name := intersperse_eq_unfold)
#check intersperse.eq_unfold
```
```leanOutput intersperse_eq_unfold
intersperse.eq_unfold.{u_1} :
  @intersperse = fun {α} x x_1 =>
    match x_1 with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```
```leanOutput intersperse_eq_unfold
intersperse.eq_unfold.{u_1} :
  @intersperse = fun {α} x x_1 =>
    match x_1 with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```
```lean +fresh (name := scopeInfo)
section
open Nat

namespace A
variable (n : Nat)
namespace B

open List
set_option pp.funBinderTypes true

#where

end A.B
end
```
```leanOutput scopeInfo (allowDiff := 1)
namespace A.B

open Nat List

variable (n : Nat)

set_option pp.funBinderTypes true
```
```leanOutput scopeInfo (allowDiff := 1)
namespace A.B

open Nat List

variable (n : Nat)

set_option pp.funBinderTypes true
```
```lean
def reverse : List α → List α := helper []
where
  helper acc
    | [] => acc
    | x :: xs => helper (x :: acc) xs

/-- info: [] -/
#guard_msgs in
#eval reverse ([] : List Nat)

/-- info: ['c', 'b', 'a'] -/
#guard_msgs in
#eval reverse "abc".toList
```
```lean
inductive Tree (α : Type u) : Type u where
  | val : α → Tree α
  | branches : List (Tree α) → Tree α

def Tree.big (n : Nat) : Tree Nat :=
  if n = 0 then .val 0
  else if n = 1 then .branches [.big 0]
  else .branches [.big (n / 2), .big (n / 3)]
```
```lean +error (name := bigMsg)
set_option guard_msgs.diff false
/--
info: Tree.branches
  [Tree.branches
     [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 2], Tree.branches [Tree.val 0]]],
   Tree.branches
     [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
-/
#guard_msgs in
#eval Tree.big 20
```
```leanOutput bigMsg (severity := information)
Tree.branches
  [Tree.branches
     [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]]],
   Tree.branches
     [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
```
```leanOutput bigMsg (severity := information)
Tree.branches
  [Tree.branches
     [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]]],
   Tree.branches
     [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
```
```leanOutput bigMsg (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

info: Tree.branches
  [Tree.branches
     [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]]],
   Tree.branches
     [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
```
```leanOutput bigMsg (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

info: Tree.branches
  [Tree.branches
     [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]]],
   Tree.branches
     [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
```
```lean +error (name := bigMsg')
set_option guard_msgs.diff true in
/--
info: Tree.branches
  [Tree.branches
     [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 2], Tree.branches [Tree.val 0]]],
   Tree.branches
     [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
      Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
-/
#guard_msgs in
#eval Tree.big 20
```
```leanOutput bigMsg'  (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

  info: Tree.branches
    [Tree.branches
       [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
-       Tree.branches [Tree.branches [Tree.val 2], Tree.branches [Tree.val 0]]],
+       Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]]],
     Tree.branches
       [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
        Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
```
```leanOutput bigMsg'  (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

  info: Tree.branches
    [Tree.branches
       [Tree.branches [Tree.branches [Tree.branches [Tree.val 0], Tree.val 0], Tree.branches [Tree.val 0]],
-       Tree.branches [Tree.branches [Tree.val 2], Tree.branches [Tree.val 0]]],
+       Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]]],
     Tree.branches
       [Tree.branches [Tree.branches [Tree.val 0], Tree.branches [Tree.val 0]],
        Tree.branches [Tree.branches [Tree.val 0], Tree.val 0]]]
``````lean
structure Z where
  a : Nat
  b : Nat
  canonical : a = 0 ∨ b = 0
```
```lean
def Z.mk' (n k : Nat) : Z where
  a := n - k
  b := k - n
  canonical := by omega
```
```lean
theorem Z_mk'_respects_eq :
    (Z.mk' n k = Z.mk' n' k') ↔ (n + k' = n' + k) := by
  simp [Z.mk']
  omega
```
```lean
instance : Neg Z where
  neg n := Z.mk' n.b n.a

instance : OfNat Z n where
  ofNat := Z.mk' n 0

instance : ToString Z where
  toString n :=
    if n.a = 0 then
      if n.b = 0 then "0"
      else s!"-{n.b}"
    else toString n.a
```
```lean (name := intFive)
#eval (5 : Z)
```
```leanOutput intFive
5
```
```leanOutput intFive
5
```
```lean (name := intMinusFive)
#eval (-5 : Z)
```
```leanOutput intMinusFive
-5
```
```leanOutput intMinusFive
-5
```
```lean
instance : Add Z where
  add n k := Z.mk' (n.a + k.a) (n.b + k.b)
```
```lean (name := addInt)
#eval (-5 + 22: Z)
```
```leanOutput addInt
17
```
```leanOutput addInt
17
```
```lean
def toInt (n k : Nat) : Int :=
  if n < k then - (k - n : Nat)
  else if n = k then 0
  else (n - k : Nat)
```
```lean
theorem toInt_sound :
    n + k' = k + n' ↔
    toInt n k = toInt n' k' := by
  simp only [toInt]
  split <;> split <;> omega
```
```lean -show
section
variable (r : α → α → Prop)
```
```lean -show
end
```
```lean -show
-- Check preceding para
section
variable {α : Sort u} [Setoid α]
/-- info: instHasEquivOfSetoid -/
#check_msgs in
#synth HasEquiv α
end
```
```lean
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1
```
```lean
def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega
```
```lean
instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv
```
```lean
def Z : Type := Quotient Z.instSetoid
```
```lean
def Z.mk (n : Z') : Z := Quotient.mk _ n
```
```lean
instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```
```lean -show
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n
```
```lean
def neg' : Z' → Z
  | (x, y) => .mk (y, x)
```
```lean
instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega
```
```lean
def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)
```
```lean
instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega
```
```lean -show
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n

def neg' : Z' → Z
  | (x, y) => .mk (y, x)

instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega

def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)

instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega

instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```
```lean
theorem Z.add_neg_inverse (n : Z) : n  + (-n) = 0 := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp +arith [· ≈ ·, Setoid.r, eq]
```
```lean -show
section
variable
  (α β : Sort u)
  (r : α → α → Prop)
  (f : α → β)
  (resp : ∀ x y, r x y → f x = f y)
  (x : α)
```
```lean -show
end
```
```lean -show
section
```
```lean
variable
  (r : α → α → Prop)
  (f : α → β)
  (ok : ∀ x y, r x y → f x = f y)
  (x : α)

example : Quot.lift f ok (Quot.mk r x) = f x := rfl
```
```lean -show
end
```
```lean
inductive RoseTree (α : Type u) where
  | leaf : α → RoseTree α
  | branch : List (RoseTree α) → RoseTree α
```
```lean +error (name := nestedquot)
inductive SetTree (α : Type u) where
  | leaf : α → SetTree α
  | branch :
    Quot (fun (xs ys : List (SetTree α)) => True) →
    SetTree α
```
```leanOutput nestedquot
(kernel) arg #2 of 'SetTree.branch' contains a non valid occurrence of the datatypes being declared
```
```leanOutput nestedquot
(kernel) arg #2 of 'SetTree.branch' contains a non valid occurrence of the datatypes being declared
```
```lean
variable {α : Sort u} {β : α → Sort v}

def extEq (f g : (x : α) → β x) : Prop :=
  ∀ x, f x = g x

def ExtFun (α : Sort u) (β : α → Sort v) :=
  Quot (@extEq α β)
```
```lean
def extApp
    (f : ExtFun α β)
    (x : α) :
    β x :=
  f.lift (· x) fun g g' h => by
    exact h x
```
```lean -show
section
variable (f : (x : α) → β x)
```
```leanTerm
extApp (Quot.mk _ f)
```
```leanTerm
fun x => (Quot.mk extEq f).lift (· x) (fun _ _ h => h x)
```
```lean -show
end
```
```lean
theorem funext'
    {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) :
    f = g := by
  suffices extApp (Quot.mk _ f) = extApp (Quot.mk _ g) by
    unfold extApp at this
    dsimp at this
    exact this
  suffices Quot.mk extEq f = Quot.mk extEq g by
    apply congrArg
    exact this
  apply Quot.sound
  exact h
```
```lean -show
section
variable {α : Sort u}
```
```lean -show
end
``````lean -show
axiom α : Type
axiom β : Type
axiom f : α → β

structure S where
  f1 : α
  f2 : β

axiom x : S

-- test claims in next para

example : (fun x => f x) = f := by rfl
example : S.mk x.f1 x.f2 = x := by rfl

export S (f1 f2)
```
```lean
def LengthList (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => α × LengthList α n
```
```lean
example : LengthList Int 0 := ()

example : LengthList String 2 :=
  ("Hello", "there", ())
```
```lean +error (name := wrongNum)
example : LengthList String 5 :=
  ("Wrong", "number", ())
```
```leanOutput wrongNum
Application type mismatch: The argument
  ()
has type
  Unit
but is expected to have type
  LengthList String 3
in the application
  ("number", ())
```
```leanOutput wrongNum
Application type mismatch: The argument
  ()
has type
  Unit
but is expected to have type
  LengthList String 3
in the application
  ("number", ())
```
```lean
example : Sort 5 := Sort 4
example : Sort 2 := Sort 1
```
```lean +error (name := sort3)
example : Sort 5 := Sort 3
```
```leanOutput sort3
Type mismatch
  Type 2
has type
  Type 3
of sort `Type 4` but is expected to have type
  Type 4
of sort `Type 5`
```
```leanOutput sort3
Type mismatch
  Type 2
has type
  Type 3
of sort `Type 4` but is expected to have type
  Type 4
of sort `Type 5`
```
```lean
example : Sort 1 := Unit
```
```lean +error (name := unit1)
example : Sort 2 := Unit
```
```leanOutput unit1
Type mismatch
  Unit
has type
  Type
of sort `Type 1` but is expected to have type
  Type 1
of sort `Type 2`
```
```leanOutput unit1
Type mismatch
  Unit
has type
  Type
of sort `Type 1` but is expected to have type
  Type 1
of sort `Type 2`
```
```lean
example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2
```
```lean
example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x
```
```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```
```lean +error (name := toosmall)
example (α : Type 2) (β : Type 1) : Type 1 := α → β
```
```leanOutput toosmall
Type mismatch
  α → β
has type
  Type 2
of sort `Type 3` but is expected to have type
  Type 1
of sort `Type 2`
```
```leanOutput toosmall
Type mismatch
  α → β
has type
  Type 2
of sort `Type 3` but is expected to have type
  Type 1
of sort `Type 2`
```
```lean +error (name := toobig)
example (α : Type 2) (β : Type 1) : Type 3 := α → β
```
```leanOutput toobig
Type mismatch
  α → β
has type
  Type 2
of sort `Type 3` but is expected to have type
  Type 3
of sort `Type 4`
```
```leanOutput toobig
Type mismatch
  α → β
has type
  Type 2
of sort `Type 3` but is expected to have type
  Type 3
of sort `Type 4`
```
```lean
structure Codec.{u} : Type (u + 1) where
  type : Type u
  encode : Array UInt32 → type → Array UInt32
  decode : Array UInt32 → Nat → Option (type × Nat)
```
```lean
def Codec.char : Codec where
  type := Char
  encode buf ch := buf.push ch.val
  decode buf i := do
    let v ← buf[i]?
    if h : v.isValidChar then
      let ch : Char := ⟨v, h⟩
      return (ch, i + 1)
    else
      failure
```
```lean +error (name := uniIncomp)
opaque T.{u} (_ : Nat) : Bool :=
  (fun (α : Sort u) => true) PUnit.{u}

set_option pp.universes true

def test.{u, v} : T.{u} 0 = T.{v} 0 := rfl
```
```leanOutput uniIncomp
Type mismatch
  rfl.{?u.46}
has type
  Eq.{?u.46} ?m.48 ?m.48
but is expected to have type
  Eq.{1} (T.{u} 0) (T.{v} 0)
```
```leanOutput uniIncomp
Type mismatch
  rfl.{?u.46}
has type
  Eq.{?u.46} ?m.48 ?m.48
but is expected to have type
  Eq.{1} (T.{u} 0) (T.{v} 0)
```
```lean
def id' (x : α) := x
```
```lean
partial def count [Monad m] (p : α → Bool) (act : m α) : m Nat := do
  if p (← act) then
    return 1 + (← count p act)
  else
    return 0
```
```lean -show
/-- info: Nat : Type -/
#check_msgs in
#check Nat

/--
info: count.{u_1} {m : Type → Type u_1} {α : Type} [Monad m] (p : α → Bool) (act : m α) : m Nat
-/
#check_msgs in
#check count
```
```lean
def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    List.{u} α → List.{v} β
  | [] => []
  | x :: xs => f x :: map f xs
```
```lean -keep
set_option autoImplicit true
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```lean +error (name := uv)
set_option autoImplicit false
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```leanOutput uv
unknown universe level `u`
```
```leanOutput uv
unknown universe level `u`
```
```leanOutput uv
unknown universe level `v`
```
```leanOutput uv
unknown universe level `v`
```
```lean -keep
set_option autoImplicit false
universe u
def id₃ (α : Type u) (a : α) := a
```
```lean -keep
def L.{u} := List (Type u)
```
```lean +error (name := unknownUni) -keep
set_option autoImplicit true
def L := List (Type u)
```
```leanOutput unknownUni
unknown universe level `u`
```
```leanOutput unknownUni
unknown universe level `u`
```
```lean -keep
universe u
def L := List (Type u)
```
```lean
universe u
def L := List (Type 0)
#check L
```