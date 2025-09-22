```lean
set_option trace.compiler.ir.result true
```
```lean (name := p1)
def process (str : String) : String × String :=
  (str.set 0 ' ', "")
```
```lean (name := p2)
def process' (str : String) : String × String:=
  (str.set 0 ' ', str)
```
```leanOutput p1 (allowDiff := 5)
[Compiler.IR] [result]
    def process._closed_0 : obj :=
      let x_1 : obj := "";
      ret x_1
    def process (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := process._closed_0;
      let x_6 : obj := ctor_0[Prod.mk] x_4 x_5;
      ret x_6
```
```leanOutput p1 (allowDiff := 5)
[Compiler.IR] [result]
    def process._closed_0 : obj :=
      let x_1 : obj := "";
      ret x_1
    def process (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := process._closed_0;
      let x_6 : obj := ctor_0[Prod.mk] x_4 x_5;
      ret x_6
```
```leanOutput p2
[Compiler.IR] [result]
    def process' (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      inc x_1;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := ctor_0[Prod.mk] x_4 x_1;
      ret x_5
```
```leanOutput p2
[Compiler.IR] [result]
    def process' (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      inc x_1;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := ctor_0[Prod.mk] x_4 x_1;
      ret x_5
```
```lean (name := discardElems)
set_option trace.compiler.ir.result true

def discardElems : List α → List Unit
  | [] => []
  | x :: xs => () :: discardElems xs
```
```leanOutput discardElems
[Compiler.IR] [result]
    def discardElems._redArg (x_1 : tobj) : tobj :=
      case x_1 : tobj of
      List.nil →
        let x_2 : tagged := ctor_0[List.nil];
        ret x_2
      List.cons →
        let x_3 : u8 := isShared x_1;
        case x_3 : u8 of
        Bool.false →
          let x_4 : tobj := proj[1] x_1;
          let x_5 : tobj := proj[0] x_1;
          dec x_5;
          let x_6 : tagged := ctor_0[PUnit.unit];
          let x_7 : tobj := discardElems._redArg x_4;
          set x_1[1] := x_7;
          set x_1[0] := x_6;
          ret x_1
        Bool.true →
          let x_8 : tobj := proj[1] x_1;
          inc x_8;
          dec x_1;
          let x_9 : tagged := ctor_0[PUnit.unit];
          let x_10 : tobj := discardElems._redArg x_8;
          let x_11 : obj := ctor_1[List.cons] x_9 x_10;
          ret x_11
    def discardElems (x_1 : ◾) (x_2 : tobj) : tobj :=
      let x_3 : tobj := discardElems._redArg x_2;
      ret x_3
```
```leanOutput discardElems
[Compiler.IR] [result]
    def discardElems._redArg (x_1 : tobj) : tobj :=
      case x_1 : tobj of
      List.nil →
        let x_2 : tagged := ctor_0[List.nil];
        ret x_2
      List.cons →
        let x_3 : u8 := isShared x_1;
        case x_3 : u8 of
        Bool.false →
          let x_4 : tobj := proj[1] x_1;
          let x_5 : tobj := proj[0] x_1;
          dec x_5;
          let x_6 : tagged := ctor_0[PUnit.unit];
          let x_7 : tobj := discardElems._redArg x_4;
          set x_1[1] := x_7;
          set x_1[0] := x_6;
          ret x_1
        Bool.true →
          let x_8 : tobj := proj[1] x_1;
          inc x_8;
          dec x_1;
          let x_9 : tagged := ctor_0[PUnit.unit];
          let x_10 : tobj := discardElems._redArg x_8;
          let x_11 : obj := ctor_1[List.cons] x_9 x_10;
          ret x_11
    def discardElems (x_1 : ◾) (x_2 : tobj) : tobj :=
      let x_3 : tobj := discardElems._redArg x_2;
      ret x_3
```
```lean -show
variable {α₁ αₙ β αᵢ}
private axiom «α₂→…→αₙ₋₁».{u} : Type u
local macro "..." : term => ``(«α₂→…→αₙ₋₁»)
```
```lean -show
universe u
variable (p : Prop)
private axiom «...» : Sort u
local macro "..." : term => ``(«...»)
```
```lean -show
  variable (u : Unit)
  ``````lean +error (name := mutScope) -keep
mutual
  abbrev NaturalNum : Type := Nat
  def n : NaturalNum := 5
end
```
```leanOutput mutScope
Unknown identifier `NaturalNum`
```
```leanOutput mutScope
Unknown identifier `NaturalNum`
```
```lean
abbrev NaturalNum : Type := Nat
def n : NaturalNum := 5
```
```lean +error (name := mutScopeTwo) -keep
mutual
  abbrev α : Type := Nat
  def identity (x : α) : α := x
end
```
```leanOutput mutScopeTwo
Unknown identifier `α`
```
```leanOutput mutScopeTwo
Unknown identifier `α`
```
```lean
mutual
  abbrev α : Type := Nat
  def identity (x : β) : β := x
end
```
```lean
def isPrime (n : Nat) : Bool := Id.run do
  for i in [2:n] do
    if i * i > n then return true
    if n % i = 0 then return false
  return true

partial def nextPrime (n : Nat) : Nat :=
  let n := n + 1
  if isPrime n then n else nextPrime n
```
```lean
def answerUser (n : Nat) : String :=
  s!"The next prime is {nextPrime n}"

def answerOtherUser (n : Nat) : String :=
  " ".intercalate [
    "The",
    "next",
    "prime",
    "is",
    toString (nextPrime n)
  ]
```
```lean
theorem answer_eq_other : answerUser = answerOtherUser := by
  funext n
  simp only [answerUser, answerOtherUser]
  simp only [toString, String.append_empty]
  rfl
```
```lean
inductive Tree α where
  | empty
  | branch (left : Tree α) (val : α) (right : Tree α)
```
```lean
unsafe def Tree.fastBEq [BEq α] (t1 t2 : Tree α) : Bool :=
  if ptrEq t1 t2 then
    true
  else
    match t1, t2 with
    | .empty, .empty => true
    | .branch l1 x r1, .branch l2 y r2 =>
      if ptrEq x y || x == y then
        l1.fastBEq l2 && r1.fastBEq r2
      else false
    | _, _ => false
```
```lean
@[implemented_by Tree.fastBEq]
opaque Tree.beq [BEq α] (t1 t2 : Tree α) : Bool

instance [BEq α] : BEq (Tree α) where
  beq := Tree.beq
```
```lean
unsafe def unFinImpl (xs : List (Fin n)) : List Nat :=
  unsafeCast xs

@[implemented_by unFinImpl]
def unFin (xs : List (Fin n)) : List Nat :=
  xs.map Fin.val
```
```lean
theorem unFin_length_eq_length {xs : List (Fin n)} :
    (unFin xs).length = xs.length := by
  simp [unFin]
```
```lean
abbrev Phrase := String

def Clause := String

@[irreducible]
def Utterance := String
```
```lean
def hello : Phrase := "Hello"

def goodMorning : Clause := "Good morning"
```
```lean +error (name := irred)
def goodEvening : Utterance := "Good evening"
```
```leanOutput irred
Type mismatch
  "Good evening"
has type
  String
but is expected to have type
  Utterance
```
```leanOutput irred
Type mismatch
  "Good evening"
has type
  String
but is expected to have type
  Utterance
```
```lean
#synth ToString Phrase
```
```lean +error (name := toStringClause)
#synth ToString Clause
```
```leanOutput toStringClause
failed to synthesize
  ToString Clause

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput toStringClause
failed to synthesize
  ToString Clause

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean
instance : ToString Clause := inferInstanceAs (ToString String)
```
```lean
def Sequence := List

def Sequence.ofList (xs : List α) : Sequence α := xs
```
```lean
#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```
```lean +error (name := irredSeq)
attribute [irreducible] Sequence

#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```
```leanOutput irredSeq
Invalid field `reverse`: The environment does not contain `Sequence.reverse`
  xs
has type
  Sequence Nat
```
```leanOutput irredSeq
Invalid field `reverse`: The environment does not contain `Sequence.reverse`
  xs
has type
  Sequence Nat
```
```lean
abbrev plus := Nat.add

def sum := Nat.add

@[irreducible]
def tally := Nat.add
```
```lean
theorem plus_eq_add : plus x y = x + y := by simp
```
```lean -keep +error (name := simpSemi)
theorem sum_eq_add : sum x y = x + y := by simp
```
```lean
theorem sum_eq_add : sum x y = x + y := by rfl
```
```lean  -keep +error (name := reflIr)
theorem tally_eq_add : tally x y = x + y := by rfl
```
```lean  -keep (name := simpName)
theorem tally_eq_add : tally x y = x + y := by simp [tally]
```
```lean
theorem tally_eq_add : tally x y = x + y := by with_unfolding_all rfl
``````lean -show
-- Just make sure that the `deriving` clause is legit
class A (n : Nat) where
  k : Nat
  eq : n = k
deriving DecidableEq
```
```lean +error (name := notClass)
def f [n : Nat] : n = n := rfl
```
```leanOutput notClass
invalid binder annotation, type is not a class instance
  Nat

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
```
```leanOutput notClass
invalid binder annotation, type is not a class instance
  Nat

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
```
```lean
namespace S
structure Magma (α : Type u) where
  op : α → α → α

structure Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

structure Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end S

namespace C1
class Monoid (α : Type u) extends S.Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C1

namespace C2
class Magma (α : Type u) where
  op : α → α → α

class Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

class Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C2
```
```lean
structure Heap (α : Type u) where
  contents : Array α
deriving Repr

def Heap.bubbleUp [Ord α] (i : Nat) (xs : Heap α) : Heap α :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if Ord.compare xs.contents[i] xs.contents[j] == .lt then
      Heap.bubbleUp j { xs with contents := xs.contents.swap i j }
    else xs

def Heap.insert [Ord α] (x : α) (xs : Heap α) : Heap α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
```
```lean
structure Heap' (α : Type u) [Ord α] where
  contents : Array α

def Heap'.bubbleUp [inst : Ord α]
    (i : Nat) (xs : @Heap' α inst) :
    @Heap' α inst :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if inst.compare xs.contents[i] xs.contents[j] == .lt then
      Heap'.bubbleUp j {xs with contents := xs.contents.swap i j}
    else xs

def Heap'.insert [Ord α] (x : α) (xs : Heap' α) : Heap' α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
```
```lean
class abbrev AddMul (α : Type u) := Add α, Mul α

def plusTimes1 [AddMul α] (x y z : α) := x + y * z

class AddMul' (α : Type u) extends Add α, Mul α

def plusTimes2 [AddMul' α] (x y z : α) := x + y * z
```
```lean (name := plusTimes1)
#eval plusTimes1 2 5 7
```
```leanOutput plusTimes1
37
```
```leanOutput plusTimes1
37
```
```lean (name := plusTimes2a) +error
#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2a
failed to synthesize
  AddMul' ?m.22

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput plusTimes2a
failed to synthesize
  AddMul' ?m.22

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```lean (name := plusTimes2b)
instance [Add α] [Mul α] : AddMul' α where

#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2b
37
```
```leanOutput plusTimes2b
37
```
```lean
structure A where
structure B where

deriving instance BEq, Repr for A, B
```
```lean
#synth BEq A
#synth BEq B
#synth Repr A
#synth Repr B
``````lean
def Greetings.english := "Hello"
```
```lean +error (name := english1)
#eval english
```
```leanOutput english1
Unknown identifier `english`
```
```leanOutput english1
Unknown identifier `english`
```
```lean
section Greetings
```
```lean +error  (name := english2)
#eval english
```
```leanOutput english2
Unknown identifier `english`
```
```leanOutput english2
Unknown identifier `english`
```
```lean  (name := english3)
open Greetings

#eval english
```
```leanOutput english3
"Hello"
```
```leanOutput english3
"Hello"
```
```lean +error (name := english4) -keep
end
```
```leanOutput english4
Missing name after `end`: Expected the current scope name `Greetings`

Hint: To end the current scope `Greetings`, specify its name:
  end ̲G̲r̲e̲e̲t̲i̲n̲g̲s̲
```
```leanOutput english4
Missing name after `end`: Expected the current scope name `Greetings`

Hint: To end the current scope `Greetings`, specify its name:
  end ̲G̲r̲e̲e̲t̲i̲n̲g̲s̲
```
```lean
end Greetings
```
```lean +error  (name := english5)
#eval english
```
```leanOutput english5
Unknown identifier `english`
```
```leanOutput english5
Unknown identifier `english`
```
```lean
namespace A.B
namespace C
end B.C
```
```lean
section
namespace D.E
```
```lean +error (name := endADE) -keep
end A.D.E
```
```leanOutput endADE
Invalid name after `end`: Expected `D.E`, but found `A.D.E`
```
```leanOutput endADE
Invalid name after `end`: Expected `D.E`, but found `A.D.E`
```
```lean
end D.E
end
end A
```
```lean
def Dessert.cupcake := "delicious"

open Dessert in
#eval cupcake
```
```lean +error (name := noCake)
#eval cupcake
```
```leanOutput noCake
Unknown identifier `cupcake`
```
```leanOutput noCake
Unknown identifier `cupcake`
```
```lean
section
set_option autoImplicit false
universe u
variable {α : Type u} (xs : List α) [Zero α] [Add α]
```
```lean +error (name := secvars) -keep
def addAll (lst : List β) : β :=
  lst.foldr (init := 0) (· + ·)
```
```leanOutput secvars
Unknown identifier `β`
```
```leanOutput secvars
Unknown identifier `β`
```
```lean
def addAll :=
  xs.foldr (init := 0) (· + ·)
```
```lean -show
section
variable {p : Nat → Prop}
variable (pFifteen : p 15)
```
```lean
section
variable {p : Nat → Prop}
variable (pZero : p 0) (pStep : ∀ n, p n → p (n + 1))
variable (pFifteen : p 15)
```
```lean +error -keep
theorem p_all : ∀ n, p n := by
  intro n
  induction n
```
```lean -keep (name := lint)
include pZero pStep pFifteen

theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
```leanOutput lint
automatically included section variable(s) unused in theorem `p_all`:
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```
```leanOutput lint
automatically included section variable(s) unused in theorem `p_all`:
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```
```lean -keep
include pZero pStep pFifteen

omit pFifteen in
theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
```lean
end
```
```lean -show
end
```