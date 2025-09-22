```lean
def two : (b : Bool) → if b then Unit × Unit else String :=
  fun b =>
    match b with
    | true => ((), ())
    | false => "two"
```
```lean
example : ((x : Nat) → String) = (Nat → String) := rfl
```
```lean
example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) := rfl
```
```lean
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0
```
```lean +error (name := nondepOops)
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (i < xs.size) → xs[i] ≠ 0
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
```lean
example :
    ({α : Type} → (x : α) → α)
    =
    ((α : Type) → (x : α) → α)
  := rfl
```
```lean -show
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- test claims in next para
example : (fun x => f x) = f := by rfl
```
```lean
def thirdChar (xs : Array Char) : Char := xs[2]!
```
```lean
example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl
```
```lean
example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl
``````lean
inductive Vacant : Type where
```
```lean
inductive No : Prop where
```
```lean -show -keep
theorem no_is_false : No = False := by
  apply propext
  constructor <;> intro h <;> cases h
```
```lean
inductive Solo where
  | solo
```
```lean (name := OneTy)
#check Solo
```
```leanOutput OneTy
Solo : Type
```
```leanOutput OneTy
Solo : Type
```
```lean (name := oneTy)
#check Solo.solo
```
```leanOutput oneTy
Solo.solo : Solo
```
```leanOutput oneTy
Solo.solo : Solo
```
```lean
inductive Yes : Prop where
  | intro
```
```lean (name := YesTy)
#check Yes
```
```leanOutput YesTy
Yes : Prop
```
```leanOutput YesTy
Yes : Prop
```
```lean (name := yesTy)
#check Yes.intro
```
```leanOutput yesTy
Yes.intro : Yes
```
```leanOutput yesTy
Yes.intro : Yes
```
```lean -show -keep
theorem yes_is_true : Yes = True := by
  apply propext
  constructor <;> intros <;> constructor
```
```lean -show
universe u
axiom α : Type u
axiom b : Bool
```
```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```
```lean
example : EvenOddList String true :=
  .cons "a" (.cons "b" .nil)
```
```lean +error (name := evenOddOops)
example : EvenOddList String true :=
  .cons "a" (.cons "b" (.cons "c" .nil))
```
```leanOutput evenOddOops
Type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true
but is expected to have type
  EvenOddList String true
```
```leanOutput evenOddOops
Type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true
but is expected to have type
  EvenOddList String true
```
```lean -show
universe u
axiom α : Type u
axiom b : Bool
```
```lean -show -keep
def EvenOddList.length : EvenOddList α b → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

theorem EvenOddList.length_matches_evenness (xs : EvenOddList α b) : b = (xs.length % 2 = 0) := by
  induction xs
  . simp [length]
  next b' _ xs ih =>
    simp [length]
    cases b' <;> simp only [Bool.true_eq_false, false_iff, true_iff] <;> simp at ih <;> omega
```
```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : β → Either α β
```
```lean (name := Either') +error
inductive Either' (α : Type u) (β : Type v) : Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either' α β
  | right : β → Either' α β
```
```leanOutput Either'
Mismatched inductive type parameter in
  Either' α β
The provided argument
  α
is not definitionally equal to the expected parameter
  α✝

Note: The value of parameter `α✝` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
```leanOutput Either'
Mismatched inductive type parameter in
  Either' α β
The provided argument
  α
is not definitionally equal to the expected parameter
  α✝

Note: The value of parameter `α✝` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
```lean (name := Either'')
inductive Either'' : Type u → Type v → Type (max u v + 1) where
  | left : {α : Type u} → {β : Type v} → α → Either'' α β
  | right : β → Either'' α β
```
```lean -show
axiom α : Type
```
```lean
inductive AtLeastOne (α : Type u) : Type u where
  | mk : α → Option (AtLeastOne α) → AtLeastOne α
```
```lean
def oneTwoThree : AtLeastOne Nat :=
  ⟨1, some ⟨2, some ⟨3, none⟩⟩⟩
```
```lean
def AtLeastOne.head : AtLeastOne α → α
  | ⟨x, _⟩ => x
```
```lean
def oneTwoThree' : AtLeastOne Nat :=
  .mk 1 (some (.mk 2 (some (.mk 3 none))))

def AtLeastOne.head' : AtLeastOne α → α
  | .mk x _ => x
```
```lean -show
axiom α : Prop
```
```lean
structure S where
  ptr_1 : Array Nat
  usize_1 : USize
  sc64_1 : UInt64
  -- wrappers don't count as scalars:
  ptr_2 : { x : UInt64 // x > 0 }
  sc64_2 : Float -- `Float` is 64 bit
  sc8_1 : Bool
  sc16_1 : UInt16
  sc8_2 : UInt8
  sc64_3 : UInt64
  usize_2 : USize
  -- trivial wrapper around `UInt32`
  ptr_3 : Char
  sc32_1 : UInt32
  sc16_2 : UInt16
```
```lean
mutual
  inductive EvenList (α : Type u) : Type u where
    | nil : EvenList α
    | cons : α → OddList α → EvenList α
  inductive OddList (α : Type u) : Type u where
    | cons : α → EvenList α → OddList α
end

example : EvenList String := .cons "x" (.cons "y" .nil)
example : OddList String := .cons "x" (.cons "y" (.cons "z" .nil))
```
```lean +error (name := evenOddMut)
example : OddList String := .cons "x" (.cons "y" .nil)
```
```leanOutput evenOddMut
Unknown constant `OddList.nil`

Note: Inferred this name from the expected resulting type of `.nil`:
  OddList String
```
```leanOutput evenOddMut
Unknown constant `OddList.nil`

Note: Inferred this name from the expected resulting type of `.nil`:
  OddList String
```
```lean +error (name := mutualNoMention)
mutual
  inductive FreshList (α : Type) (r : α → α → Prop) : Type where
    | nil : FreshList α r
    | cons (x : α) (xs : FreshList α r) (fresh : Fresh r x xs)
  inductive Fresh
      (r : α → FreshList α → Prop) :
      α → FreshList α r → Prop where
    | nil : Fresh r x .nil
    | cons : r x y → (f : Fresh r x ys) → Fresh r x (.cons y ys f)
end
```
```leanOutput mutualNoMention
Unknown identifier `FreshList`
```
```leanOutput mutualNoMention
Unknown identifier `FreshList`
```
```lean (name := bothOptional) +error
mutual
  inductive Both (α : Type u) (β : Type v) where
    | mk : α → β → Both α β
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput bothOptional
Invalid mutually inductive types: `Optional` has 1 parameter(s), but the preceding type `Both` has 2

Note: All inductive types declared in the same `mutual` block must have the same parameters
```
```leanOutput bothOptional
Invalid mutually inductive types: `Optional` has 1 parameter(s), but the preceding type `Both` has 2

Note: All inductive types declared in the same `mutual` block must have the same parameters
```
```lean (name := manyOptional) +error
mutual
  inductive Many (α : Type) : Type u where
    | nil : Many α
    | cons : α → Many α → Many α
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput manyOptional
Invalid mutually inductive types: Parameter `α` has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  Type
of sort `Type 1`
```
```leanOutput manyOptional
Invalid mutually inductive types: Parameter `α` has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  Type
of sort `Type 1`
```
```lean
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) :
    n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Type where
  | zero
    (noMore : ¬∃zs, xs = x :: zs := by simp) :
    PrefixRunOf 0 x xs xs
  | succ :
    PrefixRunOf n x xs ys →
    PrefixRunOf (n + 1) x (x :: xs) ys
end

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] :=
  .run 1 2 (by decide) (.succ (.succ .zero)) <|
  .run 2 2 (by decide) (.succ (.succ .zero)) <|
  .run 3 1 (by decide) (.succ .zero) <|
  .run 1 3 (by decide) (.succ (.succ (.succ (.zero)))) <|
  .nil
```
```lean +error (name := rleBad)
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run
    (x : α) (n : Nat) :
    n ≠ 0 → PrefixRunOf n x xs ys → RLE ys →
    RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Prop where
  | zero
    (noMore : ¬∃zs, xs = x :: zs := by simp) :
    PrefixRunOf 0 x xs xs
  | succ :
    PrefixRunOf n x xs ys →
    PrefixRunOf (n + 1) x (x :: xs) ys
end
```
```leanOutput rleBad
Invalid mutually inductive types: The resulting type of this declaration
  Prop
differs from a preceding one
  Type

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
```
```leanOutput rleBad
Invalid mutually inductive types: The resulting type of this declaration
  Prop
differs from a preceding one
  Type

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
```
```lean
def RunLengths α := List (α × Nat)
def NoRepeats : RunLengths α → Prop
  | [] => True
  | [_] => True
  | (x, _) :: ((y, n) :: xs) =>
    x ≠ y ∧ NoRepeats ((y, n) :: xs)
def RunsMatch : RunLengths α → List α → Prop
  | [], [] => True
  | (x, n) :: xs, ys =>
    ys.take n = List.replicate n x ∧
    RunsMatch xs (ys.drop n)
  | _, _ => False
def NonZero : RunLengths α → Prop
  | [] => True
  | (_, n) :: xs => n ≠ 0 ∧ NonZero xs
structure RLE (xs : List α) where
  rle : RunLengths α
  noRepeats : NoRepeats rle
  runsMatch : RunsMatch rle xs
  nonZero : NonZero rle

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] where
  rle := [(1, 2), (2, 2), (3, 1), (1, 3)]
  noRepeats := by simp [NoRepeats]
  runsMatch := by simp [RunsMatch]
  nonZero := by simp [NonZero]
```
```lean +error (name := mutualHoas)
mutual
  inductive Tm where
    | app : Tm → Tm → Tm
    | lam : Binding → Tm
  inductive Binding where
    | scope : (Tm → Tm) → Binding
end
```
```leanOutput mutualHoas
(kernel) arg #1 of 'Binding.scope' has a non positive occurrence of the datatypes being declared
```
```leanOutput mutualHoas
(kernel) arg #1 of 'Binding.scope' has a non positive occurrence of the datatypes being declared
```
```lean
mutual
  inductive LocatedStx where
    | mk (line col : Nat) (val : Stx)
  inductive Stx where
    | atom (str : String)
    | node (kind : String) (args : List LocatedStx)
end
```
```lean
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end
```
```lean
mutual
  inductive Two (α : Type) where
    | mk : α → α → Two α
  inductive Three (α : Type) where
    | mk : α → α → α → Three α
end
``````lean
def color := "yellow"
namespace Forest
def color := "green"
def statement := s!"Lemons are {color}"
end Forest
```
```lean (name := green)
#eval Forest.statement
```
```leanOutput green
"Lemons are green"
```
```leanOutput green
"Lemons are green"
```
```lean
namespace Forest
def nextStatement :=
  s!"Ripe lemons are {_root_.color}, not {color}"
end Forest
```
```lean (name := ygreen)
#eval Forest.nextStatement
```
```leanOutput ygreen
"Ripe lemons are yellow, not green"
```
```leanOutput ygreen
"Ripe lemons are yellow, not green"
```
```lean
inductive HotDrink where
  | coffee
  | tea
  | cocoa
```
```lean (name := okTea)
#check HotDrink.tea
```
```leanOutput okTea
HotDrink.tea : HotDrink
```
```leanOutput okTea
HotDrink.tea : HotDrink
```
```lean (name := notOkTea) +error
#check tea
```
```leanOutput notOkTea
Unknown identifier `tea`
```
```leanOutput notOkTea
Unknown identifier `tea`
```
```lean (name := okTea2)
section
open HotDrink
#check tea
end
```
```leanOutput okTea2
HotDrink.tea : HotDrink
```
```leanOutput okTea2
HotDrink.tea : HotDrink
```
```lean
def HotDrink.ofString? : String → Option HotDrink
  | "coffee" => some coffee
  | "tea" => some tea
  | "cocoa" => some cocoa
  | _ => none
```
```lean
inductive ColdDrink where
  | water
  | juice
```
```lean
namespace HotDrink

def toString : HotDrink → String
  | coffee => "coffee"
  | tea => "tea"
  | cocoa => "cocoa"

def _root_.ColdDrink.toString : ColdDrink → String
  | .water => "water"
  | .juice => "juice"

end HotDrink
```
```lean
namespace A -- _root_.A
def a1 := 0
namespace B -- _root_.A.B
def a2 := 0
namespace C -- _root_.A.B.C
def a3 := 0
end C
end B
end A
namespace B -- _root_.B
def a4 := 0
namespace C -- _root_.B.C
def a5 := 0
end C
end B
namespace C -- _root_.C
def a6 := 0
end C
```
```lean
section
open A B C
example := [a1, a2, a3, a4, a5, a6]
end
```
```lean +error (name := dotted)
section
open A.B C
example := [a1, a2, a3, a4, a5, a6]
end
```
```leanOutput dotted
Unknown identifier `a1`
```
```leanOutput dotted
Unknown identifier `a1`
```
```leanOutput dotted
Unknown identifier `a4`
```
```leanOutput dotted
Unknown identifier `a4`
```
```leanOutput dotted
Unknown identifier `a5`
```
```leanOutput dotted
Unknown identifier `a5`
```
```lean -show -keep
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B hiding x
```
```lean -show -keep
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B renaming x → y
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B renaming x -> y
```
```lean -show -keep
namespace A
namespace B
def y := ""
end B
end A
namespace B
end B
open A
-- test claim in preceding box
-- TODO the reality is a bit more subtle - the name should be accessible by only one path. This should be clarified.
/-- error: ambiguous identifier `y`, possible interpretations: [B.y, B.y] -/
#check_msgs in
open B (y)
```
```lean
namespace NS
scoped notation "{!{" e "}!}" => (e, e)
def three := 3
end NS
```
```leanOutput closed
<example>:1:21-1:22: unexpected token '!'; expected '}'
```
```leanOutput closed
<example>:1:21-1:22: unexpected token '!'; expected '}'
```
```lean
open scoped NS
def x := {!{ "pear" }!}
```
```lean +error (name := nothree)
def y := three
```
```leanOutput nothree
Unknown identifier `three`
```
```leanOutput nothree
Unknown identifier `three`
```
```lean
namespace Veg
inductive Leafy where
  | spinach
  | cabbage
export Leafy (spinach)
end Veg
export Veg.Leafy (cabbage)
``````lean -show
axiom α.{u} : Type u
```
```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```
```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Either α β
  | inr : β → Either α β
```
```lean
inductive CanRepr : Type (u + 1) where
  | mk : (α : Type u) → [Repr α] → CanRepr
```
```lean
inductive Spurious (α : Type 5) : Type 0 where
```
```lean (name := Bad) +error
inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```
```lean -show
axiom Bad : Type
axiom Bad.bad : (Bad → Bad) → Bad
```
```lean (name := Fix) +error
inductive Fix (f : Type u → Type u) where
  | fix : f (Fix f) → Fix f
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```
```lean -show
axiom Fix : (Type → Type) → Type
```
```lean
def Bad : Type := Fix fun t => t → t
```
```lean +error (name := PBool)
inductive PBool : Sort u where
  | true
  | false
```
```leanOutput PBool
Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort u

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
```
```leanOutput PBool
Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort u

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
``````lean
inductive ONat : Type where
  | mk (pred : Option ONat)
```
```lean
inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : List (RTree α))
```
```lean +error (name := viaAlias)
abbrev Children := List

inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : Children (RTree α))
```
```leanOutput viaAlias
(kernel) arg #3 of 'RTree.node' contains a non valid occurrence of the datatypes being declared
```
```leanOutput viaAlias
(kernel) arg #3 of 'RTree.node' contains a non valid occurrence of the datatypes being declared
```
```lean -show
variable {n : Nat}
```
```lean +error (name := localVar)
inductive DRTree (α : Type u) : Nat → Type u where
  | empty : DRTree α 0
  | node (val : α) (children : List (DRTree α n)) : DRTree α (n + 1)
```
```lean +error (name := nonPos)
inductive WithCheck where
  | done
  | check (f : Option WithCheck → Bool)
```
```leanOutput nonPos
(kernel) arg #1 of 'WithCheck.check' has a non positive occurrence of the datatypes being declared
```
```leanOutput nonPos
(kernel) arg #1 of 'WithCheck.check' has a non positive occurrence of the datatypes being declared
```
```lean +error (name := brtree)
inductive BRTree (branches : Nat) (α : Type u) : Type u where
  | mk :
    (children : List (BRTree branches α)) →
    children.length < branches →
    BRTree branches α
```
```leanOutput brtree
(kernel) application type mismatch
  List.length children
argument has type
  @_nested.List_1 branches α
but function has type
  List (@BRTree branches α) → Nat
```
```leanOutput brtree
(kernel) application type mismatch
  List.length children
argument has type
  @_nested.List_1 branches α
but function has type
  List (@BRTree branches α) → Nat
```
```lean (name := nondep)
inductive RTree'' (α : Type u) : Type u where
  | mk :
    (children : List (BRTree branches α)) →
    id children = children →
    BRTree branches α
```
```lean
inductive Palindrome (α : Type) : List α → Prop where
  | nil : Palindrome α []
  | single : Palindrome α [x]
  | cons (x : α) (p : Palindrome α xs) : Palindrome α (x :: xs ++ [x])
```
```lean -keep
inductive ONat where
  | mk (pred : Option ONat) : ONat

#check ONat.rec
```
```lean
mutual
inductive ONat' where
  | mk (pred : OptONat) : ONat'

inductive OptONat where
  | none
  | some : ONat' → OptONat
end
```
```lean
def ONat := ONat'
```
```lean
def OptONat.ofOption : Option ONat → OptONat
  | Option.none => OptONat.none
  | Option.some o => OptONat.some o
def OptONat.toOption : OptONat → Option ONat
  | OptONat.none => Option.none
  | OptONat.some o => Option.some o
```
```lean
def OptONat.to_of_eq_id o :
    OptONat.toOption (ofOption o) = o := by
  cases o <;> rfl
def OptONat.of_to_eq_id o :
    OptONat.ofOption (OptONat.toOption o) = o := by
  cases o <;> rfl
```
```lean
def ONat.mk (pred : Option ONat) : ONat :=
  ONat'.mk (.ofOption pred)
```
```lean
noncomputable def ONat.rec
    {motive1 : ONat → Sort u}
    {motive2 : Option ONat → Sort u}
    (h1 :
      (pred : Option ONat) → motive2 pred →
      motive1 (ONat.mk pred))
    (h2 : motive2 none)
    (h3 : (o : ONat) → motive1 o → motive2 (some o)) :
    (t : ONat) → motive1 t :=
  @ONat'.rec motive1 (motive2 ∘ OptONat.toOption)
    (fun pred ih =>
      OptONat.of_to_eq_id pred ▸ h1 pred.toOption ih)
    h2
    h3
``````lean -show
-- Test claim about recursive above

/--
error: (kernel) arg #1 of 'RecStruct.mk' has a non positive occurrence of the datatypes being declared
-/
#check_msgs in
structure RecStruct where
  next : RecStruct → RecStruct

```
```lean
structure MyStructure where
  field1 : α
  field2 : α
```
```lean
structure ArraySized (α : Type u) (length : Nat)  where
  array : Array α
  size_eq_length : array.size = length
```
```lean
structure Graph where
  adjacency : Array (List Nat) := #[]

def Graph.empty : Graph := {}
```
```lean
structure Palindrome where
  ofString ::
  text : String
  is_palindrome : text.data.reverse = text.data
```
```lean
structure NatStringBimap where
  /--
  Build a finite bijection between some
  natural numbers and strings
  -/
  private mk ::
  natToString : Std.HashMap Nat String
  stringToNat : Std.HashMap String Nat

def NatStringBimap.empty : NatStringBimap := ⟨{}, {}⟩

def NatStringBimap.insert
    (nat : Nat) (string : String)
    (map : NatStringBimap) :
    Option NatStringBimap :=
  if map.natToString.contains nat ||
      map.stringToNat.contains string then
    none
  else
    some (NatStringBimap.mk (map.natToString.insert nat string) (map.stringToNat.insert string nat))
```
```lean
structure AugmentedIntList where
  list : List Int
  augmentation : String := ""
```
```lean (name := isEmptyDefaults)
def AugmentedIntList.isEmpty : AugmentedIntList → Bool
  | {list := []} => true
  | _ => false

#eval {list := [], augmentation := "extra" : AugmentedIntList}.isEmpty
```
```leanOutput isEmptyDefaults
false
```
```leanOutput isEmptyDefaults
false
```
```lean (name := arrayUpdate)
structure AugmentedIntArray where
  array : Array Int
  augmentation : String := ""
deriving Repr

def one : AugmentedIntArray := {array := #[1]}
def two : AugmentedIntArray := {one with array := #[1, 2]}
def two' : AugmentedIntArray := {two with array[0] := 2}
def two'' : AugmentedIntArray := {two with array[99] := 3}
#eval (one, two, two', two'')
```
```leanOutput arrayUpdate
({ array := #[1], augmentation := "" },
 { array := #[1, 2], augmentation := "" },
 { array := #[2, 2], augmentation := "" },
 { array := #[1, 2], augmentation := "" })
```
```leanOutput arrayUpdate
({ array := #[1], augmentation := "" },
 { array := #[1, 2], augmentation := "" },
 { array := #[2, 2], augmentation := "" },
 { array := #[1, 2], augmentation := "" })
```
```lean
def location : Float × Float where
  fst := 22.807
  snd := -13.923
```
```lean -show -keep
-- If the overlapping fields have different default values, then the default value from the first
-- parent structure in the resolution order that includes the field is used.
structure Q where
  x : Nat := 0
deriving Repr
structure Q' where
  x : Nat := 3
deriving Repr
structure Q'' extends Q, Q'
deriving Repr
structure Q''' extends Q', Q
deriving Repr

/--
info: structure Q'' : Type
number of parameters: 0
parents:
  Q''.toQ : Q
  Q''.toQ' : Q'
fields:
  Q.x : Nat :=
    0
constructor:
  Q''.mk (toQ : Q) : Q''
field notation resolution order:
  Q'', Q, Q'
-/
#check_msgs in
#print Q''

/-- info: 0 -/
#check_msgs in
#eval ({} : Q'').x

/--
info: structure Q''' : Type
number of parameters: 0
parents:
  Q'''.toQ' : Q'
  Q'''.toQ : Q
fields:
  Q'.x : Nat :=
    3
constructor:
  Q'''.mk (toQ' : Q') : Q'''
field notation resolution order:
  Q''', Q', Q
-/
#check_msgs in
#print Q'''

/-- info: 3 -/
#check_msgs in
#eval ({} : Q''').x

-- Defaults use local values
structure A where
  n : Nat := 0
deriving Repr
structure B extends A where
  k : Nat := n
deriving Repr
structure C extends A where
  n := 5
deriving Repr
structure C' extends A where
  n := 3
deriving Repr

structure D extends B, C, C'
deriving Repr
structure D' extends B, C', C
deriving Repr

#eval ({} : D).k

#eval ({} : D').k

```
```lean
structure Book where
  title : String
  author : String

structure AcademicWork where
  author : String
  discipline : String

structure Textbook extends Book, AcademicWork

#check Textbook.toBook
```
```lean
def toAcademicWork (self : Textbook) : AcademicWork :=
  let .mk book discipline := self
  let .mk _title author := book
  .mk author discipline
```
```lean -show
-- check claim of equivalence
example : toAcademicWork = Textbook.toAcademicWork := by
  funext b
  cases b
  dsimp [toAcademicWork]
```
```lean
structure Pair (α : Type u) where
  fst : α
  snd : α
deriving Repr

structure Triple (α : Type u) extends Pair α where
  thd : α
deriving Repr

def coords : Triple Nat := {fst := 17, snd := 2, thd := 95}
```
```lean (name := coords1)
#eval coords.1
```
```leanOutput coords1
{ fst := 17, snd := 2 }
```
```leanOutput coords1
{ fst := 17, snd := 2 }
```
```lean -show -keep
example (t : Triple α) : t.fst = t.toPair.fst := rfl
```
```lean
structure EvenNumber where
  val : Nat
  isEven : 2 ∣ val := by decide

structure EvenPrime extends EvenNumber where
  notOne : val ≠ 1 := by decide
  isPrime : ∀ n, n ≤ val → n ∣ val  → n = 1 ∨ n = val

def two : EvenPrime where
  val := 2
  isPrime := by
    intros
    repeat' (cases ‹Nat.le _ _›)
    all_goals omega

def printEven (num : EvenNumber) : IO Unit :=
  IO.print num.val
```
```lean +error (name := printTwo)
#check printEven two
```
```leanOutput printTwo
Application type mismatch: The argument
  two
has type
  EvenPrime
but is expected to have type
  EvenNumber
in the application
  printEven two
```
```leanOutput printTwo
Application type mismatch: The argument
  two
has type
  EvenPrime
but is expected to have type
  EvenNumber
in the application
  printEven two
```
```lean -show -keep
structure A where
  x : Nat
  y : Int
structure A' where
  x : Int
structure B where
  foo : Nat
structure C extends A where
  z : String
/-- info: C.mk (toA : A) (z : String) : C -/
#check_msgs in
#check C.mk

def someC : C where
  x := 1
  y := 2
  z := ""

/--
error: Type mismatch
  someC
has type
  C
but is expected to have type
  A
-/
#check_msgs in
#check (someC : A)

structure D extends A, B where
  z : String
/-- info: D.mk (toA : A) (toB : B) (z : String) : D -/
#check_msgs in
#check D.mk
structure E extends A, B where
  x := 44
  z : String
/-- info: E.mk (toA : A) (toB : B) (z : String) : E -/
#check_msgs in
#check E.mk
/--
error: Field type mismatch: Field `x` from parent `A'` has type
  Int
but is expected to have type
  Nat
-/
#check_msgs in
structure F extends A, A' where

```
```lean
structure Vehicle where
  wheels : Nat

structure Bicycle extends Vehicle where
  wheels := 2

structure ElectricVehicle extends Vehicle where
  batteries : Nat := 1

structure FamilyBike extends Bicycle where
  wheels := 3

structure ElectricBike extends Bicycle, ElectricVehicle

structure ElectricFamilyBike
    extends FamilyBike, ElectricBike where
  batteries := 2
```
```lean (name := el)
#print ElectricBike
```
```leanOutput el
structure ElectricBike : Type
number of parameters: 0
parents:
  ElectricBike.toBicycle : Bicycle
  ElectricBike.toElectricVehicle : ElectricVehicle
fields:
  Vehicle.wheels : Nat :=
    2
  ElectricVehicle.batteries : Nat :=
    1
constructor:
  ElectricBike.mk (toBicycle : Bicycle) (batteries : Nat) : ElectricBike
field notation resolution order:
  ElectricBike, Bicycle, ElectricVehicle, Vehicle
```
```leanOutput el
structure ElectricBike : Type
number of parameters: 0
parents:
  ElectricBike.toBicycle : Bicycle
  ElectricBike.toElectricVehicle : ElectricVehicle
fields:
  Vehicle.wheels : Nat :=
    2
  ElectricVehicle.batteries : Nat :=
    1
constructor:
  ElectricBike.mk (toBicycle : Bicycle) (batteries : Nat) : ElectricBike
field notation resolution order:
  ElectricBike, Bicycle, ElectricVehicle, Vehicle
```
```lean  (name := elFam)
#print ElectricFamilyBike
```
```leanOutput elFam
structure ElectricFamilyBike : Type
number of parameters: 0
parents:
  ElectricFamilyBike.toFamilyBike : FamilyBike
  ElectricFamilyBike.toElectricBike : ElectricBike
fields:
  Vehicle.wheels : Nat :=
    3
  ElectricVehicle.batteries : Nat :=
    2
constructor:
  ElectricFamilyBike.mk (toFamilyBike : FamilyBike) (batteries : Nat) : ElectricFamilyBike
field notation resolution order:
  ElectricFamilyBike, FamilyBike, ElectricBike, Bicycle, ElectricVehicle, Vehicle
```
```leanOutput elFam
structure ElectricFamilyBike : Type
number of parameters: 0
parents:
  ElectricFamilyBike.toFamilyBike : FamilyBike
  ElectricFamilyBike.toElectricBike : ElectricBike
fields:
  Vehicle.wheels : Nat :=
    3
  ElectricVehicle.batteries : Nat :=
    2
constructor:
  ElectricFamilyBike.mk (toFamilyBike : FamilyBike) (batteries : Nat) : ElectricFamilyBike
field notation resolution order:
  ElectricFamilyBike, FamilyBike, ElectricBike, Bicycle, ElectricVehicle, Vehicle
```